import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BoundedCoupling

namespace OAI

namespace AnchoredBoundedData

open Set MeasureTheory ExtremalEdges BoundedData

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma compact_body (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p) (b : V → ℝ) :
    IsCompact (conditionalBody G pins b) := by
  classical
  choose p hp path using ha
  let walk (x : V) : G.Walk x (p x) := Classical.choice (path x)
  let R (x : Free pins) : ℝ := |b (p x)|+(walk x).length
  apply isCompact_Icc.of_isClosed_subset (closed_conditionalBody G pins b) (s := Icc (-R) R)
  intro h hh
  have hb (x : Free pins) : |h x|≤R x := by
    have hbnd := bound_along_walk G (restore pins b h) hh (walk x)
    have hx : restore pins b h x=h x := by simp [restore,x.property]
    have hp' : restore pins b h (p x)=b (p x) := by simp [restore,hp]
    rw [hx,hp'] at hbnd
    have ht : |h x|≤|h x-b (p x)|+|b (p x)| := by simpa only [sub_add_cancel] using abs_add_le (h x-b (p x)) (b (p x))
    dsimp [R]
    linarith
  exact ⟨fun x => (abs_le.mp (hb x)).1,fun x => (abs_le.mp (hb x)).2⟩

lemma neighbor_nonempty (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p) (x : Free pins) :
    (G.neighborFinset x).Nonempty := by
  classical
  obtain ⟨p,hp,⟨w⟩⟩ := ha x
  have hxp : (x:V)≠p := fun h => x.property (h ▸ hp)
  cases w with
  | nil => exact (hxp rfl).elim
  | cons hxy w => exact ⟨_,by simpa using hxy⟩

noncomputable def bodyMeasure (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) : ProbabilityMeasure (conditionalBody G pins b) :=
  ⟨(volume (conditionalBody G pins b))⁻¹ • Measure.comap Subtype.val volume,by
    constructor
    rw [Measure.smul_apply,(MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins b).measurableSet).comap_apply,
      image_univ,Subtype.range_coe]
    exact ENNReal.inv_mul_cancel hpos.ne' (compact_body G pins ha b).measure_ne_top⟩

lemma bodyMeasure_map (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) :
    Measure.map Subtype.val (bodyMeasure G pins ha b hpos : Measure (conditionalBody G pins b))=law G pins b := by
  change Measure.map Subtype.val (_ • Measure.comap Subtype.val volume)=_
  rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    map_comap_subtype_coe (closed_conditionalBody G pins b).measurableSet]
  rfl

lemma bodyUpdate_preserves (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p)
    (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) (x : Free pins) :
    Measure.map (bodyUpdate G pins hn b x)
      ((bodyMeasure G pins ha b hpos : Measure (conditionalBody G pins b)).prod UnitControl.law)=
    (bodyMeasure G pins ha b hpos : Measure (conditionalBody G pins b)) := by
  apply (MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins b).measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe (continuous_bodyUpdate G pins hn b x).measurable,bodyMeasure_map]
  change Measure.map ((fun z : (Free pins → ℝ)×ℝ => update G pins hn b x z.1 z.2) ∘ Prod.map Subtype.val Subtype.val) _=_
  rw [← Measure.map_map (continuous_update G pins hn b x).measurable (measurable_subtype_coe.prodMap measurable_subtype_coe),
    ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,bodyMeasure_map,UnitControl.map_val]
  exact update_preserves_law G pins hn b x

end AnchoredBoundedData

namespace AnchoredBoundedData

open Set MeasureTheory ExtremalEdges BoundedData

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma continuous_restore_function (pins : Set V) (b : V → ℝ) : Continuous (restore pins b) := by
  exact continuous_pi (fun x => continuous_restore pins b x)

theorem one_sample_bounded_data_anchored
    (G : SimpleGraph V) (pins : Set V)
    (ha : ∀ x : V, ∃ p∈pins, G.Reachable x p)
    (b : V → ℝ) (B : ℝ) (hB : 0≤B) (hb : ∀ x∈pins,|b x|≤B)
    (hpos : 0<volume (conditionalBody G pins b)) :
    ∃ π : Measure ((Free pins → ℝ) × (Free pins → ℝ)),
      IsProbabilityMeasure π ∧ Measure.map Prod.fst π=law G pins b ∧
      Measure.map Prod.snd π=law G pins (fun _ => 0) ∧
      ∀ᵐ z∂π,∀ x : V,|restore pins b z.1 x-restore pins (fun _ => 0) z.2 x|≤B := by
  classical
  let X := conditionalBody G pins b
  let Y := conditionalBody G pins (fun _ => 0)
  let : CompactSpace X := (isCompact_iff_compactSpace.mp (compact_body G pins ha b))
  let : CompactSpace Y := (isCompact_iff_compactSpace.mp (compact_body G pins ha (fun _ => 0)))
  let : CompactSpace (Icc (0:ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  let hn := neighbor_nonempty G pins ha
  let μ : ProbabilityMeasure X := bodyMeasure G pins ha b hpos
  let ν : ProbabilityMeasure Y := bodyMeasure G pins ha (fun _ => 0) (volume_zeroBody_pos G pins)
  let d : X×Y → ℝ := fun z => max 0 (‖restore pins b z.1.val-restore pins (fun _ => 0) z.2.val‖-B)
  let H : X×Y → ℝ := fun z => (∑ y,z.1.val y)+(∑ y,z.2.val y)
  let T := bodyUpdate G pins hn b
  let S := bodyUpdate G pins hn (fun _ => 0)
  have hd : Continuous d := by
    exact continuous_const.max ((((continuous_restore_function pins b).comp (continuous_subtype_val.comp continuous_fst)).sub
      ((continuous_restore_function pins (fun _ => 0)).comp (continuous_subtype_val.comp continuous_snd))).norm.sub continuous_const)
  have hH : Continuous H := by
    exact (continuous_finsetSum _ (fun y _ => (continuous_apply y).comp (continuous_subtype_val.comp continuous_fst))).add
      (continuous_finsetSum _ (fun y _ => (continuous_apply y).comp (continuous_subtype_val.comp continuous_snd)))
  have hdec (x : Free pins) (z : X×Y) (u : Icc (0:ℝ) 1) : d (T x (z.1,u),S x (z.2,u))≤d z := by
    apply max_le_max le_rfl
    exact sub_le_sub_right (update_norm_difference G pins hn b (fun _ => 0) z.1.val z.2.val x u.property) B
  let u₀ : Icc (0:ℝ) 1 := ⟨0,by norm_num⟩
  have hdown (x : Free pins) (z : X×Y) : H (T x (z.1,u₀),S x (z.2,u₀))≤H z := by
    change (∑ y,update G pins hn b x z.1.val 0 y)+(∑ y,update G pins hn (fun _ => 0) x z.2.val 0 y)≤_
    rw [update_sum,update_sum]
    dsimp [H]
    linarith [lower_le G pins hn b z.1.val z.1.property x,lower_le G pins hn (fun _ => 0) z.2.val z.2.property x]
  have hfixed (z : X×Y) (he : ∀ x,H (T x (z.1,u₀),S x (z.2,u₀))=H z) : d z=0 := by
    have he' (x : Free pins) : lower G pins hn b z.1.val x=z.1.val x ∧ lower G pins hn (fun _ => 0) z.2.val x=z.2.val x := by
      have hx := he x
      change (∑ y,update G pins hn b x z.1.val 0 y)+(∑ y,update G pins hn (fun _ => 0) x z.2.val 0 y)=_ at hx
      rw [update_sum,update_sum] at hx
      dsimp [H] at hx
      have hl := lower_le G pins hn b z.1.val z.1.property x
      have hr := lower_le G pins hn (fun _ => 0) z.2.val z.2.property x
      constructor <;> linarith
    have hbound := lower_fixed_comparison G pins hn b B hb z.1.val z.2.val z.1.property z.2.property
      (fun x => (he' x).1) (fun x => (he' x).2)
    have hnorm : ‖restore pins b z.1.val-restore pins (fun _ => 0) z.2.val‖≤B := by
      apply (pi_norm_le_iff_of_nonneg hB).mpr
      intro x
      exact hbound x
    exact max_eq_left (sub_nonpos.mpr hnorm)
  obtain ⟨π,hπ,hzero⟩ := CompactCoupling.exists_zero μ ν UnitControl.law UnitControl.support_full u₀ T S
    (continuous_bodyUpdate G pins hn b) (continuous_bodyUpdate G pins hn (fun _ => 0))
    (bodyUpdate_preserves G pins ha hn b hpos)
    (bodyUpdate_preserves G pins ha hn (fun _ => 0) (volume_zeroBody_pos G pins)) d H hd hH hdec hdown hfixed
  let F : X×Y → (Free pins → ℝ)×(Free pins → ℝ) := Prod.map Subtype.val Subtype.val
  have hF : MeasurableEmbedding F := (MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins b).measurableSet).prodMap
    (MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins (fun _ => 0)).measurableSet)
  refine ⟨Measure.map F (π:Measure (X×Y)),inferInstance,?_,?_,?_⟩
  · rw [Measure.map_map measurable_fst hF.measurable]
    change Measure.map (Subtype.val ∘ Prod.fst) (π:Measure (X×Y))=law G pins b
    rw [← Measure.map_map measurable_subtype_coe measurable_fst]
    have hp' : Measure.map Prod.fst (π:Measure (X×Y))=(μ:Measure X) := congrArg Subtype.val hπ.1
    rw [hp']
    exact bodyMeasure_map G pins ha b hpos
  · rw [Measure.map_map measurable_snd hF.measurable]
    change Measure.map (Subtype.val ∘ Prod.snd) (π:Measure (X×Y))=law G pins (fun _ => 0)
    rw [← Measure.map_map measurable_subtype_coe measurable_snd]
    have hp' : Measure.map Prod.snd (π:Measure (X×Y))=(ν:Measure Y) := congrArg Subtype.val hπ.2
    rw [hp']
    exact bodyMeasure_map G pins ha (fun _ => 0) (volume_zeroBody_pos G pins)
  · apply hF.ae_map_iff.mpr
    filter_upwards [hzero] with z hz
    intro x
    have hnorm : ‖restore pins b z.1.val-restore pins (fun _ => 0) z.2.val‖≤B := by
      have hh := le_max_right 0 (‖restore pins b z.1.val-restore pins (fun _ => 0) z.2.val‖-B)
      change max 0 (‖restore pins b z.1.val-restore pins (fun _ => 0) z.2.val‖-B)=0 at hz
      rw [hz] at hh
      linarith
    exact (norm_le_pi_norm (restore pins b z.1.val-restore pins (fun _ => 0) z.2.val) x).trans hnorm

end AnchoredBoundedData

end OAI
