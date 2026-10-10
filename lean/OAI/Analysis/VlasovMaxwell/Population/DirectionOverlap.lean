import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.MomentumDirection
import OAI.Analysis.VlasovMaxwell.Geometry.UpperTimeCut

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma physicalPhaseForce_cutoff {s : Solution} {τ H t : ℝ} (hτH : τ < H)
    (x a : Vec) (p : Phase) (hp : t-coneRadius x p.1 ≤ τ) :
    physicalPhaseForce (cutoffPrefix τ H s) t x a p=physicalPhaseForce s t x a p := by
  simp only [physicalPhaseForce,cutoffPrefix,upperTimeExtend,upperTimeCut_one hτH hp,one_smul]

lemma SmoothClassicalPrefix.retarded_force_phase_domain {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (ht : 0 < t) (htH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ p in retardedPhaseDomain t x,
        s.f (t-‖x-p.1‖,p) • physicalPhaseForce s t x a p := by
  let τ := (t+H)/2
  have htτ : t < τ := by dsimp [τ]; linarith
  have hτH : τ < H := by dsimp [τ]; linarith
  have hτ0 : 0 ≤ τ := ht.le.trans htτ.le
  have he := classical_retarded_force_phase_domain_before (hs.cutoff_classical_before hτ0 hτH)
    (hs.cutoff_smooth hτH) ht htτ x a
  rw [(cutoffPrefix_eq hτH htτ.le s).2.1 x,(cutoffPrefix_eq hτH htτ.le s).2.2 x] at he
  refine he.trans ?_
  congr 2
  apply setIntegral_congr_fun (isOpen_retardedPhaseDomain t x).measurableSet
  intro p hp
  have htime : t-coneRadius x p.1 ≤ τ := (sub_le_self t (norm_nonneg _)).trans htτ.le
  change (cutoffPrefix τ H s).f (t-‖x-p.1‖,p) • physicalPhaseForce (cutoffPrefix τ H s) t x a p = _
  rw [physicalPhaseForce_cutoff hτH x a p htime]
  change (cutoffPrefix τ H s).f (t-coneRadius x p.1,p) • _ = s.f (t-coneRadius x p.1,p) • _
  rw [(cutoffPrefix_eq hτH htime s).1 p]

lemma SmoothClassicalPrefix.retarded_force_label_integral {d : Datum} {s : Solution} {H t : ℝ}
    (hs : SmoothClassicalPrefix d s H) (F : PhaseFlowOn s.E s.B H)
    (ht : 0 < t) (htH : t < H) (x a : Vec) :
    s.E (t,x)+cross a (s.B (t,x))=boundaryLorentzForce (datumBoundarySolution d) t x a+
      (4*Real.pi)⁻¹ • ∫ z in initialConeLabels t x,
        (1-dot (coneDirection x (F.retardedSource ⟨ht.le,htH.le⟩ x z).1)
          (velocity (F.retardedSource ⟨ht.le,htH.le⟩ x z).2))⁻¹ •
          (d.f₀ z • physicalPhaseForce s t x a (F.retardedSource ⟨ht.le,htH.le⟩ x z)) := by
  rw [hs.retarded_force_phase_domain ht htH x a]
  congr 2
  rw [F.retarded_transport_integral hs.energyPrefix.f_smooth hs.energyPrefix.vlasov
    ⟨ht.le,htH.le⟩ x]
  apply setIntegral_congr_fun (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
  intro z hz
  change _ • (s.f (0,z) • _) = _ • (d.f₀ z • _)
  rw [hs.initial_f]
  rfl

lemma SmoothClassicalPrefix.exists_phaseFlowOn {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hH : 0 < H) : Nonempty (PhaseFlowOn s.E s.B H) :=
  RVM.exists_phaseFlowOn hH
    ((hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1))
    ((hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1))
end RVM

open Set MeasureTheory
open scoped ENNReal

namespace RVM

def DirectionOverlap {ι κ : Type*} (l r : ι → ℝ) (l' r' : κ → ℝ) :=
  {ij : ι × κ // max (l ij.1) (l' ij.2) < min (r ij.1) (r' ij.2)}

noncomputable instance {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ) : Fintype (DirectionOverlap l r l' r') := by
  unfold DirectionOverlap
  exact Fintype.ofFinite _

lemma directionOverlap_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j))) :
    Fintype.card (DirectionOverlap l r l' r') ≤ Fintype.card ι + Fintype.card κ := by
  classical
  let charge : DirectionOverlap l r l' r' → ι ⊕ κ := fun z =>
    if l z.1.1 ≤ l' z.1.2 then Sum.inr z.1.2 else Sum.inl z.1.1
  have hc : Function.Injective charge := by
    intro a b hab
    have ha := a.2
    have hb := b.2
    dsimp [charge] at hab
    split_ifs at hab with h₁ h₂ h₂
    · have hj : a.1.2 = b.1.2 := Sum.inr.inj hab
      have hi : a.1.1 = b.1.1 := by
        by_contra hn
        have hd := Set.disjoint_left.mp (hleft _ _ hn)
        apply hd (a := l' a.1.2)
        · exact ⟨h₁, (le_max_right _ _).trans_lt (lt_of_lt_of_le ha (min_le_left _ _))⟩
        · rw [hj]
          exact ⟨h₂, (le_max_right _ _).trans_lt (lt_of_lt_of_le hb (min_le_left _ _))⟩
      exact Subtype.ext (Prod.ext hi hj)
    · have hi : a.1.1 = b.1.1 := Sum.inl.inj hab
      have hj : a.1.2 = b.1.2 := by
        by_contra hn
        have hd := Set.disjoint_left.mp (hright _ _ hn)
        apply hd (a := l a.1.1)
        · exact ⟨(lt_of_not_ge h₁).le,
            (le_max_left _ _).trans_lt (lt_of_lt_of_le ha (min_le_right _ _))⟩
        · rw [hi]
          exact ⟨(lt_of_not_ge h₂).le,
            (le_max_left _ _).trans_lt (lt_of_lt_of_le hb (min_le_right _ _))⟩
      exact Subtype.ext (Prod.ext hi hj)
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective charge hc

lemma refined_direction_hit_duration {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    {X Y a u : ℝ → Vec} {D H : Set ℝ} {c R : ℝ}
    (v : DirectionOverlap l r l' r' → Vec)
    (hc : 0 < c)
    (hD : ∀ i, Ico (l i) (r i) ⊆ D)
    (hcover : ∀ t ∈ H, (∃ i, t ∈ Ico (l i) (r i)) ∧
      (∃ j, t ∈ Ico (l' j) (r' j)))
    (hXc : ContinuousOn X D) (hYc : ContinuousOn Y D)
    (hX : ∀ t ∈ interior D, HasDerivAt X (a t) t)
    (hY : ∀ t ∈ interior D, HasDerivAt Y (u t) t)
    (hv : ∀ z, c ≤ ‖v z‖)
    (hvel : ∀ z t, t ∈ Ioo (max (l z.1.1) (l' z.1.2))
      (min (r z.1.1) (r' z.1.2)) → ‖u t - a t - v z‖ ≤ c/2)
    (hsep : ∀ t ∈ H, ‖Y t - X t‖ ≤ R) :
    volume H ≤ (Fintype.card ι + Fintype.card κ : ℝ≥0∞) *
      ENNReal.ofReal (4*R/c) := by
  classical
  let C : DirectionOverlap l r l' r' → Set ℝ :=
    fun z => Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))
  have hCD (z : DirectionOverlap l r l' r') : C z ⊆ D := by
    intro t ht
    exact hD z.1.1 ⟨(le_max_left _ _).trans ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have hcount := directionOverlap_card_le l r l' r' hleft hright
  have hcov : H ⊆ ⋃ z, H ∩ C z := by
    intro t ht
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcover t ht
    have hz : max (l i) (l' j) < min (r i) (r' j) :=
      (max_le hi.1 hj.1).trans_lt (lt_min hi.2 hj.2)
    exact mem_iUnion.mpr ⟨⟨(i,j),hz⟩,ht,max_le hi.1 hj.1,lt_min hi.2 hj.2⟩
  have hcell (z : DirectionOverlap l r l' r') :
      volume (H ∩ C z) ≤ ENNReal.ofReal (4*R/c) := by
    apply stable_cell_duration (convex_Ico _ _) inter_subset_right hc (hv z)
      (hXc.mono (hCD z)) (hYc.mono (hCD z))
    · intro t ht
      exact hX t (interior_mono (hCD z) ht)
    · intro t ht
      exact hY t (interior_mono (hCD z) ht)
    · intro t ht
      apply hvel z t
      simpa only [C, interior_Ico] using ht
    · intro t ht
      exact hsep t ht.1
  calc
    volume H ≤ volume (⋃ z, H ∩ C z) := measure_mono hcov
    _ ≤ ∑ z, volume (H ∩ C z) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _z : DirectionOverlap l r l' r', ENNReal.ofReal (4*R/c) :=
      Finset.sum_le_sum (fun z _ => hcell z)
    _ = (Fintype.card (DirectionOverlap l r l' r') : ℝ≥0∞) *
        ENNReal.ofReal (4*R/c) := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcount

lemma retarded_boundary_hit_duration {H : Set ℝ} (arrival : ℝ → ℝ)
    (B : Finset ℝ) {L : ℝ}
    (hdelay : ∀ s ∈ H, arrival s - s ≤ L) :
    volume {s ∈ H | ∃ b ∈ B, s ≤ b ∧ b ≤ arrival s} ≤
      (B.card : ℝ≥0∞) * ENNReal.ofReal L := by
  classical
  have hcov : {s ∈ H | ∃ b ∈ B, s ≤ b ∧ b ≤ arrival s} ⊆
      ⋃ b ∈ B, Icc (b-L) b := by
    intro s hs
    obtain ⟨b, hb, hsb, hba⟩ := hs.2
    exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, by
      have := hdelay s hs.1
      constructor <;> linarith⟩⟩
  calc
    _ ≤ volume (⋃ b ∈ B, Icc (b-L) b) := measure_mono hcov
    _ ≤ ∑ b ∈ B, volume (Icc (b-L) b) := measure_biUnion_finset_le B _
    _ = (B.card : ℝ≥0∞) * ENNReal.ofReal L := by
      simp only [Real.volume_Icc,sub_sub_cancel]
      simp

lemma PhaseFlowOn.refined_direction_occupation {s : Solution} {T t p c R : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T)
    (zX : Phase) {H : Phase → Set ℝ} (n : Phase → ℕ) (m N : ℕ)
    (l r : ∀ z, Fin (n z) → ℝ) (l' r' : Fin m → ℝ)
    (hleft : ∀ z i j, i ≠ j → Disjoint (Ico (l z i) (r z i)) (Ico (l z j) (r z j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    (hn : ∀ z, n z ≤ N)
    (v : ∀ z, DirectionOverlap (l z) (r z) l' r' → Vec)
    (hc : 0 < c)
    (hD : ∀ z i, Ico (l z i) (r z i) ⊆ Icc 0 T)
    (hcover : ∀ z τ, τ ∈ H z → (∃ i, τ ∈ Ico (l z i) (r z i)) ∧
      (∃ j, τ ∈ Ico (l' j) (r' j)))
    (hv : ∀ z k, c ≤ ‖v z k‖)
    (hvel : ∀ z k τ, τ ∈ Ioo (max (l z k.1.1) (l' k.1.2))
      (min (r z k.1.1) (r' k.1.2)) →
        ‖velocity (F.flow z τ).2 - velocity (F.flow zX τ).2 - v z k‖ ≤ c/2)
    (hsep : ∀ z τ, τ ∈ H z → ‖(F.flow z τ).1 - (F.flow zX τ).1‖ ≤ R)
    (hmom : ∀ z, (H z).Nonempty → p ≤ q (F.flow z t).2) :
    ENNReal.ofReal p * labelOccupation (fun z => s.f (0,z)) H ≤
      ENNReal.ofReal (((N:ℝ) + m) * (4*R/c)) *
        ENNReal.ofReal (∫ x : Vec, totalEnergy s (0,x)) := by
  apply F.label_occupation_cell_bound hs ht _ hmom
  intro z
  have hh := refined_direction_hit_duration (l z) (r z) l' r' (hleft z) hright
    (v z) hc (hD z) (hcover z) (F.continuousOn_time zX).fst
    (F.continuousOn_time z).fst
    (fun τ hτ => (F.ode zX τ (interior_subset hτ)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hτ) |>.fst)
    (fun τ hτ => (F.ode z τ (interior_subset hτ)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hτ) |>.fst)
    (hv z) (hvel z) (hsep z)
  simp only [Fintype.card_fin] at hh
  calc
    volume (H z) ≤ (n z + m : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := hh
    _ ≤ (N + m : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := by
      gcongr
      exact_mod_cast hn z
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma velocity_direction_deficit {v : Vec} (hv : v ≠ 0) :
    ‖velocity v - momentumDirection v‖ ≤ (q v)⁻¹^2 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hq := q_pos v
  have hnq := norm_lt_q v
  have hsq := q_sq v
  have he : velocity v = (‖v‖ / q v) • momentumDirection v := by
    rw [velocity,momentumDirection,smul_smul]
    congr 1
    field_simp
  rw [he]
  conv_lhs => arg 1; rhs; rw [← one_smul ℝ (momentumDirection v)]
  rw [← sub_smul,norm_smul,
    momentumDirection_norm hv,mul_one,Real.norm_eq_abs,abs_of_nonpos]
  · have hr : 0 < q v * (q v + ‖v‖) := mul_pos hq (by positivity)
    have hid : 1 - ‖v‖/q v = (q v * (q v + ‖v‖))⁻¹ := by
      field_simp
      nlinarith
    rw [neg_sub,hid]
    rw [inv_pow]
    exact (inv_le_inv₀ hr (sq_pos_of_pos hq)).mpr (by nlinarith)
  · exact sub_nonpos.mpr ((div_le_one hq).mpr hnq.le)

lemma velocity_change_of_direction {v w : Vec} {δ ε : ℝ}
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hdir : ‖momentumDirection v - momentumDirection w‖ ≤ δ)
    (hvq : (q v)⁻¹^2 ≤ ε) (hwq : (q w)⁻¹^2 ≤ ε) :
    ‖velocity v - velocity w‖ ≤ δ + 2*ε := by
  calc
    _ = ‖(velocity v-momentumDirection v) +
      (momentumDirection v-momentumDirection w) + (momentumDirection w-velocity w)‖ := by
        congr 1; abel
    _ ≤ ‖velocity v-momentumDirection v‖ + ‖momentumDirection v-momentumDirection w‖ +
      ‖momentumDirection w-velocity w‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε + δ + ε := by
      gcongr
      · exact (velocity_direction_deficit hv).trans hvq
      · rw [norm_sub_rev]; exact (velocity_direction_deficit hw).trans hwq
    _ = _ := by ring

lemma refined_direction_hit_duration_of_hits {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    {X Y a u : ℝ → Vec} {D H : Set ℝ} {c R : ℝ}
    (hc : 0 < c)
    (hD : ∀ i, Ico (l i) (r i) ⊆ D)
    (hcover : ∀ t ∈ H, (∃ i, t ∈ Ico (l i) (r i)) ∧
      (∃ j, t ∈ Ico (l' j) (r' j)))
    (hXc : ContinuousOn X D) (hYc : ContinuousOn Y D)
    (hX : ∀ t ∈ interior D, HasDerivAt X (a t) t)
    (hY : ∀ t ∈ interior D, HasDerivAt Y (u t) t)
    (hstable : ∀ z : DirectionOverlap l r l' r',
      (H ∩ Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))).Nonempty →
      ∃ v : Vec, c ≤ ‖v‖ ∧ ∀ t ∈ Ioo (max (l z.1.1) (l' z.1.2))
        (min (r z.1.1) (r' z.1.2)), ‖u t-a t-v‖ ≤ c/2)
    (hsep : ∀ t ∈ H, ‖Y t - X t‖ ≤ R) :
    volume H ≤ (Fintype.card ι + Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := by
  classical
  let C : DirectionOverlap l r l' r' → Set ℝ :=
    fun z => Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))
  have hcov : H ⊆ ⋃ z, H ∩ C z := by
    intro t ht
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hcover t ht
    have he : max (l i) (l' j) ≤ t := max_le hi.1 hj.1
    have hf : t < min (r i) (r' j) := lt_min hi.2 hj.2
    exact mem_iUnion.mpr ⟨⟨(i,j),he.trans_lt hf⟩,ht,he,hf⟩
  have hCD (z : DirectionOverlap l r l' r') : C z ⊆ D := fun _ ht =>
    hD z.1.1 ⟨(le_max_left _ _).trans ht.1,ht.2.trans_le (min_le_left _ _)⟩
  have hcell (z : DirectionOverlap l r l' r') : volume (H ∩ C z) ≤ ENNReal.ofReal (4*R/c) := by
    by_cases hh : (H ∩ C z).Nonempty
    · obtain ⟨v,hv,hvel⟩ := hstable z hh
      apply stable_cell_duration (convex_Ico _ _) inter_subset_right hc hv
        (hXc.mono (hCD z)) (hYc.mono (hCD z))
      · intro t ht
        exact hX t (interior_mono (hCD z) ht)
      · intro t ht
        exact hY t (interior_mono (hCD z) ht)
      · intro t ht
        apply hvel t
        simpa only [C,interior_Ico] using ht
      · intro t ht
        exact hsep t ht.1
    · rw [not_nonempty_iff_eq_empty.mp hh,measure_empty]
      exact bot_le
  calc
    volume H ≤ volume (⋃ z, H ∩ C z) := measure_mono hcov
    _ ≤ ∑ z, volume (H ∩ C z) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _z : DirectionOverlap l r l' r', ENNReal.ofReal (4*R/c) :=
      Finset.sum_le_sum (fun z _ => hcell z)
    _ = (Fintype.card (DirectionOverlap l r l' r') : ℝ≥0∞) * ENNReal.ofReal (4*R/c) := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast directionOverlap_card_le l r l' r' hleft hright

lemma relative_velocity_direction_cell {V W : ℝ → Vec} {t s₀ t₀ : ℝ} {c δ ε : ℝ}
    (hVt : V t ≠ 0) (hVs : V s₀ ≠ 0) (hWt : W t ≠ 0) (hWs : W s₀ ≠ 0)
    (hWt₀ : W t₀ ≠ 0)
    (hVdir : ‖momentumDirection (V t)-momentumDirection (V s₀)‖ ≤ δ)
    (hWdir : ‖momentumDirection (W t)-momentumDirection (W s₀)‖ ≤ δ)
    (hWcross : ‖momentumDirection (W s₀)-momentumDirection (W t₀)‖ ≤ δ)
    (hVqt : (q (V t))⁻¹^2 ≤ ε) (hVqs : (q (V s₀))⁻¹^2 ≤ ε)
    (hWqt : (q (W t))⁻¹^2 ≤ ε) (hWqs : (q (W s₀))⁻¹^2 ≤ ε)
    (hWqt₀ : (q (W t₀))⁻¹^2 ≤ ε)
    (hhit : 2*c ≤ ‖velocity (V s₀)-velocity (W t₀)‖)
    (hsmall : δ+2*ε ≤ c/4) :
    c ≤ ‖velocity (V s₀)-velocity (W s₀)‖ ∧
      ‖velocity (V t)-velocity (W t)-(velocity (V s₀)-velocity (W s₀))‖ ≤ c/2 := by
  have hcross := velocity_change_of_direction hWs hWt₀ hWcross hWqs hWqt₀
  constructor
  · have hn := norm_sub_le (velocity (V s₀)-velocity (W s₀))
      (velocity (W t₀)-velocity (W s₀))
    have he : velocity (V s₀)-velocity (W s₀)-(velocity (W t₀)-velocity (W s₀)) =
        velocity (V s₀)-velocity (W t₀) := by abel
    rw [he,norm_sub_rev (velocity (W t₀))] at hn
    have hnn := norm_nonneg (velocity (W s₀)-velocity (W t₀))
    linarith
  · have hvs := velocity_change_of_direction hVt hVs hVdir hVqt hVqs
    have hws := velocity_change_of_direction hWt hWs hWdir hWqt hWqs
    have he : velocity (V t)-velocity (W t)-(velocity (V s₀)-velocity (W s₀)) =
      (velocity (V t)-velocity (V s₀))-(velocity (W t)-velocity (W s₀)) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)

lemma direction_good_hit_separation {X : ℝ → Vec} {Y n : Vec} {V : ℝ → Vec}
    {s t δ ε b : ℝ} (hst : s ≤ t)
    (hX : ∀ r ∈ Icc s t, HasDerivWithinAt X (velocity (V r)) (Icc s t) r)
    (hnz : ∀ r ∈ Icc s t, V r ≠ 0)
    (hq : ∀ r ∈ Icc s t, (q (V r))⁻¹^2 ≤ ε)
    (hdir : ∀ r ∈ Icc s t, ‖momentumDirection (V r)-momentumDirection (V t)‖ ≤ δ)
    (hcone : X t-Y=(t-s) • n) (hbin : ‖velocity (V t)-n‖ ≤ b) :
    ‖Y-X s‖ ≤ (δ+2*ε+b)*(t-s) := by
  have ht : t ∈ Icc s t := right_mem_Icc.mpr hst
  have hd (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivWithinAt (fun v => X v-v • n) (velocity (V r)-n) (Icc s t) r := by
    have hh := (hX r hr).sub ((hasDerivWithinAt_id r _).smul_const n)
    change HasDerivWithinAt (fun v => X v-v • n) (velocity (V r)-1 • n) (Icc s t) r at hh
    simpa only [one_smul] using hh
  have hb (r : ℝ) (hr : r ∈ Icc s t) : ‖velocity (V r)-n‖ ≤ δ+2*ε+b := by
    have hc := velocity_change_of_direction (hnz r hr) (hnz t ht) (hdir r hr) (hq r hr) (hq t ht)
    calc
      _ = ‖(velocity (V r)-velocity (V t))+(velocity (V t)-n)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hc hbin)
  have hh := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (left_mem_Icc.mpr hst) ht
  have he : X t-t • n-(X s-s • n)=Y-X s := by
    calc
      _ = (X t-Y-(t-s) • n)+(Y-X s) := by rw [sub_smul]; abel
      _ = _ := by rw [hcone,sub_self,zero_add]
  rw [he,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] at hh
  exact hh

lemma PhaseFlowOn.direction_closed_bin_hit_separation {s : Solution} {T φ δ ε t τ l r : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    (hcellT : Ico l r ⊆ Icc 0 T) (ht : t ∈ Ico l r) (hτ : τ ∈ Ico l r)
    (hnz : ∀ u ∈ Ico l r, (F.flow zX u).2 ≠ 0)
    (hq : ∀ u ∈ Ico l r, (q (F.flow zX u).2)⁻¹^2 ≤ ε)
    (hdir : ∀ a ∈ Ico l r, ∀ b ∈ Ico l r,
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖ ≤ δ)
    (hbin : InClosedConeBin F.flow zX B τ t zY)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) (hsmall : δ+2*ε ≤ φ/16) :
    ‖(F.flow zY t).1-(F.flow zX t).1‖ ≤ 5*B.rmax*φ := by
  obtain ⟨n,_,hcone,hbound,_,_⟩ := small_closed_bin_hit_geometry hbin hr hφ hd hDlo hDhi hw
  have hdelay := hbin.2.1
  have hta : t ≤ τ := by linarith [hdelay.1]
  have hinside : Icc t τ ⊆ Ico l r := fun u hu => ⟨ht.1.trans hu.1,hu.2.trans_lt hτ.2⟩
  have hST := hinside.trans hcellT
  have hder (u : ℝ) (hu : u ∈ Icc t τ) : HasDerivWithinAt
      (fun v => (F.flow zX v).1) (velocity (F.flow zX u).2) (Icc t τ) u := by
    have hh : HasDerivWithinAt (fun v => (F.flow zX v).1)
        (velocity (F.flow zX u).2) (Icc 0 T) u := (F.ode zX u (hST hu)).fst
    exact hh.mono hST
  have hh := direction_good_hit_separation hta hder
    (fun u hu => hnz u (hinside hu)) (fun u hu => hq u (hinside hu))
    (fun u hu => hdir u (hinside hu) τ hτ) hcone hbound
  calc
    _ ≤ (δ+2*ε+4*φ)*(τ-t) := hh
    _ ≤ (5*φ)*(τ-t) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hta)
    _ ≤ (5*φ)*B.rmax := mul_le_mul_of_nonneg_left hdelay.2 (by positivity)
    _ = _ := by ring

lemma PhaseFlowOn.direction_good_hit_duration {s : Solution} {T φ δ ε : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι → ℝ) (l' r' : κ → ℝ)
    (hleft : ∀ i j, i ≠ j → Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀ i j, i ≠ j → Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    (hsrcT : ∀ i, Ico (l i) (r i) ⊆ Icc 0 T)
    (hrecT : ∀ j, Ico (l' j) (r' j) ⊆ Icc 0 T)
    (hsrcnz : ∀ i t, t ∈ Ico (l i) (r i) → (F.flow zY t).2 ≠ 0)
    (hrecnz : ∀ j t, t ∈ Ico (l' j) (r' j) → (F.flow zX t).2 ≠ 0)
    (hsrcq : ∀ i t, t ∈ Ico (l i) (r i) → (q (F.flow zY t).2)⁻¹^2 ≤ ε)
    (hrecq : ∀ j t, t ∈ Ico (l' j) (r' j) → (q (F.flow zX t).2)⁻¹^2 ≤ ε)
    (hsrcdir : ∀ i, ∀ a ∈ Ico (l i) (r i), ∀ b ∈ Ico (l i) (r i),
      ‖momentumDirection (F.flow zY a).2-momentumDirection (F.flow zY b).2‖ ≤ δ)
    (hrecdir : ∀ j, ∀ a ∈ Ico (l' j) (r' j), ∀ b ∈ Ico (l' j) (r' j),
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖ ≤ δ)
    {H : Set ℝ} (arrival : ℝ → ℝ)
    (hcover : ∀ t ∈ H, ∃ i, t ∈ Ico (l i) (r i))
    (hgood : ∀ t ∈ H, ∃ j, t ∈ Ico (l' j) (r' j) ∧ arrival t ∈ Ico (l' j) (r' j))
    (hbin : ∀ t ∈ H, InClosedConeBin F.flow zX B (arrival t) t zY)
    (hr : 0 < B.rmin) (hφ : 0 < φ)
    (hd : B.dmax ≤ φ^2/32) (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hw : 4 ≤ φ*B.wmin) (hsmall : δ+2*ε ≤ φ/16) :
    volume H ≤ (Fintype.card ι + Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal (80*B.rmax) := by
  have hcov : ∀ t ∈ H, (∃ i, t ∈ Ico (l i) (r i)) ∧
      (∃ j, t ∈ Ico (l' j) (r' j)) := by
    intro t ht
    obtain ⟨j,hj,_⟩ := hgood t ht
    exact ⟨hcover t ht,j,hj⟩
  have hsep (t : ℝ) (ht : t ∈ H) : ‖(F.flow zY t).1-(F.flow zX t).1‖ ≤ 5*B.rmax*φ := by
    obtain ⟨j,hj,hja⟩ := hgood t ht
    exact F.direction_closed_bin_hit_separation zX zY B (hrecT j) hj hja
      (hrecnz j) (hrecq j) (hrecdir j) (hbin t ht) hr hφ hd hDlo hDhi hw hsmall
  have hstab (z : DirectionOverlap l r l' r')
      (hh : (H ∩ Ico (max (l z.1.1) (l' z.1.2)) (min (r z.1.1) (r' z.1.2))).Nonempty) :
      ∃ v : Vec, φ/4 ≤ ‖v‖ ∧ ∀ t ∈ Ioo (max (l z.1.1) (l' z.1.2))
        (min (r z.1.1) (r' z.1.2)),
        ‖velocity (F.flow zY t).2-velocity (F.flow zX t).2-v‖ ≤ (φ/4)/2 := by
    obtain ⟨u,hu,huc⟩ := hh
    have hui : u ∈ Ico (l z.1.1) (r z.1.1) :=
      ⟨(le_max_left _ _).trans huc.1,huc.2.trans_le (min_le_left _ _)⟩
    have huj : u ∈ Ico (l' z.1.2) (r' z.1.2) :=
      ⟨(le_max_right _ _).trans huc.1,huc.2.trans_le (min_le_right _ _)⟩
    obtain ⟨j,hj,hja⟩ := hgood u hu
    have hjz : j=z.1.2 := by
      by_contra hne
      exact Set.disjoint_left.mp (hright j z.1.2 hne) hj huj
    subst j
    obtain ⟨_,_,_,_,hlo,_⟩ := small_closed_bin_hit_geometry (hbin u hu) hr hφ hd hDlo hDhi hw
    have hsmall' : δ+2*ε ≤ (φ/4)/4 := by linarith
    have hh (t : ℝ) (hti : t ∈ Ico (l z.1.1) (r z.1.1))
        (htj : t ∈ Ico (l' z.1.2) (r' z.1.2)) :=
      relative_velocity_direction_cell (V:=fun t => (F.flow zY t).2)
        (W:=fun t => (F.flow zX t).2) (t:=t) (s₀:=u) (t₀:=arrival u)
        (c:=φ/4) (δ:=δ) (ε:=ε)
        (hsrcnz _ t hti) (hsrcnz _ u hui) (hrecnz _ t htj) (hrecnz _ u huj) (hrecnz _ _ hja)
        (hsrcdir _ t hti u hui) (hrecdir _ t htj u huj) (hrecdir _ u huj _ hja)
        (hsrcq _ t hti) (hsrcq _ u hui) (hrecq _ t htj) (hrecq _ u huj) (hrecq _ _ hja)
        (show 2*(φ/4) ≤ ‖velocity (F.flow zY u).2-velocity (F.flow zX (arrival u)).2‖ by linarith)
        hsmall'
    refine ⟨velocity (F.flow zY u).2-velocity (F.flow zX u).2,(hh u hui huj).1,?_⟩
    intro t ht
    exact (hh t ⟨(le_max_left _ _).trans ht.1.le,ht.2.trans_le (min_le_left _ _)⟩
      ⟨(le_max_right _ _).trans ht.1.le,ht.2.trans_le (min_le_right _ _)⟩).2
  have hbound := refined_direction_hit_duration_of_hits l r l' r' hleft hright
    (X:=fun t => (F.flow zX t).1) (Y:=fun t => (F.flow zY t).1)
    (a:=fun t => velocity (F.flow zX t).2) (u:=fun t => velocity (F.flow zY t).2)
    (D:=Icc 0 T) (H:=H) (R:=5*B.rmax*φ)
    (by positivity : 0 < φ/4) hsrcT hcov
    ((F.continuousOn_time zX).fst) ((F.continuousOn_time zY).fst)
    (fun t ht => ((F.ode zX t (interior_subset ht)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).fst)
    (fun t ht => ((F.ode zY t (interior_subset ht)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)).fst)
    hstab hsep
  have he : 4*(5*B.rmax*φ)/(φ/4)=80*B.rmax := by field_simp [hφ.ne']; ring
  simpa only [he] using hbound

lemma receiver_cells_good_or_bad {κ : Type*} [Fintype κ]
    (l r : κ→ℝ) {s t : ℝ} (hst : s≤t) (hc : ∃j,s∈Ico (l j) (r j)) :
    (∃j,s∈Ico (l j) (r j) ∧ t∈Ico (l j) (r j)) ∨
      ∃b∈Finset.univ.image r,s≤b ∧ b≤t := by
  classical
  obtain ⟨j,hj⟩ := hc
  by_cases ht : t<r j
  · exact Or.inl ⟨j,hj,⟨hj.1.trans hst,ht⟩⟩
  · exact Or.inr ⟨r j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,hj.2.le,le_of_not_gt ht⟩

lemma PhaseFlowOn.direction_total_hit_duration {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase) (B : ClosedConeBin)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l r : ι→ℝ) (l' r' : κ→ℝ)
    (hleft : ∀i j,i≠j→Disjoint (Ico (l i) (r i)) (Ico (l j) (r j)))
    (hright : ∀i j,i≠j→Disjoint (Ico (l' i) (r' i)) (Ico (l' j) (r' j)))
    {δ ε φ : ℝ}
    (hsrcT : ∀i,Ico (l i) (r i)⊆Icc 0 T)
    (hrecT : ∀j,Ico (l' j) (r' j)⊆Icc 0 T)
    (hsrcnz : ∀i t,t∈Ico (l i) (r i)→(F.flow zY t).2≠0)
    (hrecnz : ∀j t,t∈Ico (l' j) (r' j)→(F.flow zX t).2≠0)
    (hsrcq : ∀i t,t∈Ico (l i) (r i)→(q (F.flow zY t).2)⁻¹^2≤ε)
    (hrecq : ∀j t,t∈Ico (l' j) (r' j)→(q (F.flow zX t).2)⁻¹^2≤ε)
    (hsrcdir : ∀i,∀a∈Ico (l i) (r i),∀b∈Ico (l i) (r i),
      ‖momentumDirection (F.flow zY a).2-momentumDirection (F.flow zY b).2‖≤δ)
    (hrecdir : ∀j,∀a∈Ico (l' j) (r' j),∀b∈Ico (l' j) (r' j),
      ‖momentumDirection (F.flow zX a).2-momentumDirection (F.flow zX b).2‖≤δ)
    {H : Set ℝ} (arrival : ℝ→ℝ)
    (hsrc : ∀t∈H,∃i,t∈Ico (l i) (r i))
    (hrec : ∀t∈H,∃j,t∈Ico (l' j) (r' j))
    (hbin : ∀t∈H,InClosedConeBin F.flow zX B (arrival t) t zY)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hφ : 0<φ)
    (hd : B.dmax≤φ^2/32) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hw : 4≤φ*B.wmin) (hsmall : δ+2*ε≤φ/16) :
    volume H≤(Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (81*B.rmax) := by
  classical
  let ends := Finset.univ.image r'
  let Bad := {t∈H | ∃b∈ends,t≤b ∧ b≤arrival t}
  let Good := H\Bad
  have hgood : ∀t∈Good,∃j,t∈Ico (l' j) (r' j) ∧ arrival t∈Ico (l' j) (r' j) := by
    intro t ht
    have hh := (hbin t ht.1).2.1.1
    rcases receiver_cells_good_or_bad l' r' (s:=t) (t:=arrival t)
      (by linarith) (hrec t ht.1) with hg|hb
    · exact hg
    · exact False.elim (ht.2 ⟨ht.1,hb⟩)
  have hg := F.direction_good_hit_duration zX zY B l r l' r' hleft hright
    hsrcT hrecT hsrcnz hrecnz hsrcq hrecq hsrcdir hrecdir arrival
    (fun t ht=>hsrc t ht.1) hgood (fun t ht=>hbin t ht.1)
    hr hφ hd hDlo hDhi hw hsmall
  have hb : volume Bad≤(Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := by
    have he : ends.card≤Fintype.card κ := (Finset.card_image_le).trans (by simp)
    have h := retarded_boundary_hit_duration (H:=H) arrival ends
      (fun t ht=>(hbin t ht).2.1.2)
    apply h.trans
    gcongr
  have hc : H⊆Good∪Bad := by
    intro t ht
    by_cases htb : t∈Bad
    · exact Or.inr htb
    · exact Or.inl ⟨ht,htb⟩
  calc
    volume H≤volume Good+volume Bad := (measure_mono hc).trans (measure_union_le _ _)
    _ ≤ (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (80*B.rmax)+
      (Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := add_le_add hg hb
    _ ≤ (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal (80*B.rmax)+
      (Fintype.card ι+Fintype.card κ : ℝ≥0∞)*ENNReal.ofReal B.rmax := by gcongr; exact le_add_left le_rfl
    _ = _ := by
      rw [←mul_add,←ENNReal.ofReal_add (by positivity) hrmax]
      congr 2
      ring

end RVM

end

end OAI
