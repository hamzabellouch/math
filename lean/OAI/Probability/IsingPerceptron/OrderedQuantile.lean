import Mathlib
import OAI.Probability.IsingPerceptron.ArrayGeometry

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma map_restrict_fst_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hS : MeasurableSet S) :
    ((μ.restrict (univ ×ˢ T)).map Prod.fst) S = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_fst hS,Measure.restrict_apply (hS.preimage measurable_fst)]
  congr 1
  ext x
  simp

lemma map_restrict_snd_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hT : MeasurableSet T) :
    ((μ.restrict (S ×ˢ univ)).map Prod.snd) T = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_snd hT,Measure.restrict_apply (hT.preimage measurable_snd)]
  congr 1
  ext x
  simp [and_comm]

lemma measure_pair_eq_of_lower_rectangles {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ a b : ℝ, μ (Iic a ×ˢ Iic b) = ν (Iic a ×ˢ Iic b))
    (hU : μ univ = ν univ) : μ = ν := by
  have hfirst (a : ℝ) : (μ.restrict (Iic a ×ˢ univ)).map Prod.snd =
      (ν.restrict (Iic a ×ˢ univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro b
    rw [map_restrict_snd_rectangle μ measurableSet_Iic,map_restrict_snd_rectangle ν measurableSet_Iic]
    exact h a b
  have hsecond (T : Set ℝ) (hT : MeasurableSet T) :
      (μ.restrict (univ ×ˢ T)).map Prod.fst = (ν.restrict (univ ×ˢ T)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro a
    rw [map_restrict_fst_rectangle μ measurableSet_Iic,map_restrict_fst_rectangle ν measurableSet_Iic]
    have he := congrArg (fun ρ : Measure ℝ => ρ T) (hfirst a)
    simpa only [map_restrict_snd_rectangle μ hT,map_restrict_snd_rectangle ν hT] using he
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod _ hU
  rintro _ ⟨S,hS,T,hT,rfl⟩
  have he := congrArg (fun ρ : Measure ℝ => ρ S) (hsecond T hT)
  simpa only [map_restrict_fst_rectangle μ hS,map_restrict_fst_rectangle ν hS] using he

lemma ordered_pair_cdf (μ : Measure (ℝ × ℝ))
    (ho : ∀ x ∈ μ.support, ∀ y ∈ μ.support, x.1 < y.1 → x.2 ≤ y.2) (a b : ℝ) :
    μ (Iic a ×ˢ Iic b) = min (μ (Prod.fst ⁻¹' Iic a)) (μ (Prod.snd ⁻¹' Iic b)) := by
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic a
  let T : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic b
  have hrect : Iic a ×ˢ Iic b = S ∩ T := rfl
  rw [hrect]
  change μ (S ∩ T) = min (μ S) (μ T)
  have hsupport : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  by_cases h : ∀ x ∈ μ.support, x ∈ S → x ∈ T
  · have hst : S ≤ᵐ[μ] T := hsupport.mono (fun x hx => h x hx)
    rw [min_eq_left (measure_mono_ae hst)]
    apply measure_congr
    filter_upwards [hst] with x hx
    exact propext ⟨fun hh => hh.1,fun hh => ⟨hh,hx hh⟩⟩
  · push Not at h
    obtain ⟨x,hx,hxs,hxt⟩ := h
    have hts : T ≤ᵐ[μ] S := by
      filter_upwards [hsupport] with y hy
      intro hyt
      change y.1 ≤ a
      by_contra! hy'
      have hxy := ho x hx y hy (lt_of_le_of_lt hxs hy')
      exact hxt (hxy.trans hyt)
    rw [min_eq_right (measure_mono_ae hts)]
    apply measure_congr
    filter_upwards [hts] with y hy
    exact propext ⟨fun hh => hh.2,fun hh => ⟨hy hh,hh⟩⟩

lemma pair_quantile_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (a b : ℝ) :
    (unitUniform.map (fun u => (quantileFunction μ u,quantileFunction ν u))) (Iic a ×ˢ Iic b) =
      min (μ (Iic a)) (ν (Iic b)) := by
  rw [Measure.map_apply ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable) (measurableSet_Iic.prod measurableSet_Iic)]
  have he : (fun u => (quantileFunction μ u,quantileFunction ν u)) ⁻¹' (Iic a ×ˢ Iic b) =ᵐ[unitUniform]
      Iic (min (cdf μ a) (cdf ν b)) := by
    filter_upwards [quantile_preimage_Iic hμ a,quantile_preimage_Iic hν b] with u hu hv
    change (quantileFunction μ u ≤ a ∧ quantileFunction ν u ≤ b) = (u ≤ min (cdf μ a) (cdf ν b))
    rw [le_min_iff]
    exact congrArg₂ And hu hv
  rw [measure_congr he,unitUniform_Iic ⟨le_min (cdf_nonneg μ a) (cdf_nonneg ν b),
    (min_le_left _ _).trans (cdf_le_one μ a)⟩,ENNReal.ofReal_min,ofReal_cdf,ofReal_cdf]

 

theorem ordered_pair_quantile_law {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (ho : ∀ x ∈ ρ.support, ∀ y ∈ ρ.support, x.1 < y.1 → x.2 ≤ y.2)
    (hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0:ℝ) 1 ∧ x.2 ∈ Icc (0:ℝ) 1) :
    unitUniform.map (fun u => (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u)) = ρ := by
  let : IsProbabilityMeasure (ρ.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (ρ.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance
  have hμ : ∀ᵐ x ∂ρ.map Prod.fst, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.1))
  have hν : ∀ᵐ x ∂ρ.map Prod.snd, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.2))
  let : IsProbabilityMeasure (unitUniform.map (fun u =>
      (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u))) :=
    (Measure.isProbabilityMeasure_map_iff ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable).aemeasurable).mpr inferInstance
  apply measure_pair_eq_of_lower_rectangles _ (by simp)
  intro a b
  rw [pair_quantile_cdf hμ hν,ordered_pair_cdf ρ ho,
    Measure.map_apply measurable_fst measurableSet_Iic,Measure.map_apply measurable_snd measurableSet_Iic]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 
def treeTail (n d : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (((n+1:ℕ):ℝ)*t-d))

lemma continuous_treeTail (n d : ℕ) : Continuous (treeTail n d) := by
  unfold treeTail; fun_prop

lemma treeTail_mem (n d : ℕ) (t : ℝ) : treeTail n d t ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma treeTail_level (n d j : ℕ) : treeTail n d ((j:ℝ)/(n+1:ℕ)) =
    if d < j then 1 else 0 := by
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  simp only [treeTail,mul_div_cancel₀ _ hn]
  split_ifs with h
  · have h' : (d:ℝ)+1 ≤ j := by exact_mod_cast h
    rw [min_eq_left (by linarith),max_eq_right zero_le_one]
  · have h' : (j:ℝ) ≤ d := by exact_mod_cast (Nat.le_of_not_gt h)
    rw [min_eq_right (by linarith),max_eq_left (by linarith)]

lemma treeTail_overlap (n : ℕ) (d : Fin n) (x y : LabeledLeaf n) :
    treeTail n d (treeOverlap n x y) =
      if (labeledAddress n x).take (d+1) = (labeledAddress n y).take (d+1) then 1 else 0 := by
  rw [treeOverlap,treeTail_level]
  simp only [labeled_prefix_eq_iff n x y (d := d+1) (by omega),Nat.add_one_le_iff]

lemma enrichedArrayLaw_treeTail {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) (d : Fin n) :
    (∫ x, treeTail n d (treeArray x 0 1)
      ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray)) = 1-b d := by
  rw [enrichedArrayLaw_integral P r n b h u ν hm (fun x => treeTail n d (treeArray x 0 1))
    ((continuous_treeTail n d).comp (by unfold treeArray; fun_prop)).measurable]
  let D : (Fin 2 → Spin N × LabeledLeaf n) → ℝ := fun σ =>
    if (labeledAddress n (σ 1).2).take (d+1) = (labeledAddress n (σ 0).2).take (d+1) then 1 else 0
  have hbD (σ) : |D σ| ≤ 1 := by dsimp only [D]; split_ifs <;> norm_num
  have he := enrichedReplicaLaw_integral hN n b hh h0 u hu ν P hm hK hφ r D hbD
    (fun i : Fin 2 => i.val) Fin.val_injective
  rw [← enriched_tilted_label_tail P r n b hb h u ν hm d]
  change _ = enrichedReplicaAverage P r n b h u ν φ D
  rw [← he]
  apply integral_congr_ae
  apply ae_of_all
  intro σ
  change treeTail n d (treeOverlap n (σ 0).2 (σ 1).2) = _
  rw [treeTail_overlap]
  simp only [D,Fin.val_zero,Fin.val_one,eq_comm]

def treeLevels (n : ℕ) : Set ℝ := range (fun j : Fin (n+1) => (j:ℝ)/(n+1:ℕ))

lemma isClosed_treeLevels (n : ℕ) : IsClosed (treeLevels n) := (finite_range _).isClosed

lemma treeOverlap_mem_levels (n : ℕ) (x y : LabeledLeaf n) : treeOverlap n x y ∈ treeLevels n :=
  ⟨⟨labeledCommonDepth n x y,by have := labeledCommonDepth_le n x y; omega⟩,rfl⟩

lemma enrichedArrayLaw_treeLevels {N : ℕ} {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b h : ℕ → ℝ)
    (u : Fin N → ℝ) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) :
    ∀ᵐ x ∂(enrichedArrayLaw P r n b h u ν hm : Measure JointArray), treeArray x 0 1 ∈ treeLevels n := by
  rw [enrichedArrayLaw]
  apply (ae_map_iff (measurable_sampledOverlapArray (enrichedJointEntry n)).aemeasurable
    ((isClosed_treeLevels n).measurableSet.preimage (by unfold treeArray; fun_prop))).mpr
  exact ae_of_all _ (fun σ => treeOverlap_mem_levels n (σ 0).2 (σ 1).2)

 

theorem enrichedArrayLaw_limit_tree
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (h : ℕ → ℕ → ℝ) (hh : ∀ k, Monotone (h k)) (h0 : ∀ k, 0 ≤ h k 0)
    (u : (k : ℕ) → Fin (N k) → ℝ) (hu : ∀ k j, |u k j| ≤ 2)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    (A : ℕ → Type*) [∀ k, MeasurableSpace (A k)]
    (P : (k : ℕ) → Measure (A k)) [∀ k, IsProbabilityMeasure (P k)]
    (φ : (k : ℕ) → A k → Spin (N k) → ℝ) (hm : ∀ k, Measurable (φ k))
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ k y x, |φ k y x| ≤ K)
    (r : ℕ → ℝ≥0) (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw (P k) (r k) n b (h k) (u k) (ν k) (hm k)) atTop (𝓝 μ)) :
    (∀ᵐ x ∂(μ : Measure JointArray), treeArray x 0 1 ∈ treeLevels n) ∧
      ∀ d : Fin n, (∫ x, treeTail n d (treeArray x 0 1) ∂(μ : Measure JointArray)) = 1-b d := by
  constructor
  · exact ae_closed_of_weak_limit hL ((isClosed_treeLevels n).preimage (by unfold treeArray; fun_prop))
      (fun k => enrichedArrayLaw_treeLevels (P k) (r k) n b (h k) (u k) (ν k) (hm k))
  · intro d
    have he := jointArray_tendsto_integral hL
      (hF := (continuous_treeTail n d).comp (by unfold treeArray; fun_prop : Continuous (fun x : JointArray => treeArray x 0 1)))
    have ha (k) := enrichedArrayLaw_treeTail (hN k) n b hb (hh k) (h0 k) (u k) (hu k)
      (ν k) (P k) (hm k) hK (hφ k) (r k) d
    have he' := he.congr' (Eventually.of_forall ha)
    exact tendsto_nhds_unique he' tendsto_const_nhds

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma treeTail_eq_level_indicator {n d : ℕ} {t : ℝ} (ht : t ∈ treeLevels n) :
    treeTail n d t = if (d:ℝ)/(n+1:ℕ) < t then 1 else 0 := by
  obtain ⟨j,rfl⟩ := ht
  rw [treeTail_level]
  simp only [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (n+1:ℕ)),Nat.cast_lt]

lemma cdf_of_treeTail {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {n d : ℕ}
    (hρ : ∀ᵐ t ∂ρ, t ∈ treeLevels n) {b : ℝ}
    (hb : (∫ t, treeTail n d t ∂ρ) = 1-b) : cdf ρ ((d:ℝ)/(n+1:ℕ)) = b := by
  have hi : Integrable (treeTail n d) ρ :=
    integrable_of_measurable_abs_le (continuous_treeTail n d).measurable
      (fun t => by rw [abs_of_nonneg (treeTail_mem n d t).1]; exact (treeTail_mem n d t).2)
  calc
    _ = ∫ t, (Iic ((d:ℝ)/(n+1:ℕ))).indicator (fun _ => (1:ℝ)) t ∂ρ := by
      rw [integral_indicator_const _ measurableSet_Iic,cdf_eq_real,smul_eq_mul,mul_one]
    _ = ∫ t, 1-treeTail n d t ∂ρ := integral_congr_ae (hρ.mono (fun t ht => by
      simp only [treeTail_eq_level_indicator (d := d) ht]
      by_cases h : (d:ℝ)/(n+1:ℕ) < t
      · simp only [Set.indicator,Set.mem_Iic,h,not_le.mpr h,ite_false,ite_true,sub_self]
      · simp only [Set.indicator,Set.mem_Iic,h,le_of_not_gt h,ite_false,ite_true,sub_zero]))
    _ = b := by rw [integral_sub (integrable_const _) hi,hb]; simp

lemma quantile_treeTail {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {n d : ℕ}
    (hs : ∀ᵐ t ∂ρ, t ∈ Icc (0:ℝ) 1)
    (hρ : ∀ᵐ t ∂ρ, t ∈ treeLevels n) {b : ℝ}
    (hb : (∫ t, treeTail n d t ∂ρ) = 1-b) :
    ∀ᵐ u ∂unitUniform, treeTail n d (quantileFunction ρ u) = if b < u then 1 else 0 := by
  have hm := (monotone_quantileFunction hs).measurable
  have hl := quantileFunction_law hs
  have hlev : ∀ᵐ u ∂unitUniform, quantileFunction ρ u ∈ treeLevels n := by
    apply (ae_map_iff hm.aemeasurable (isClosed_treeLevels n).measurableSet).mp
    rw [hl]
    exact hρ
  have hc := cdf_of_treeTail hρ hb
  filter_upwards [hlev,ae_restrict_mem (μ := volume) measurableSet_Ioo] with u hu hu'
  rw [treeTail_eq_level_indicator hu]
  have he := quantileFunction_le_iff hs hu' (x := (d:ℝ)/(n+1:ℕ))
  rw [hc] at he
  have he' : (d:ℝ)/(n+1:ℕ) < quantileFunction ρ u ↔ b < u := by
    simpa only [not_le] using not_congr he
  simp only [he']

 

theorem ordered_pair_tree_tail_integral {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (ho : ∀ x ∈ ρ.support, ∀ y ∈ ρ.support, x.1 < y.1 → x.2 ≤ y.2)
    (hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0:ℝ) 1 ∧ x.2 ∈ Icc (0:ℝ) 1)
    {n d : ℕ} (hl : ∀ᵐ x ∂ρ, x.2 ∈ treeLevels n) {b : ℝ}
    (ht : (∫ x, treeTail n d x.2 ∂ρ) = 1-b) :
    (∫ x, x.1*treeTail n d x.2 ∂ρ) =
      ∫ u in Ioi b, quantileFunction (ρ.map Prod.fst) u ∂unitUniform := by
  let : IsProbabilityMeasure (ρ.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (ρ.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance
  have hr : ∀ᵐ t ∂ρ.map Prod.fst, t ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.1))
  have hT : ∀ᵐ t ∂ρ.map Prod.snd, t ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.2))
  have hlev : ∀ᵐ t ∂ρ.map Prod.snd, t ∈ treeLevels n :=
    (ae_map_iff measurable_snd.aemeasurable (isClosed_treeLevels n).measurableSet).mpr hl
  have hti : (∫ t, treeTail n d t ∂ρ.map Prod.snd) = 1-b := by
    rw [integral_map measurable_snd.aemeasurable (continuous_treeTail n d).measurable.aestronglyMeasurable]
    exact ht
  have hqt := quantile_treeTail hT hlev hti
  have hm := (monotone_quantileFunction hr).measurable.prodMk (monotone_quantileFunction hT).measurable
  have hF : Measurable (fun x : ℝ × ℝ => x.1*treeTail n d x.2) :=
    measurable_fst.mul ((continuous_treeTail n d).measurable.comp measurable_snd)
  have hi := integral_map (μ := unitUniform) hm.aemeasurable hF.aestronglyMeasurable
  rw [ordered_pair_quantile_law ho hs] at hi
  rw [hi,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [hqt] with u hu
  rw [hu]
  by_cases h : b < u <;> simp [h]

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma enrichedMeanPressure_field_cost {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h l : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (hl : Monotone l) (l0 : 0 ≤ l 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    |enrichedMeanPressure P r n b (fun i => h i+l i) u ν φ-
      enrichedMeanPressure P r n b h u ν φ| ≤ l n/2 := by
  have he := enrichedMeanPressure_field_insert hN n b hb hh h0 hl l0 u hu ν P hm hK hφ r
    (a := 1) zero_le_one
  simp only [one_mul,Real.sqrt_one] at he
  have hc := random_cylinder_cgf_mean_bounds (P := enrichedCylinderLaw P r n b)
    (measurable_enrichedGibbsReference n h u ν hm) (externalFieldCoefficients n l)
    (fun s => (externalFieldCoefficients_variance n hl l0 s).le) 1
  simp only [one_pow,one_mul] at hc
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc' := (div_le_iff₀ hn).mpr (show (∫ z, cgf (fun x => cylinderField
      (externalFieldCoefficients n l x) z.2) (enrichedGibbsReference n h u ν φ z.1) 1
      ∂(enrichedCylinderLaw P r n b).prod gaussianCoordinates) ≤ l n/2*(N:ℝ) by nlinarith [hc.2])
  have hc0 := div_nonneg hc.1 hn.le
  rw [he]
  apply abs_le.mpr
  constructor <;> nlinarith

 

def finiteFieldPath {n : ℕ} (a : Fin (n+1) → ℝ) (i : ℕ) : ℝ :=
  ∑ j, if j.val ≤ i then a j else 0

lemma finiteFieldPath_last {n : ℕ} (a : Fin (n+1) → ℝ) : finiteFieldPath a n = ∑ j, a j := by
  simp only [finiteFieldPath,show ∀ j : Fin (n+1), j.val ≤ n from fun j => by omega,ite_true]

lemma finiteFieldPath_nonneg {n : ℕ} {a : Fin (n+1) → ℝ} (ha : ∀ j, 0 ≤ a j) (i : ℕ) :
    0 ≤ finiteFieldPath a i := Finset.sum_nonneg (fun j _ => by split_ifs; exact ha j; exact le_refl 0)

lemma monotone_finiteFieldPath {n : ℕ} {a : Fin (n+1) → ℝ} (ha : ∀ j, 0 ≤ a j) :
    Monotone (finiteFieldPath a) := by
  intro i k hik
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ i
  · simp [hj,hj.trans hik]
  · simp only [hj,ite_false]
    split_ifs; exact ha j; exact le_refl 0

lemma finiteFieldPath_add {n : ℕ} (a c : Fin (n+1) → ℝ) :
    finiteFieldPath (fun i => a i+c i) = fun i => finiteFieldPath a i+finiteFieldPath c i := by
  funext i
  simp only [finiteFieldPath,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma finiteFieldPath_sub {n : ℕ} (a c : Fin (n+1) → ℝ) :
    finiteFieldPath (fun i => a i-c i) = fun i => finiteFieldPath a i-finiteFieldPath c i := by
  funext i
  simp only [finiteFieldPath,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma enrichedMeanPressure_field_lipschitz {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {a c : Fin (n+1) → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 ≤ c j)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    |enrichedMeanPressure P r n b (finiteFieldPath a) u ν φ-
      enrichedMeanPressure P r n b (finiteFieldPath c) u ν φ| ≤ (∑ j, |a j-c j|)/2 := by
  let d : Fin (n+1) → ℝ := fun j => min (a j) (c j)
  have hd : ∀ j, 0 ≤ d j := fun j => le_min (ha j) (hc j)
  have had : ∀ j, 0 ≤ a j-d j := fun j => sub_nonneg.mpr (min_le_left _ _)
  have hcd : ∀ j, 0 ≤ c j-d j := fun j => sub_nonneg.mpr (min_le_right _ _)
  have heA := enrichedMeanPressure_field_cost hN n b hb (monotone_finiteFieldPath hd)
    (finiteFieldPath_nonneg hd 0) (monotone_finiteFieldPath had) (finiteFieldPath_nonneg had 0)
    u hu ν P hm hK hφ r
  have heC := enrichedMeanPressure_field_cost hN n b hb (monotone_finiteFieldPath hd)
    (finiteFieldPath_nonneg hd 0) (monotone_finiteFieldPath hcd) (finiteFieldPath_nonneg hcd 0)
    u hu ν P hm hK hφ r
  simp only [finiteFieldPath_sub,add_sub_cancel] at heA heC
  have hs : finiteFieldPath a n-finiteFieldPath d n + (finiteFieldPath c n-finiteFieldPath d n) =
      ∑ j, |a j-c j| := by
    simp only [finiteFieldPath_last,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [d]
    rcases le_total (a j) (c j) with h | h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have ht := abs_sub_le (enrichedMeanPressure P r n b (finiteFieldPath a) u ν φ)
    (enrichedMeanPressure P r n b (finiteFieldPath d) u ν φ)
    (enrichedMeanPressure P r n b (finiteFieldPath c) u ν φ)
  rw [abs_sub_comm (enrichedMeanPressure P r n b (finiteFieldPath d) u ν φ)] at ht
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace IsingPerceptron
open Set Filter
open scoped Topology

lemma factorial_successor_term (n : ℕ) (x : ℝ) :
    (n+1 : ℝ) * x^(n+1) / (n+1).factorial = x * (x^n / n.factorial) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma summable_count_pow_div_factorial (x : ℝ) :
    Summable (fun n : ℕ => (n : ℝ)*x^n/n.factorial) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.cast_add,Nat.cast_one,factorial_successor_term] using
    (Real.summable_pow_div_factorial x).mul_left x

lemma summable_linear_pow_div_factorial (C K x : ℝ) :
    Summable (fun n : ℕ => (C+K*n)*x^n/n.factorial) := by
  have hs := ((Real.summable_pow_div_factorial x).mul_left C).add
    ((summable_count_pow_div_factorial x).mul_left K)
  apply hs.congr
  intro n
  ring

lemma summable_growth_exponentialSeries {a : ℕ → ℝ} {C K : ℝ}
    (_hC : 0 ≤ C) (_hK : 0 ≤ K) (ha : ∀ n, |a n| ≤ C+K*n) (x : ℝ) :
    Summable (fun n : ℕ => a n*x^n/n.factorial) := by
  apply Summable.of_norm_bounded (summable_linear_pow_div_factorial C K |x|)
  intro n
  simp only [Real.norm_eq_abs,abs_div,abs_mul,abs_pow,Nat.abs_cast]
  gcongr
  exact ha n

lemma hasDerivAt_exponentialSeries {a : ℕ → ℝ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (ha : ∀ n, |a n| ≤ C+K*n) (x : ℝ) :
    HasDerivAt (fun y => ∑' n : ℕ, a n*y^n/n.factorial)
      (∑' n : ℕ, a (n+1)*x^n/n.factorial) x := by
  let B := |x|+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hshift n : |a (n+1)| ≤ (C+K)+K*n := by
    have H := ha (n+1)
    push_cast at H
    linarith
  have hu := summable_linear_pow_div_factorial (C+K) K B
  have hg (n : ℕ) (y : ℝ) :
      HasDerivAt (fun y : ℝ => a (n+1)*y^(n+1)/(n+1).factorial)
        (a (n+1)*y^n/n.factorial) y := by
    convert (((hasDerivAt_id y).pow (n+1)).const_mul (a (n+1))).div_const ((n+1).factorial : ℝ) using 1 <;> try rfl
    simp only [id_eq,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,Nat.factorial_succ,Nat.cast_mul]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
    field_simp
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-B) B) :
      ‖a (n+1)*y^n/n.factorial‖ ≤ ((C+K)+K*n)*B^n/n.factorial := by
    have hab : |y| ≤ B := le_of_lt (abs_lt.mpr hy)
    simp only [Real.norm_eq_abs,abs_div,abs_mul,abs_pow,Nat.abs_cast]
    gcongr
    exact hshift n
  have hzero : Summable (fun n : ℕ => a (n+1)*(0:ℝ)^(n+1)/(n+1).factorial) := by simp
  have hs := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-B) B).isPreconnected
    (fun n y _ => hg n y) hbound (show (0:ℝ) ∈ Ioo (-B) B from ⟨by linarith, hB⟩) hzero
    (show x ∈ Ioo (-B) B from abs_lt.mp (by dsimp [B]; linarith))
  have he (y : ℝ) : (∑' n : ℕ, a n*y^n/n.factorial) =
      a 0 + ∑' n : ℕ, a (n+1)*y^(n+1)/(n+1).factorial := by
    rw [← (summable_growth_exponentialSeries hC hK ha y).sum_add_tsum_nat_add 1]
    simp
  simpa only [← he] using hs.const_add (a 0)

 

def poissonMean (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * ∑' n : ℕ, a n*t^n/n.factorial

lemma poissonMean_eq_integral (a : ℕ → ℝ) (r : ℝ≥0) :
    poissonMean a r = ∫ n, a n ∂poissonMeasure r := by
  rw [poissonMean,integral_poissonMeasure,← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

lemma hasDerivAt_poissonMean {a : ℕ → ℝ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (ha : ∀ n, |a n| ≤ C+K*n) (t : ℝ) :
    HasDerivAt (poissonMean a) (poissonMean (fun n => a (n+1)-a n) t) t := by
  have hshift n : |a (n+1)| ≤ (C+K)+K*n := by
    have H := ha (n+1)
    push_cast at H
    linarith
  have hd := (((hasDerivAt_id t).neg.exp).mul (hasDerivAt_exponentialSeries hC hK ha t))
  have he : (∑' n : ℕ, (a (n+1)-a n)*t^n/n.factorial) =
      (∑' n : ℕ, a (n+1)*t^n/n.factorial) - ∑' n : ℕ, a n*t^n/n.factorial := by
    rw [← (summable_growth_exponentialSeries (add_nonneg hC hK) hK hshift t).tsum_sub
      (summable_growth_exponentialSeries hC hK ha t)]
    apply tsum_congr
    intro n
    ring
  convert hd using 1 <;> try rfl
  change Real.exp (-t) * (∑' n : ℕ, (a (n+1)-a n)*t^n/n.factorial) =
    Real.exp (-t) * (-1) * (∑' n : ℕ, a n*t^n/n.factorial) +
    Real.exp (-t) * (∑' n : ℕ, a (n+1)*t^n/n.factorial)
  rw [he]
  ring

lemma poissonMean_derivative_bound {a : ℕ → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (ha : ∀ n, |a (n+1)-a n| ≤ K) (r : ℝ≥0) :
    |poissonMean (fun n => a (n+1)-a n) r| ≤ K := by
  rw [poissonMean_eq_integral]
  exact (abs_integral_le_integral_abs).trans (by
    have hi : Integrable (fun n => |a (n+1)-a n|) (poissonMeasure r) :=
      Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable K
        (ae_of_all _ (fun n => by simpa only [Real.norm_eq_abs,abs_abs] using ha n))
    simpa using integral_mono hi (integrable_const K) ha)

 

theorem poisson_count_derivative {a : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ n, |a (n+1)-a n| ≤ K) (t : ℝ) :
    HasDerivAt (poissonMean a) (poissonMean (fun n => a (n+1)-a n) t) t := by
  have hg : ∀ n, |a n| ≤ |a 0|+K*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh : |a (n+1)| ≤ |a n|+K := by
        calc
          _ = |a n+(a (n+1)-a n)| := by congr 1; ring
          _ ≤ |a n|+|a (n+1)-a n| := abs_add_le _ _
          _ ≤ _ := add_le_add_right (ha n) _
      push_cast
      linarith
  exact hasDerivAt_poissonMean (abs_nonneg _) hK hg t

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

abbrev EnrichedFixedData (n : ℕ) (A : Type*) := ((ℕ → A) × LabeledTree n) × (ℕ → ℝ)

def enrichedFixedLaw {A : Type*} [MeasurableSpace A] (P : Measure A)
    (n : ℕ) (b : ℕ → ℝ) : Measure (EnrichedFixedData n A) :=
  ((Measure.infinitePi (fun _ : ℕ => P)).prod (labeledCascadeLaw n b)).prod gaussianCoordinates

instance enrichedFixedLaw_probability {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (n : ℕ) (b : ℕ → ℝ) : IsProbabilityMeasure (enrichedFixedLaw P n b) := by
  unfold enrichedFixedLaw
  infer_instance

def enrichedCountJoin {n : ℕ} {A : Type*} (z : ℕ × EnrichedFixedData n A) : EnrichedCylinderData n A :=
  (((z.1,z.2.1.1),z.2.1.2),z.2.2)

lemma enrichedCountJoin_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (r : ℝ≥0) (n : ℕ) (b : ℕ → ℝ) :
    MeasurePreserving (enrichedCountJoin (n := n) (A := A))
      ((poissonMeasure r).prod (enrichedFixedLaw P n b)) (enrichedCylinderLaw P r n b) := by
  let μ := poissonMeasure r
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  let ρ := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let τ := gaussianCoordinates
  have h1 := (measurePreserving_prodAssoc μ (ν.prod ρ) τ).symm MeasurableEquiv.prodAssoc
  have h2 := ((measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc).prod
    (MeasurePreserving.id τ)
  exact h2.comp h1

lemma poisson_ae_all {p : ℕ → Prop} {r : ℝ≥0} (hr : 0 < r) (hp : ∀ᵐ m ∂poissonMeasure r, p m) :
    ∀ m, p m := by
  intro m
  apply ae_iff_of_countable.mp hp m
  rw [poissonMeasure_singleton]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  positivity

lemma enrichedFixed_pressure_integrable {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    Integrable (fun z => enrichedCylinderPressure n h u ν φ (enrichedCountJoin (m,z))) (enrichedFixedLaw P n b) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi := (enrichedCylinderPressure_field_cap hN n b hb hh h0 (le_refl (h n)) u hu ν P hm hK hφ
    (1:ℝ≥0) (α := 1/N) (by simp [hn])).1
  have hi' := (hi.comp_measurePreserving (enrichedCountJoin_preserving P 1 n b)).integrable (by norm_num)
  exact poisson_ae_all (by norm_num : (0:ℝ≥0)<1) hi'.prod_right_ae m

lemma enrichedFixed_exp_ae {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (m : ℕ) :
    ∀ᵐ z ∂enrichedFixedLaw P n b,
      Integrable (fun s => Real.exp (enrichedHamiltonian n h u φ (enrichedCountJoin (m,z)) s))
        (labeledSpinReference n ν z.1.2) := by
  have he := (enrichedCountJoin_preserving P 1 n b).quasiMeasurePreserving.ae
    (enrichedCylinder_exp_ae hN n b hh h0 u hu ν P hK hφ (1:ℝ≥0))
  exact poisson_ae_all (by norm_num : (0:ℝ≥0)<1) (Measure.ae_ae_of_ae_prod he) m

lemma abs_cgf_one_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : X → ℝ} (hY : Measurable Y) {K : ℝ} (hYb : ∀ x, |Y x| ≤ K) :
    |cgf Y ν 1| ≤ K := by
  have hi : Integrable (fun x => Real.exp (Y x)) ν := Integrable.of_bound
    hY.exp.aestronglyMeasurable (Real.exp K) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
        Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hYb x))))
  have hp : 0 < ∫ x, Real.exp (Y x) ∂ν := MeasureTheory.integral_exp_pos hi
  have hu : (∫ x, Real.exp (Y x) ∂ν) ≤ Real.exp K := by
    simpa using integral_mono hi (integrable_const (Real.exp K))
      (fun x => Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hYb x)))
  have hl : Real.exp (-K) ≤ ∫ x, Real.exp (Y x) ∂ν := by
    simpa using integral_mono (integrable_const (Real.exp (-K))) hi
      (fun x => Real.exp_le_exp.mpr (neg_le.mp (le_trans (neg_le_abs _) (hYb x))))
  unfold cgf mgf
  simp only [one_mul]
  apply abs_le.mpr
  exact ⟨by simpa using Real.log_le_log (Real.exp_pos (-K)) hl,
    by simpa using Real.log_le_log hp hu⟩

end IsingPerceptron

end

end OAI
