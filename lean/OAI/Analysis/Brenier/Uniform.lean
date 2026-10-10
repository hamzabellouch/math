import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358.UniformSource

variable {d : ℕ} {K : Set (E d)}

/-- Normalization of a compact body with nonempty interior gives a probability measure. -/
theorem probability (hK : IsCompact K) (hinterior : (interior K).Nonempty) :
    IsProbabilityMeasure (uniformMeasure K) := by
  constructor
  rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_pos_of_nonempty_interior volume hinterior).ne'
    hK.measure_ne_top

theorem supported (hK : MeasurableSet K) : IsSupported (uniformMeasure K) K := by
  simp [IsSupported, uniformMeasure, Measure.restrict_apply hK.compl]

theorem ae_mem (hK : MeasurableSet K) : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
  ae_iff.mpr (supported hK)

/-- Continuous functions on a compact source are integrable after normalization,
including the zero-volume case. -/
theorem integrable_continuousOn {F : Type*} [NormedAddCommGroup F]
    (hK : IsCompact K) {f : E d → F} (hf : ContinuousOn f K) :
    Integrable f (uniformMeasure K) := by
  by_cases hv : volume K = 0
  · have hzero : uniformMeasure K = 0 := by
      simp [uniformMeasure, Measure.restrict_eq_zero.mpr hv]
    rw [hzero]
    exact integrable_zero_measure
  · exact (hf.integrableOn_compact hK).smul_measure (ENNReal.inv_ne_top.mpr hv)

theorem integrable_norm (hK : IsCompact K) :
    Integrable (fun x : E d => ‖x‖) (uniformMeasure K) :=
  integrable_continuousOn hK continuous_norm.continuousOn

theorem integrable_norm_pow (hK : IsCompact K) (n : ℕ) :
    Integrable (fun x : E d => ‖x‖ ^ n) (uniformMeasure K) :=
  integrable_continuousOn hK (continuous_norm.pow n).continuousOn

theorem exists_ae_norm_bound (hK : IsCompact K) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  filter_upwards [ae_mem hK.measurableSet] with x hx
  exact (hC x hx).trans (le_max_left _ _)

end Problem358.UniformSource

namespace Problem358

/-- Normalizing a set of strictly positive finite volume gives a probability source. -/
theorem isProbabilityMeasure_uniformMeasure_of_volume {d : ℕ} {K : Set (E d)}
    (hpos : 0 < volume K) (hfinite : volume K ≠ ∞) :
    IsProbabilityMeasure (uniformMeasure K) := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite

/-- The source hypotheses in the qualified stability theorem guarantee normalization. -/
theorem isProbabilityMeasure_uniformMeasure_of_compact {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hKi : (interior K).Nonempty) :
    IsProbabilityMeasure (uniformMeasure K) :=
  isProbabilityMeasure_uniformMeasure_of_volume
    (Measure.measure_pos_of_nonempty_interior volume hKi) hK.measure_lt_top.ne

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Problem358

/-- Every uniform source is absolutely continuous with respect to ambient volume,
without any measurability, finiteness, or nondegeneracy assumptions on its set. -/
theorem uniformMeasure_absolutelyContinuous {d : ℕ} (K : Set (E d)) :
    uniformMeasure K ≪ volume := by
  exact Measure.smul_absolutelyContinuous.trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- A volume-null exceptional set is null for any uniform source. -/
theorem uniformMeasure_null_of_volume_null {d : ℕ} (K : Set (E d))
    {N : Set (E d)} (hN : volume N = 0) : uniformMeasure K N = 0 :=
  uniformMeasure_absolutelyContinuous K hN

/-- A proper affine subspace is null for any uniform source. -/
theorem uniformMeasure_affineSubspace {d : ℕ} (K : Set (E d))
    (A : AffineSubspace ℝ (E d)) (hA : A ≠ ⊤) :
    uniformMeasure K (A : Set (E d)) = 0 :=
  uniformMeasure_null_of_volume_null K (Measure.addHaar_affineSubspace volume A hA)

/-- A level set of a real scalar product is an affine subspace. -/
def innerLevelSubspace {d : ℕ} (a : E d) (b : ℝ) : AffineSubspace ℝ (E d) where
  carrier := {x | inner ℝ a x = b}
  smul_vsub_vadd_mem' := by
    intro t p q r hp hq hr
    change inner ℝ a p = b at hp
    change inner ℝ a q = b at hq
    change inner ℝ a r = b at hr
    change inner ℝ a (t • (p - q) + r) = b
    simp only [inner_add_right, inner_smul_right, inner_sub_right, hp, hq, hr]
    ring

/-- A hyperplane with nonzero normal is a proper affine subspace. -/
theorem innerLevelSubspace_ne_top {d : ℕ} {a : E d} (ha : a ≠ 0) (b : ℝ) :
    innerLevelSubspace a b ≠ ⊤ := by
  intro h
  have hz : (0 : E d) ∈ innerLevelSubspace a b := by rw [h]; trivial
  have haa : a ∈ innerLevelSubspace a b := by rw [h]; trivial
  change inner ℝ a 0 = b at hz
  change inner ℝ a a = b at haa
  apply ha
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simpa only [inner_zero_right] using haa.trans hz.symm

/-- Every nontrivial real scalar-product level set is volume-null. -/
theorem volume_inner_level {d : ℕ} {a : E d} (ha : a ≠ 0) (b : ℝ) :
    volume {x : E d | inner ℝ a x = b} = 0 := by
  exact Measure.addHaar_affineSubspace volume (innerLevelSubspace a b)
    (innerLevelSubspace_ne_top ha b)

/-- Every nontrivial real scalar-product level set is uniform-source-null. -/
theorem uniformMeasure_inner_level {d : ℕ} (K : Set (E d))
    {a : E d} (ha : a ≠ 0) (b : ℝ) :
    uniformMeasure K {x : E d | inner ℝ a x = b} = 0 :=
  uniformMeasure_null_of_volume_null K (volume_inner_level ha b)

/-- The tie set of two affine functions with distinct slopes is null. -/
theorem uniformMeasure_affine_tie {d : ℕ} (K : Set (E d))
    {y z : E d} (hyz : y ≠ z) (c e : ℝ) :
    uniformMeasure K {x : E d | inner ℝ y x + c = inner ℝ z x + e} = 0 := by
  have hsets : {x : E d | inner ℝ y x + c = inner ℝ z x + e} =
      {x : E d | inner ℝ (y - z) x = e - c} := by
    ext x
    simp only [Set.mem_ofPred_eq, inner_sub_left]
    constructor <;> intro hx <;> linarith
  rw [hsets]
  exact uniformMeasure_inner_level K (sub_ne_zero.mpr hyz) (e - c)

/-- Outside a null set, equal values of two affine functions mean equal slopes. -/
theorem ae_affine_eq_imp_slope_eq {d : ℕ} (K : Set (E d))
    (y z : E d) (c e : ℝ) :
    ∀ᵐ x ∂uniformMeasure K, inner ℝ y x + c = inner ℝ z x + e → y = z := by
  by_cases hyz : y = z
  · exact Filter.Eventually.of_forall (fun _ _ => hyz)
  · have hne : ∀ᵐ x ∂uniformMeasure K, inner ℝ y x + c ≠ inner ℝ z x + e := by
      rw [ae_iff]
      simpa only [not_not] using uniformMeasure_affine_tie K hyz c e
    filter_upwards [hne] with x hx h
    exact (hx h).elim

/-- A countable family of affine functions has no ties between distinct slopes
at almost every source point. In particular this applies to finite maxima. -/
theorem ae_all_affine_eq_imp_slope_eq {d : ℕ} {ι : Type*} [Countable ι]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) :
    ∀ᵐ x ∂uniformMeasure K, ∀ i j,
      inner ℝ (y i) x + c i = inner ℝ (y j) x + c j → y i = y j := by
  simp only [ae_all_iff]
  intro i j
  exact ae_affine_eq_imp_slope_eq K (y i) (y j) (c i) (c j)

/-- The boundary of a convex set is null under every uniform source. -/
theorem uniformMeasure_frontier_convex {d : ℕ} (K : Set (E d))
    {S : Set (E d)} (hS : Convex ℝ S) :
    uniformMeasure K (frontier S) = 0 :=
  uniformMeasure_null_of_volume_null K (hS.addHaar_frontier volume)

/-- Normalization always has total mass at most one, even for degenerate sets. -/
theorem uniformMeasure_univ_le_one {d : ℕ} (K : Set (E d)) :
    uniformMeasure K Set.univ ≤ 1 := by
  simp only [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_le_one (volume K)

/-- Every normalized restriction is a finite measure, including zero/infinite-volume sets. -/
theorem uniformMeasure_finite {d : ℕ} (K : Set (E d)) :
    IsFiniteMeasure (uniformMeasure K) :=
  ⟨lt_of_le_of_lt (uniformMeasure_univ_le_one K) ENNReal.one_lt_top⟩

end Problem358

end

noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology

namespace Problem358.UniformSource

/-- The topological support of normalized volume on a convex body is the whole body. -/
theorem subset_support {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    K ⊆ (uniformMeasure K).support := by
  have hi : interior K ⊆ (uniformMeasure K).support := by
    intro x hx
    apply (Measure.mem_support_iff_forall x).mpr
    intro U hU
    have hpos : 0 < volume (U ∩ K) :=
      Measure.measure_pos_of_mem_nhds volume (Filter.inter_mem hU (mem_interior_iff_mem_nhds.mp hx))
    rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply' hK.measurableSet,
      smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hK.measure_ne_top) hpos.ne'
  have hclosure : closure (interior K) ⊆ (uniformMeasure K).support :=
    closure_minimal hi Measure.isClosed_support
  have hKclosure : closure (interior K) = K := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  rwa [hKclosure] at hclosure

theorem support_eq {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    (uniformMeasure K).support = K := by
  exact Set.Subset.antisymm
    (Measure.support_subset_of_isClosed hK.isClosed (ae_mem hK.measurableSet))
    (subset_support hK hconv hne)

end Problem358.UniformSource

end

end OAI
