/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license.
Authors: OpenAI
-/
import OAI.AlgebraicGeometry.CartierSections.ExpansionValuation

namespace OAI

/-!
# Compact normalized monomial cones

Local algebra for uniform Cartier sections.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace CartierSections.FormalMonomial
variable {σ k : Type*} [Fintype σ] [CommRing k]

/-- A single finite subset of the support computes all nonnegative weighted
orders, including all faces. The exponents do not depend on the weights. -/
lemma exists_finite_formula (f : MvPowerSeries σ k) :
    ∃ T : Finset (σ →₀ ℕ), ∀ w : σ → NNReal,
      value w f = T.inf (fun d => (Finsupp.weight w d : ENNReal)) := by
  obtain ⟨T, hTS, hT⟩ := finite_dominated_generators {d | MvPowerSeries.coeff d f ≠ 0}
  refine ⟨T, fun w => le_antisymm ?_ ?_⟩
  · exact Finset.le_inf_iff.mpr fun d hd => value_le_weight w (hTS hd)
  · apply (le_value_iff w).mpr
    intro d hd
    obtain ⟨e, he, hed⟩ := hT d hd
    exact (Finset.inf_le he).trans (ENNReal.coe_le_coe.mpr (weight_mono w hed))

omit [Fintype σ] in
lemma continuous_weight (d : σ →₀ ℕ) :
    Continuous (fun w : σ → NNReal => Finsupp.weight w d) := by
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  fun_prop

/-- Formal monomial evaluation is continuous on the closed cone of nonnegative weights. -/
lemma continuous_value (f : MvPowerSeries σ k) :
    Continuous (fun w : σ → NNReal => value w f) := by
  obtain ⟨T, hT⟩ := exists_finite_formula f
  simp_rw [hT]
  exact Continuous.finset_inf_apply fun d _ => ENNReal.continuous_coe.comp (continuous_weight d)

end CartierSections.FormalMonomial

namespace CartierSections
variable {σ k A : Type*} [Fintype σ] [Field k] [CommRing A] [Algebra k A]

lemma continuous_monomial_evaluation (θ : A →ₐ[k] MvPowerSeries σ k) (f : A) :
    Continuous (fun w : σ → NNReal => expansionValuation θ w f) :=
  FormalMonomial.continuous_value (θ f)

/-- We use the pointwise topology on actual regular-function evaluations,
which is precisely the topology invoked in the E compactness argument. -/
lemma continuous_monomial_evaluations (θ : A →ₐ[k] MvPowerSeries σ k) :
    Continuous (fun w : σ → NNReal => fun f : A => expansionValuation θ w f) :=
  continuous_pi fun f => continuous_monomial_evaluation θ f

/-- The normalized section of a monomial cone; `a i` is the positive
discrepancy of its primitive ray in the application. -/
def normalizedWeights (a : σ → NNReal) : Set (σ → NNReal) :=
  {w | ∑ i, a i * w i = 1}

lemma isClosed_normalizedWeights (a : σ → NNReal) :
    IsClosed (normalizedWeights a) := by
  change IsClosed {w : σ → NNReal | ∑ i, a i * w i = 1}
  exact isClosed_eq (by fun_prop) continuous_const

lemma isCompact_normalizedWeights (a : σ → NNReal) (ha : ∀ i, 0 < a i) :
    IsCompact (normalizedWeights a) := by
  refine (isCompact_Icc (a := (0 : σ → NNReal)) (b := fun i => (a i)⁻¹)).of_isClosed_subset
    (isClosed_normalizedWeights a) ?_
  intro w hw
  refine ⟨fun i => bot_le, fun i => ?_⟩
  have h : a i * w i ≤ 1 := calc
    a i * w i ≤ ∑ j, a j * w j := Finset.single_le_sum (f := fun j => a j * w j) (fun j _ => bot_le) (Finset.mem_univ i)
    _ = 1 := hw
  have hd : w i ≤ (1 : NNReal) / a i := (le_div_iff₀ (ha i)).mpr (by
    simpa only [mul_comm] using h)
  simpa only [one_div] using hd

/-- The normalized monomial cone is compact in pointwise regular-function evaluation. -/
lemma isCompact_monomial_cone (θ : A →ₐ[k] MvPowerSeries σ k)
    (a : σ → NNReal) (ha : ∀ i, 0 < a i) :
    IsCompact ((fun w : σ → NNReal => fun f : A => expansionValuation θ w f) ''
      normalizedWeights a) :=
  (isCompact_normalizedWeights a ha).image (continuous_monomial_evaluations θ)

end CartierSections

namespace CartierSections
section MonomialSlice
variable {σ k A ι J : Type*} [Fintype σ] [Finite ι]
  [Field k] [CommRing A] [Algebra k A]

/-- Literal evaluation constraints from the common lc slice, on the ambient
space of readings of regular functions. In use `m j` is the positive integer
multiplicity from E, and the normalization of discrepancy is imposed by the
normalized coordinate cone. -/
def valuationConstraints (h : A) (F : J → A) (m : J → ENNReal) : Set (A → ENNReal) :=
  {v | v h = 1} ∩ ⋂ j, {v | m j ≤ v (F j)}

omit [CommRing A] in
lemma isClosed_valuationConstraints (h : A) (F : J → A) (m : J → ENNReal) :
    IsClosed (valuationConstraints h F m) := by
  exact (isClosed_eq (continuous_apply h) continuous_const).inter
    (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply (F j)))

/-- A finite union of formal-coordinate cones cut by normalized evaluation constraints. -/
def finiteChartSlice (θ : ι → A →ₐ[k] MvPowerSeries σ k)
    (a : ι → σ → NNReal) (h : A) (F : J → A) (m : J → ENNReal) : Set (A → ENNReal) :=
  (⋃ i, (fun w : σ → NNReal => fun f : A => expansionValuation (θ i) w f) ''
    normalizedWeights (a i)) ∩ valuationConstraints h F m

lemma isCompact_finiteChartSlice (θ : ι → A →ₐ[k] MvPowerSeries σ k)
    (a : ι → σ → NNReal) (ha : ∀ i j, 0 < a i j)
    (h : A) (F : J → A) (m : J → ENNReal) :
    IsCompact (finiteChartSlice θ a h F m) :=
  (isCompact_iUnion fun i => isCompact_monomial_cone (θ i) (a i) (ha i)).inter_right
    (isClosed_valuationConstraints h F m)

/-- Compactness turns simultaneous domination on every finite set of functions
into domination on all functions. -/
lemma simultaneous_targets_of_finite (θ : ι → A →ₐ[k] MvPowerSeries σ k)
    (a : ι → σ → NNReal) (ha : ∀ i j, 0 < a i j)
    (h : A) (F : J → A) (m : J → ENNReal) (s : A → ENNReal)
    (hfinite : ∀ T : Finset A, ∃ (i : ι) (w : σ → NNReal),
      w ∈ normalizedWeights (a i) ∧
      (fun f => expansionValuation (θ i) w f) ∈ valuationConstraints h F m ∧
      ∀ f ∈ T, s f ≤ expansionValuation (θ i) w f) :
    ∃ (i : ι) (w : σ → NNReal), w ∈ normalizedWeights (a i) ∧
      (fun f => expansionValuation (θ i) w f) ∈ valuationConstraints h F m ∧
      ∀ f, s f ≤ expansionValuation (θ i) w f := by
  classical
  let C := finiteChartSlice θ a h F m
  have hC : IsCompact C := isCompact_finiteChartSlice θ a ha h F m
  obtain ⟨v, hv, hb⟩ := hC.inter_iInter_nonempty (fun f => {v : A → ENNReal | s f ≤ v f})
    (fun f => isClosed_le continuous_const (continuous_apply f)) (by
      intro T
      obtain ⟨i, w, hw, hc, ht⟩ := hfinite T
      refine ⟨fun f => expansionValuation (θ i) w f, ?_, ?_⟩
      · exact ⟨Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hw⟩, hc⟩
      · exact Set.mem_iInter.mpr fun f => Set.mem_iInter.mpr fun hf => ht f hf)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv.1
  obtain ⟨w, hw, rfl⟩ := hi
  exact ⟨i, w, hw, hv.2, fun f => Set.mem_iInter.mp hb f⟩

end MonomialSlice
end CartierSections

end

end OAI
