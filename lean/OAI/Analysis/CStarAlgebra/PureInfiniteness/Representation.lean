import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

section Ultra
variable {ι : Type*} (ω : Ultrafilter ι)

lemma exists_complex_ultralimit (z : ι → ℂ) (R : ℝ) (hz : ∀ i, ‖z i‖ ≤ R) :
    ∃ c : ℂ, Tendsto z (ω : Filter ι) (𝓝 c) := by
  obtain ⟨c, _, hc⟩ := (isCompact_closedBall (0 : ℂ) R).ultrafilter_le_nhds
    (ω.map z) (by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff]
      change ∀ᶠ i in (ω : Filter ι), z i ∈ Metric.closedBall 0 R
      exact Filter.Eventually.of_forall (fun i => by simpa using hz i))
  exact ⟨c, by
    change Filter.map z (ω : Filter ι) ≤ 𝓝 c
    simpa only [Ultrafilter.coe_map] using hc⟩

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
variable (f : ι → A →ₚ[ℂ] ℂ) (hf : ∀ i a, ‖f i a‖ ≤ ‖a‖)

def ultraValue (a : A) : ℂ :=
  (exists_complex_ultralimit ω (fun i => f i a) ‖a‖ (fun i => hf i a)).choose

lemma tendsto_ultraValue (a : A) :
    Tendsto (fun i => f i a) (ω : Filter ι) (𝓝 (ultraValue ω f hf a)) :=
  (exists_complex_ultralimit ω (fun i => f i a) ‖a‖ (fun i => hf i a)).choose_spec

def ultraPositive : A →ₚ[ℂ] ℂ where
  toFun := ultraValue ω f hf
  map_add' a b := by
    apply tendsto_nhds_unique (tendsto_ultraValue ω f hf (a + b))
    simpa only [map_add] using (tendsto_ultraValue ω f hf a).add
      (tendsto_ultraValue ω f hf b)
  map_smul' c a := by
    apply tendsto_nhds_unique (tendsto_ultraValue ω f hf (c • a))
    simpa only [map_smul, RingHom.id_apply] using (tendsto_ultraValue ω f hf a).const_smul c
  monotone' := by
    intro a b hab
    exact le_of_tendsto_of_tendsto (tendsto_ultraValue ω f hf a)
      (tendsto_ultraValue ω f hf b) (Filter.Eventually.of_forall fun i => (f i).monotone hab)

lemma tendsto_ultraPositive (a : A) :
    Tendsto (fun i => f i a) (ω : Filter ι) (𝓝 (ultraPositive ω f hf a)) :=
  tendsto_ultraValue ω f hf a

lemma ultraPositive_norm_le (a : A) : ‖ultraPositive ω f hf a‖ ≤ ‖a‖ :=
  le_of_tendsto' (tendsto_ultraPositive ω f hf a).norm (fun i => hf i a)

lemma ultraPositive_eq_zero_of_tendsto {a : A}
    (ha : Tendsto (fun i => f i a) (ω : Filter ι) (𝓝 0)) :
    ultraPositive ω f hf a = 0 :=
  tendsto_nhds_unique (tendsto_ultraPositive ω f hf a) ha
end Ultra

section GNS
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

lemma gns_zero_of_sandwich (a : A)
    (ha : ∀ b : A, f (star (a * b) * (a * b)) = 0) :
    f.gnsNonUnitalStarAlgHom a = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (f.gnsNonUnitalStarAlgHom a).continuous continuous_const
  | ih b =>
    rw [zero_apply, ← norm_eq_zero]
    rw [f.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe]
    change ‖f.toPreGNS (a * f.ofPreGNS b)‖ = 0
    rw [f.preGNS_norm_def]
    simp only [f.ofPreGNS_toPreGNS, ha, Complex.zero_re, Real.sqrt_zero]

lemma gnsStar_nonzero_of_value {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (g : B →ₚ[ℂ] ℂ) (a : B)
    (ha : g (star a * a) ≠ 0) : g.gnsStarAlgHom a ≠ 0 := by
  intro h
  have hx := congrArg (fun T : g.GNS →L[ℂ] g.GNS => T
    (↑(g.toPreGNS 1) : g.GNS)) h
  have hn := congrArg norm hx
  change ‖g.gnsNonUnitalStarAlgHom a (↑(g.toPreGNS 1) : g.GNS)‖ = ‖(0 : g.GNS)‖ at hn
  rw [g.gnsNonUnitalStarAlgHom_apply_coe, UniformSpace.Completion.norm_coe] at hn
  have hab : ‖g.toPreGNS a‖ = 0 := by
    simp only [norm_zero] at hn
    change ‖g.toPreGNS (a * 1)‖ = 0 at hn
    simpa using hn
  have hh := g.preGNS_norm_sq (g.toPreGNS a)
  rw [hab] at hh
  apply ha
  simpa using hh.symm
end GNS

section Vector
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

def vectorPositive : A →ₚ[ℂ] ℂ where
  toFun a := ⟪ξ, π a ξ⟫_ℂ
  map_add' a b := by simp
  map_smul' c a := by simp
  monotone' := by
    intro a b hab
    rw [← sub_nonneg, ← inner_sub_right, ← sub_apply, ← map_sub]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp
      (map_nonneg π (sub_nonneg.mpr hab)) |>.inner_nonneg_right ξ

lemma vectorPositive_norm_le (hξ : ‖ξ‖ ≤ 1) (a : A) :
    ‖vectorPositive π ξ a‖ ≤ ‖a‖ := by
  calc
    ‖vectorPositive π ξ a‖ ≤ ‖ξ‖ * ‖π a ξ‖ := norm_inner_le_norm ξ (π a ξ)
    _ ≤ ‖ξ‖ * (‖a‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((π a).le_opNorm ξ |>.trans (mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg ξ))) (norm_nonneg ξ)
    _ ≤ 1 * (‖a‖ * 1) := mul_le_mul hξ
      (mul_le_mul_of_nonneg_left hξ (norm_nonneg a)) (by positivity) (by positivity)
    _ = ‖a‖ := by ring

lemma vectorPositive_star_mul (a : A) :
    vectorPositive π ξ (star a * a) = (‖π a ξ‖ ^ 2 : ℝ) := by
  change ⟪ξ, π (star a * a) ξ⟫_ℂ = _
  rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl
end Vector

section LimitRep
variable {ι A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]
variable (ω : Ultrafilter ι) (π : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))
  (ξ : ∀ i, H i) (hξ : ∀ i, ‖ξ i‖ ≤ 1)

def limitFunctional : A →ₚ[ℂ] ℂ :=
  ultraPositive ω (fun i => vectorPositive (π i) (ξ i))
    (fun i => vectorPositive_norm_le (π i) (ξ i) (hξ i))

abbrev LimitHilbert := (limitFunctional ω π ξ hξ).GNS

def limitRep : A →⋆ₐ[ℂ] (LimitHilbert ω π ξ hξ →L[ℂ] LimitHilbert ω π ξ hξ) :=
  (limitFunctional ω π ξ hξ).gnsStarAlgHom

lemma limitFunctional_tendsto (a : A) :
    Tendsto (fun i => vectorPositive (π i) (ξ i) a) (ω : Filter ι)
      (𝓝 (limitFunctional ω π ξ hξ a)) := tendsto_ultraPositive _ _ _ _

lemma limitRep_annihilates (a : A)
    (ha : Tendsto (fun i => ‖π i a‖) (ω : Filter ι) (𝓝 0)) :
    limitRep ω π ξ hξ a = 0 := by
  change (limitFunctional ω π ξ hξ).gnsNonUnitalStarAlgHom a = 0
  apply gns_zero_of_sandwich
  intro b
  apply ultraPositive_eq_zero_of_tendsto
  have hh : Tendsto (fun i => ‖π i (a * b) (ξ i)‖) (ω : Filter ι) (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
      (show Tendsto (fun i => ‖π i a‖ * ‖b‖) (ω : Filter ι) (𝓝 0) by
        simpa using ha.mul_const ‖b‖)
    have hmul : ‖π i (a * b)‖ ≤ ‖π i a‖ * ‖b‖ := by
      rw [map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le (π i) b) (norm_nonneg _))
    calc
      ‖π i (a * b) (ξ i)‖ ≤ ‖π i (a * b)‖ * ‖ξ i‖ := (π i (a * b)).le_opNorm _
      _ ≤ (‖π i a‖ * ‖b‖) * 1 := mul_le_mul hmul (hξ i) (norm_nonneg _) (by positivity)
      _ = ‖π i a‖ * ‖b‖ := mul_one _
  simpa only [vectorPositive_star_mul, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero]
    using (hh.pow 2).ofReal

lemma limitRep_nonzero (a : A) {δ : ℝ} (hδ : 0 < δ)
    (ha : ∀ᶠ i in (ω : Filter ι), δ ≤ ‖π i a (ξ i)‖) :
    limitRep ω π ξ hξ a ≠ 0 := by
  apply gnsStar_nonzero_of_value
  have hlim := (Complex.continuous_re.tendsto _).comp
    (limitFunctional_tendsto ω π ξ hξ (star a * a))
  have hle : δ ^ 2 ≤ (limitFunctional ω π ξ hξ (star a * a)).re := by
    apply ge_of_tendsto hlim
    filter_upwards [ha] with i hi
    simp only [Function.comp_apply, vectorPositive_star_mul, Complex.ofReal_re]
    exact pow_le_pow_left₀ hδ.le hi 2
  intro hf
  rw [hf, Complex.zero_re] at hle
  nlinarith [sq_pos_of_pos hδ]
end LimitRep
end MainGap

noncomputable section
open scoped Topology ComplexOrder InnerProductSpace
namespace MainGap

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : A)

def generatedRange : Submodule ℂ H :=
  (Submodule.span ℂ {x | ∃ a : A, ∃ y : H, x = π a (π v y)}).topologicalClosure

instance : CompleteSpace (generatedRange π v) := by
  unfold generatedRange
  infer_instance

lemma range_mem_generatedRange (y : H) : π v y ∈ generatedRange π v := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, y, by simp⟩

lemma generatedRange_invariant (a : A) :
    ∀ x ∈ generatedRange π v, π a x ∈ generatedRange π v := by
  change generatedRange π v ≤ (generatedRange π v).comap (π a).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro x ⟨b, y, rfl⟩
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨a * b, y, by simp⟩
  · exact (Submodule.isClosed_topologicalClosure _).preimage (π a).continuous

def rangeRestriction : A →⋆ₐ[ℂ] (generatedRange π v →L[ℂ] generatedRange π v) where
  toFun a := (π a).restrict (generatedRange_invariant π v a)
  map_one' := by ext x; simp [ContinuousLinearMap.restrict]
  map_mul' a b := by ext x; simp [ContinuousLinearMap.restrict]
  map_add' a b := by ext x; simp [ContinuousLinearMap.restrict]
  commutes' c := by ext x; simp [ContinuousLinearMap.restrict, Algebra.algebraMap_eq_smul_one]
  map_zero' := by ext x; simp [ContinuousLinearMap.restrict]
  map_star' a := by
    change (π (star a)).restrict (generatedRange_invariant π v (star a)) =
      ContinuousLinearMap.adjoint ((π a).restrict (generatedRange_invariant π v a))
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    change ⟪π (star a) (x : H), (y : H)⟫_ℂ = ⟪(x : H), π a (y : H)⟫_ℂ
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

@[simp]
lemma rangeRestriction_apply (a : A) (x : generatedRange π v) :
    ((rangeRestriction π v a x : generatedRange π v) : H) = π a (x : H) := rfl

lemma rangeRestriction_kills (u : A) (hu : ∀ a : A, π u * π a * π v = 0) :
    rangeRestriction π v u = 0 := by
  have hle : generatedRange π v ≤ (π u).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨a, y, rfl⟩
      change π u (π a (π v y)) = 0
      have := congrArg (fun T : H →L[ℂ] H => T y) (hu a)
      simpa using this
    · exact (π u).isClosed_ker
  ext x
  exact hle x.property

lemma rangeRestriction_nonzero (hv : IsSelfAdjoint v) (hne : π v ≠ 0) :
    rangeRestriction π v v ≠ 0 := by
  intro h
  apply hne
  apply (CStarRing.star_mul_self_eq_zero_iff (π v)).mp
  have hv' : IsSelfAdjoint (π v) := hv.map π
  rw [hv'.star_eq]
  ext y
  have hy := congrArg (fun T : generatedRange π v →L[ℂ] generatedRange π v =>
    T ⟨π v y, range_mem_generatedRange π v y⟩) h
  have := congrArg (fun x : generatedRange π v => (x : H)) hy
  simpa using this

end MainGap

end
end

end OAI
