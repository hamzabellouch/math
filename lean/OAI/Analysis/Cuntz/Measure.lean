import OAI.Analysis.Cuntz.Commutative
import OAI.Analysis.Cuntz.Spectral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Layercake

namespace OAI

noncomputable section

/-! Real functional calculus and signed and complex spectral measures. -/

open scoped Matrix CStarAlgebra ComplexOrder
open Set MeasureTheory TopologicalSpace

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {X : Type*} [TopologicalSpace X]

/-- Real continuous functions viewed inside the complex function algebra. -/
def continuousRealInclusion : C(X, ℝ) →⋆ₐ[ℝ] C(X, ℂ) where
  toFun f := ⟨fun x => (f x : ℂ), by fun_prop⟩
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' f g := by ext x; simp
  map_mul' f g := by ext x; simp
  commutes' r := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' f := by ext x; simp

@[simp] theorem continuousRealInclusion_apply (f : C(X, ℝ)) (x : X) :
    continuousRealInclusion f x = (f x : ℂ) := rfl

variable [CompactSpace X]

local instance continuousMapRealFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ C(X, ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

theorem continuous_continuousRealInclusion : Continuous (continuousRealInclusion (X := X)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : C(X, ℝ) × X => (p.1 p.2 : ℂ))
  fun_prop

theorem continuousRealInclusion_cutoff (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    cuntzCutoff (continuousRealInclusion f) t =
      continuousRealInclusion (continuousDimensionCutoff f t) := by
  ext x
  have hsa : IsSelfAdjoint (continuousRealInclusion f) := (map_nonneg continuousRealInclusion hf).isSelfAdjoint
  have hsax : IsSelfAdjoint (continuousRealInclusion f x) := by
    change star (f x : ℂ) = (f x : ℂ)
    simp
  have h := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc
    (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f) (ha := hsa) (hφa := hsax)
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _ at h
  change (cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)) x = _
  rw [h]
  exact cfc_algebraMap (A := ℂ) (f x) (fun s : ℝ => max (s-t) 0)

variable {A : Type*} [CStarAlgebra A] {n : ℕ}

/-- The real function algebra mapped into the ambient finite matrix algebra. -/
def realFunctionHom (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) :
    C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A :=
  (ψ.restrictScalars ℝ).comp continuousRealInclusion

theorem realFunctionHom_continuous (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) :
    Continuous (realFunctionHom ψ) := by
  have hψ : Continuous ψ := by fun_prop
  exact hψ.comp continuous_continuousRealInclusion

/-- Genuine CFC naturality identifies the image of a scalar cutoff. -/
theorem realFunctionHom_cutoff (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    realFunctionHom ψ (continuousDimensionCutoff f t) = cuntzCutoff (realFunctionHom ψ f) t := by
  change ψ (continuousRealInclusion (continuousDimensionCutoff f t)) = _
  rw [← continuousRealInclusion_cutoff f hf t]
  exact ψ.map_cfc (fun s : ℝ => max (s-t) 0) (continuousRealInclusion f)
    (ha := (map_nonneg continuousRealInclusion hf).isSelfAdjoint)
    (hφa := (map_nonneg ψ (map_nonneg continuousRealInclusion hf)).isSelfAdjoint)

section Measures
variable [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
namespace CuntzDimensionState

/-- The single finite Borel measure associated with a commutative representation. -/
def spectralMeasure (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : Measure X :=
  (d.continuousDimension (realFunctionHom ψ)).measure

instance spectralMeasure_finite (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : IsFiniteMeasure (d.spectralMeasure ψ) :=
  inferInstanceAs (IsFiniteMeasure (d.continuousDimension (realFunctionHom ψ)).measure)

theorem spectralMeasure_lt (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    d.spectralMeasure ψ {x | t < f x} = ENNReal.ofReal
      (d.distribution ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ t) := by
  have he : {x | t < f x} = {x | 0 < continuousDimensionCutoff f t x} := by
    ext x
    simp only [continuousDimensionCutoff, ContinuousMap.coe_mk, lt_max_iff, lt_self_iff_false, or_false]
    exact (sub_pos : 0 < f x-t ↔ t < f x).symm
  rw [he]
  change (d.continuousDimension (realFunctionHom ψ)).measure _ = _
  rw [d.continuousDimension_measure_positive_support _ (realFunctionHom_continuous ψ)
    _ (continuousDimensionCutoff_nonneg f t)]
  congr 1
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm (realFunctionHom ψ (continuousDimensionCutoff f t)))
    (CStarMatrix.ofMatrix.symm (cuntzCutoff (realFunctionHom ψ f) t))
  rw [realFunctionHom_cutoff ψ f hf]
  exact .refl _

theorem spectralMeasure_real_lt (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) (t : ℝ) :
    (d.spectralMeasure ψ).real {x | t < f x} =
      d.distribution ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ t := by
  rw [measureReal_def, d.spectralMeasure_lt ψ f hf, ENNReal.toReal_ofReal (d.distribution_nonneg _ _)]

/-- The original finite spectral integral equals the integral against the
constructed measure. No new choice of positive functional is made. -/
theorem spectralValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ =
      ∫ x, f x ∂(d.spectralMeasure ψ) := by
  let p : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩
  have hi : Integrable f (d.spectralMeasure ψ) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [hi.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf)]
  simp_rw [d.spectralMeasure_real_lt ψ f hf]
  change d.spectralValue p = ∫ t in Ioi 0, d.distribution p t
  rw [spectralValue, intervalIntegral.integral_of_le (norm_nonneg _)]
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro t ht
  apply d.distribution_eq_zero
  have h : ¬t ≤ ‖CStarMatrix.ofMatrix p.matrix‖ := by
    intro hle
    exact ht.2 ⟨ht.1, hle⟩
  exact (lt_of_not_ge h).le

/-- Additivity of the EXISTING spectral value on positive functions in one
commutative representation, as a consequence of actual measure integration. -/
theorem spectralValue_realFunction_add (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f g : C(X, ℝ)) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ (f+g)), map_nonneg (realFunctionHom ψ) (add_nonneg hf hg)⟩ =
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ f), map_nonneg (realFunctionHom ψ) hf⟩ +
      d.spectralValue ⟨n, CStarMatrix.ofMatrix.symm (realFunctionHom ψ g), map_nonneg (realFunctionHom ψ) hg⟩ := by
  rw [d.spectralValue_eq_measure_integral ψ (f+g) (add_nonneg hf hg),
    d.spectralValue_eq_measure_integral ψ f hf, d.spectralValue_eq_measure_integral ψ g hg]
  exact integral_add
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
    (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))

end CuntzDimensionState
end Measures

omit [CompactSpace X] in
/-- All real-valued functions give self-adjoint elements, regardless of sign. -/
theorem continuousRealInclusion_selfAdjoint (f : C(X, ℝ)) :
    IsSelfAdjoint (continuousRealInclusion f) := by
  change star (continuousRealInclusion f) = continuousRealInclusion f
  ext x
  simp

theorem continuousRealInclusion_posPart (f : C(X, ℝ)) :
    (continuousRealInclusion f)⁺ = continuousRealInclusion (continuousDimensionCutoff f 0) := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc]
  ext x
  have hs := continuousRealInclusion_selfAdjoint f
  have hsx : IsSelfAdjoint (continuousRealInclusion f x) := by
    change star (f x : ℂ) = (f x : ℂ)
    simp
  have h := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc (fun s : ℝ => s⁺)
    (continuousRealInclusion f) (ha := hs) (hφa := hsx)
  change (cfc (fun s : ℝ => s⁺) (continuousRealInclusion f)) x = _
  change (cfc (fun s : ℝ => s⁺) (continuousRealInclusion f)) x = _ at h
  rw [h]
  have he := cfc_algebraMap (A := ℂ) (f x) (fun s : ℝ => s⁺)
  change cfc (fun s : ℝ => s⁺) (f x : ℂ) = ((max (f x-0) 0 : ℝ) : ℂ)
  rw [sub_zero]
  exact he


theorem realFunctionHom_selfAdjoint (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) : IsSelfAdjoint (realFunctionHom ψ f) :=
  (continuousRealInclusion_selfAdjoint f).map ψ

theorem realFunctionHom_posPart (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) :
    (realFunctionHom ψ f)⁺ = realFunctionHom ψ (continuousDimensionCutoff f 0) := by
  change (ψ (continuousRealInclusion f))⁺ = ψ (continuousRealInclusion (continuousDimensionCutoff f 0))
  rw [← continuousRealInclusion_posPart f]
  exact (ψ.toNonUnitalStarAlgHom.map_cfcₙ (fun s : ℝ => s⁺) (continuousRealInclusion f)
    (ha := continuousRealInclusion_selfAdjoint f) (hφa := realFunctionHom_selfAdjoint ψ f)).symm

theorem realFunctionHom_negPart (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A)
    (f : C(X, ℝ)) :
    (realFunctionHom ψ f)⁻ = realFunctionHom ψ (continuousDimensionCutoff (-f) 0) := by
  rw [← CFC.posPart_neg, ← map_neg, realFunctionHom_posPart]

omit [CompactSpace X] in
theorem continuousDimensionCutoff_sub (f : C(X, ℝ)) :
    continuousDimensionCutoff f 0 - continuousDimensionCutoff (-f) 0 = f := by
  ext x
  change max (f x-0) 0 - max (-f x-0) 0 = f x
  simp only [sub_zero]
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

section Measures
variable [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
namespace CuntzDimensionState

/-- The canonical signed extension agrees with the same measure on all real
continuous functions, including those of mixed sign. -/
theorem signedValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℝ)) :
    d.signedValue (realFunctionHom ψ f) = ∫ x, f x ∂(d.spectralMeasure ψ) := by
  unfold signedValue
  simp only [realFunctionHom_posPart, realFunctionHom_negPart, positiveValue]
  rw [d.spectralValue_eq_measure_integral ψ _ (continuousDimensionCutoff_nonneg f 0),
    d.spectralValue_eq_measure_integral ψ _ (continuousDimensionCutoff_nonneg (-f) 0)]
  rw [← integral_sub
    ((continuousDimensionCutoff f 0).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuousDimensionCutoff (-f) 0).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => congrArg (fun g : C(X, ℝ) => g x) (continuousDimensionCutoff_sub f))


/-- The globally fixed complex spectral value agrees with the same finite
measure on EVERY complex continuous function in the representation. -/
theorem complexValue_eq_measure_integral (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℂ)) :
    d.complexValue (ψ f) = ∫ x, f x ∂(d.spectralMeasure ψ) := by
  let fr : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
  let fi : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩
  have he : f = continuousRealInclusion fr + Complex.I • continuousRealInclusion fi := by
    ext x
    apply Complex.ext <;> simp [fr, fi]
  have hψ : ψ f = realFunctionHom ψ fr + Complex.I • realFunctionHom ψ fi := by
    conv_lhs => rw [he, map_add, map_smul]
    rfl
  rw [hψ, d.complexValue_real_imag _ _ (realFunctionHom_selfAdjoint ψ fr)
    (realFunctionHom_selfAdjoint ψ fi),
    d.complexValue_selfAdjoint (realFunctionHom_selfAdjoint ψ fr),
    d.complexValue_selfAdjoint (realFunctionHom_selfAdjoint ψ fi),
    d.signedValue_eq_measure_integral ψ fr, d.signedValue_eq_measure_integral ψ fi]
  have hi : Integrable f (d.spectralMeasure ψ) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [mul_comm Complex.I]
  exact integral_re_add_im hi

/-- Complex linearity for the original spectral value composed with a
commutative representation. Agreement is pointwise, ensuring overlap consistency. -/
def complexValueLinearMap (d : CuntzDimensionState A) {n : ℕ}
    (ψ : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := d.complexValue (ψ f)
  map_add' f g := by
    rw [d.complexValue_eq_measure_integral ψ (f+g),
      d.complexValue_eq_measure_integral ψ f, d.complexValue_eq_measure_integral ψ g]
    exact integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))
  map_smul' r f := by
    rw [d.complexValue_eq_measure_integral ψ (r • f), d.complexValue_eq_measure_integral ψ f]
    exact integral_smul r _

end CuntzDimensionState
end Measures
end Kaplansky

end

end OAI
