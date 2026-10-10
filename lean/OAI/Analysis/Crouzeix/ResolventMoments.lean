import Mathlib
import OAI.Analysis.Crouzeix.PhysicalCalculus

namespace OAI

/-! Resolvent Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma contourEval_circleIntegral (A : Operator H) {V : Set ℂ}
    (Γ : CalculusContour (numericalClosure A) V) (f : CircleSpace → ℂ → ℂ)
    (hf : ContinuousOn (fun p : ℝ × CircleSpace => f p.2 (Γ.path p.1)) (Icc 0 1 ×ˢ univ)) :
    contourEval A Γ.toSmoothContour (fun z => ∫ t, f t z ∂circleMeasure) =
      ∫ t, contourEval A Γ.toSmoothContour (f t) ∂circleMeasure := by
  let k (s : ℝ) (t : CircleSpace) := f t (Γ.path s) • contourKernel A Γ.toSmoothContour s
  have hc : ContinuousOn (uncurry k) (Icc 0 1 ×ˢ univ) :=
    hf.smul ((continuousOn_contourKernel A Γ).comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hi := (hc.integrableOn_compact (μ := volume.prod circleMeasure)
    (isCompact_Icc.prod isCompact_univ)).mono_set (prod_mono Ioc_subset_Icc_self (Subset.refl univ))
  have hi' : Integrable (uncurry k) ((volume.restrict (uIoc 0 1)).prod circleMeasure) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ,
      uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hi
  simp only [contourEval_eq_kernel]
  simp_rw [← integral_smul_const]
  rw [intervalIntegral_integral_swap hi', integral_smul]

lemma ringInverse_neg {R : Type*} [Ring R] (a : R) : Ring.inverse (-a) = -Ring.inverse a := by
  rw [← neg_one_mul a, Ring.inverse_mul (Or.inl isUnit_one.neg)]
  have h : Ring.inverse (-1 : R) = (-1 : R) := by
    rw [show (-1 : R) = ((-1 : Rˣ) : R) from rfl, Ring.inverse_unit]
    simp
  rw [h, mul_neg_one]

lemma contourEval_sub_inv (A : Operator H) {V : Set ℂ}
    (Γ : CalculusContour (numericalClosure A) V) {a : ℂ} (ha : a ∉ V) :
    contourEval A Γ.toSmoothContour (fun z => (a - z)⁻¹) =
      Ring.inverse (algebraMap ℂ (Operator H) a - A) := by
  have hfun : (fun z : ℂ => (a-z)⁻¹) = (fun z => (-1 : ℂ) * (z-a)⁻¹) := by
    ext z
    rw [← neg_sub z a, inv_neg, neg_one_mul]
  rw [hfun, contourEval_const_mul, contourEval_inv_sub A Γ ha, neg_one_smul,
    ← ringInverse_neg, neg_sub]

end

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma boundaryMap_not_mem (hU : IsOpen U) (t : CircleSpace) : C.boundaryMap t ∉ U :=
  fun ht => (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ ht)

lemma boundary_difference_ne_zero (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (t : CircleSpace) :
    C.boundaryMap t - z ≠ 0 := fun he => C.boundaryMap_not_mem hU t (sub_eq_zero.mp he ▸ hz)

def operatorResolvent (A : Operator H) (hKU : numericalClosure A ⊆ U) (hU : IsOpen U) :
    C(CircleSpace, Operator H) :=
  ⟨fun t => C.boundaryNormal t • Ring.inverse (algebraMap ℂ (Operator H) (C.boundaryMap t) - A),
    C.boundaryNormal.continuous.smul ((continuousOn_resolvent A).comp_continuous C.boundaryMap.continuous
      (fun t ht => C.boundaryMap_not_mem hU t (hKU ht)))⟩

lemma operatorResolvent_add_star_nonneg (A : Operator H) (hKU : numericalClosure A ⊆ U)
    (hU : IsOpen U) (hc : Convex ℝ U) (t : CircleSpace) :
    0 ≤ C.operatorResolvent A hKU hU t + star (C.operatorResolvent A hKU hU t) := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply isPositive_original_resolvent_of_not_mem
  · exact fun ht => C.boundaryMap_not_mem hU t (hKU ht)
  · intro w hw
    exact C.supporting_normal hc (norm_circleCoordinate t) (subset_closure (hKU (subset_closure hw)))

variable [Nontrivial H]

lemma integral_operatorResolvent_moment (A : Operator H) (hKU : numericalClosure A ⊆ U)
    (hU : IsOpen U) (j : ℤ) :
    (∫ t, (circleCoordinate t)^j • C.operatorResolvent A hKU hU t ∂circleMeasure) =
      holomorphicEval A C.outerDomain (C.physicalCoefficient j) := by
  obtain ⟨Γ⟩ := exists_calculusContour (isCompact_numericalClosure A)
    (convex_numericalClosure A) (numericalClosure_nonempty A) hU hKU
  have hsub : U ⊆ C.outerDomain := subset_closure.trans C.closure_subset_outerDomain
  rw [← holomorphicEval_restrict A hU C.isOpen_outerDomain hKU hsub
    (C.differentiableOn_physicalCoefficient j), holomorphicEval_eq_contourEval A hU
      ((C.differentiableOn_physicalCoefficient j).mono hsub) Γ]
  have he : contourEval A Γ.toSmoothContour (C.physicalCoefficient j) =
      contourEval A Γ.toSmoothContour (fun z => ∫ t, (circleCoordinate t)^j *
        (C.boundaryNormal t / (C.boundaryMap t-z)) ∂circleMeasure) := by
    apply contourEval_congr
    rintro z ⟨s,hs,rfl⟩
    exact C.physicalCoefficient_inside hU j (Γ.avoids s hs).1
  rw [he]
  have hcont : ContinuousOn (fun p : ℝ × CircleSpace => (circleCoordinate p.2)^j *
      (C.boundaryNormal p.2 / (C.boundaryMap p.2 - Γ.path p.1))) (Icc 0 1 ×ˢ univ) := by
    exact ((circleCoordinate.continuous.zpow₀ j (fun t => Or.inl (circleCoordinate_ne_zero t))).comp continuous_snd).continuousOn.mul
      ((C.boundaryNormal.continuous.comp continuous_snd).continuousOn.div
        ((C.boundaryMap.continuous.comp continuous_snd).sub (Γ.smooth.continuous.comp continuous_fst)).continuousOn
        (fun p hp => C.boundary_difference_ne_zero hU (Γ.avoids p.1 hp.1).1 p.2))
  rw [contourEval_circleIntegral A Γ _ hcont]
  apply integral_congr_ae
  filter_upwards [] with t
  have heq : (fun z => (circleCoordinate t)^j * (C.boundaryNormal t / (C.boundaryMap t-z))) =
      (fun z => ((circleCoordinate t)^j * C.boundaryNormal t) * (C.boundaryMap t-z)⁻¹) := by
    ext z; simp only [div_eq_mul_inv, mul_assoc]
  rw [heq, contourEval_const_mul, contourEval_sub_inv A Γ (C.boundaryMap_not_mem hU t), mul_smul]
  rfl

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
