import Mathlib
import OAI.Analysis.Crouzeix.AngularTransport

namespace OAI

/-! Angular Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

lemma interiorBoundary_ne_zero (t : CircleSpace) : C.interiorBoundary R t ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [C.norm_interiorBoundary]; exact one_ne_zero)

lemma integral_angularJacobian_pow_succ (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n+1) ∂circleMeasure) = 0 := by
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain
    (R.analytic_f.deriv.differentiableOn.fun_mul (R.analytic_f.differentiableOn.pow n))
  convert hz using 1
  apply integral_congr_ae
  filter_upwards [] with t
  change (C.boundaryNormal t * deriv R.f (C.boundaryMap t) / C.interiorBoundary R t) *
    C.interiorBoundary R t ^ (n+1) = C.boundaryNormal t *
      (deriv R.f (C.boundaryMap t) * C.interiorBoundary R t ^ n)
  rw [pow_succ]
  field_simp [C.interiorBoundary_ne_zero R t]

lemma integral_angularJacobian (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.angularJacobian R t ∂circleMeasure) = 1 := by
  let a := R.h 0
  have haU : a ∈ U := R.h_zero_mem
  have ha : a ∈ R.domain := R.closure_subset_domain (subset_closure haU)
  have hfa : R.f a = 0 := R.f_h_zero
  let g := dslope R.f a
  have hg : AnalyticOnNhd ℂ g R.domain :=
    ((differentiableOn_dslope (R.isOpen_domain.mem_nhds ha)).mpr
      R.analytic_f.differentiableOn).analyticOnNhd R.isOpen_domain
  have hgn : ∀ z ∈ R.domain, g z ≠ 0 := by
    intro z hz
    by_cases he : z = a
    · subst z
      simpa only [g, dslope_same] using deriv_ne_zero_of_injOn R.isOpen_domain R.analytic_f.differentiableOn R.injective_f ha
    · dsimp only [g]
      rw [dslope_of_ne _ he, slope_def_module, hfa, sub_zero, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
        (fun hh => he (R.injective_f hz ha (hh.trans hfa.symm)))
  have hfgg : ∀ z, (z-a) * g z = R.f z := fun z => by
    simpa only [smul_eq_mul, hfa, sub_zero] using sub_smul_dslope R.f a z
  have hd : ∀ z ∈ R.domain, deriv R.f z = g z + (z-a) * deriv g z := by
    intro z hz
    have heq : (fun w => (w-a) * g w) = R.f := funext hfgg
    have ht := ((hasDerivAt_id z).sub_const a).mul (hg z hz).differentiableAt.hasDerivAt
    have hd := ht.deriv
    change deriv (fun w => (w-a) * g w) z = 1 * g z + (z-a) * deriv g z at hd
    simpa only [heq, one_mul] using hd
  let v : ℂ → ℂ := fun z => deriv g z / g z
  have hv : DifferentiableOn ℂ v R.domain := hg.deriv.differentiableOn.div
    hg.differentiableOn hgn
  have hz := C.physical_integral_zero hc R.isOpen_domain R.closure_subset_domain hv
  have hba (t : CircleSpace) : C.boundaryMap t ≠ a := fun he =>
    (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (he ▸ haU))
  have hbc (t : CircleSpace) : C.boundaryMap t ∈ R.domain :=
    R.closure_subset_domain (C.boundaryMap_mem_frontier t).1
  have heq (t : CircleSpace) : C.angularJacobian R t =
      C.boundaryNormal t / (C.boundaryMap t-a) + C.boundaryNormal t * v (C.boundaryMap t) := by
    change C.boundaryNormal t * deriv R.f (C.boundaryMap t) / R.f (C.boundaryMap t) = _
    rw [hd _ (hbc t), ← hfgg]
    dsimp only [v]
    field_simp [hgn _ (hbc t), sub_ne_zero.mpr (hba t)]
  have hi1 : Integrable (fun t => C.boundaryNormal t / (C.boundaryMap t-a)) circleMeasure :=
    (C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const)
      (fun t => sub_ne_zero.mpr (hba t))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun t => C.boundaryNormal t * v (C.boundaryMap t)) circleMeasure :=
    (C.boundaryNormal.continuous.mul (hv.continuousOn.comp_continuous
      C.boundaryMap.continuous hbc)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [heq]
  rw [integral_add hi1 hi2, hz, add_zero]
  have hh := C.boundaryContour_index_inside hU haU
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) = 1 at hh
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - a)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - a)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w-a)⁻¹)] at hh
  exact hh

lemma integral_angularJacobian_pow (hU : IsOpen U) (hc : Convex ℝ U) (n : ℕ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^n ∂circleMeasure) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp only [pow_zero, mul_one, ↓reduceIte]; exact C.integral_angularJacobian R hU hc
  | succ n => simpa only [Nat.succ_ne_zero, ↓reduceIte] using C.integral_angularJacobian_pow_succ R hc n

lemma conj_angularJacobian (t : CircleSpace) : conj (C.angularJacobian R t) = C.angularJacobian R t := by
  apply Complex.ext <;> simp [(C.angularJacobian_real_nonneg R t).1]

lemma integral_angularJacobian_zpow (hU : IsOpen U) (hc : Convex ℝ U) (j : ℤ) :
    (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^j ∂circleMeasure) =
      if j = 0 then 1 else 0 := by
  cases j with
  | ofNat n =>
    change (∫ t, C.angularJacobian R t * (C.interiorBoundary R t)^(n : ℤ) ∂circleMeasure) =
      if (n : ℤ) = 0 then 1 else 0
    simpa only [zpow_natCast, Nat.cast_eq_zero] using C.integral_angularJacobian_pow R hU hc n
  | negSucc n =>
    have he (t : CircleSpace) : C.angularJacobian R t * (C.interiorBoundary R t)^((Int.negSucc n)) =
        conj (C.angularJacobian R t * (C.interiorBoundary R t)^(n+1)) := by
      rw [zpow_negSucc, ← inv_pow, Complex.inv_eq_conj (C.norm_interiorBoundary R t),
        map_mul, C.conj_angularJacobian, map_pow]
    simp_rw [he]
    rw [integral_conj, C.integral_angularJacobian_pow_succ R hc, map_zero]
    simp

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
