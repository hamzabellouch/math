import Mathlib
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem tsupport_coordinateLaplacian_subset (φ : Position → ℝ) :
    tsupport (coordinateLaplacian φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

theorem local_harmonic_part {F σ ρ : Position → ℝ} {U : Set Position} {A : ℝ}
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hpoisson : HasWeakLaplacian F U (fun x => 4*Real.pi*σ x))
    (hρ : Integrable ρ) (hρpos : ∀ x, 0 ≤ ρ x) (hρbd : ∀ x, ρ x ≤ A)
    (he : Set.EqOn σ ρ U) :
    HasWeakLaplacian (fun x => F x+potentialOf ρ x) U (fun _ => 0) := by
  intro φ hφ hφc hφU
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hiF : Integrable (fun x => F x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx =>
      hU.continuousOn_iff.mp hF (hφU (tsupport_coordinateLaplacian_subset φ hx)))
      (continuous_coordinateLaplacian hφ2) (hasCompactSupport_coordinateLaplacian hφc)
  have hiP : Integrable (fun x => potentialOf ρ x*coordinateLaplacian φ x) :=
    ((potentialOf_continuous hρ hρpos hρbd).mul (continuous_coordinateLaplacian hφ2)).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateLaplacian hφc).mul_left
  have heq : (fun x => (F x+potentialOf ρ x)*coordinateLaplacian φ x) =
      fun x => F x*coordinateLaplacian φ x+potentialOf ρ x*coordinateLaplacian φ x := by
    ext x
    ring
  have hrho : (fun x => -(4*Real.pi)*ρ x*φ x) = fun x => -(4*Real.pi*σ x*φ x) := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · rw [he (hφU hx)]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, neg_zero]
  rw [heq, integral_add hiF hiP, hpoisson φ hφ hφc hφU,
    potentialOf_weakLaplacian hρ φ hφ hφc (Set.subset_univ _), hrho, integral_neg]
  simp only [add_neg_cancel, zero_mul, integral_zero]

theorem coordinateLaplacian_comp_smul (f : Position → ℝ) (D : ℝ) (x : Position) :
    coordinateLaplacian (fun y => f (D • y)) x = D^2*coordinateLaplacian f (D • x) := by
  unfold coordinateLaplacian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun t : ℝ => f (D • (x+t • axis a))) =
      (fun t : ℝ => (fun u : ℝ => f (D • x+u • axis a)) (D*t)) := by
    funext t
    simp only [smul_add, smul_smul]
  rw [he]
  have hed : (deriv fun t : ℝ => (fun u : ℝ => f (D • x+u • axis a)) (D*t)) =
      (fun t : ℝ => D * deriv (fun u : ℝ => f (D • x+u • axis a)) (D*t)) := by
    funext t
    exact deriv_comp_mul_left D (fun u : ℝ => f (D • x+u • axis a)) t
  rw [hed, deriv_const_mul_field, deriv_comp_mul_left]
  simp only [smul_eq_mul, mul_zero]
  ring

theorem HasWeakLaplacian.dilate {F q : Position → ℝ} {U : Set Position}
    {D : ℝ} (hD : 0 < D) (hw : HasWeakLaplacian F U q) :
    HasWeakLaplacian (fun x => D^4*F (D • x)) ((fun x => D • x) ⁻¹' U)
      (fun x => D^6*q (D • x)) := by
  intro φ hφ hc ht
  let e : Position ≃ₜ Position := Homeomorph.smul (Units.mk0 D⁻¹ (inv_ne_zero hD.ne'))
  let ψ : Position → ℝ := fun x => φ (D⁻¹ • x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.const_smul D⁻¹)
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e
  have hψt : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : e x ∈ tsupport φ := by
      simpa only [ψ, show (fun x : Position => D⁻¹ • x) = e from rfl,
        ← Function.comp_def, tsupport_comp_eq_preimage, Set.mem_preimage] using hx
    have := ht hx'
    simpa only [Set.mem_preimage, e, Homeomorph.smul_apply, Units.smul_def,
      Units.val_mk0, smul_smul, mul_inv_cancel₀ hD.ne', one_smul] using this
  have hid (x : Position) : D⁻¹ • (D • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hLap (x : Position) : coordinateLaplacian ψ (D • x) =
      (D⁻¹)^2*coordinateLaplacian φ x := by
    change coordinateLaplacian (fun y => φ (D⁻¹ • y)) (D • x) = _
    rw [coordinateLaplacian_comp_smul, hid]
  have hleft := Measure.integral_comp_smul_of_nonneg volume
    (fun x => F x*coordinateLaplacian ψ x) D (hR := hD.le)
  have hright := Measure.integral_comp_smul_of_nonneg volume
    (fun x => q x*ψ x) D (hR := hD.le)
  simp only [Position, finrank_euclideanSpace_fin, smul_eq_mul] at hleft hright
  simp_rw [hLap, show ∀ x, F (D • x)*((D⁻¹)^2*coordinateLaplacian φ x) =
    (D⁻¹)^2*(F (D • x)*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul] at hleft
  simp only [ψ, hid] at hright
  have hwe := hw ψ hψ hψc hψt
  have hEq : (∫ x, F (D • x)*coordinateLaplacian φ x) = D^2*(∫ x, q (D • x)*φ x) := by
    rw [hwe, ← hright] at hleft
    field_simp [hD.ne'] at hleft
    nlinarith [hleft]
  simp_rw [mul_assoc, integral_const_mul]
  rw [hEq]
  ring

end NeutralAtom
end

end
end

end OAI
