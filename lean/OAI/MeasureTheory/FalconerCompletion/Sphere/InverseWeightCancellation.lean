import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasureTransport2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
variable {n : ℕ}

lemma inverse_weight_cancellationND {D r s t : ℝ} (hD : 0 < D) (hr : 0 < r) (hs : 0 < s) :
    (D*s)^(-t)*(r*D)^t = (r/s)^t := by
  rw [Real.mul_rpow (le_of_lt hD) (le_of_lt hs),
    Real.mul_rpow (le_of_lt hr) (le_of_lt hD),Real.rpow_neg (le_of_lt hD),
    Real.rpow_neg (le_of_lt hs),Real.div_rpow (le_of_lt hr) (le_of_lt hs)]
  have hDt : D^t ≠ 0 := (Real.rpow_pos_of_pos hD t).ne'
  field_simp

lemma inverse_order_splitND {D r s : ℝ} (hs : s ≠ 0) (j : ℕ) :
    ((r*D:ℝ):ℂ)^(-(j:ℤ)) = ((r/s:ℝ):ℂ)^(-(j:ℤ))*((D*s:ℝ):ℂ)^(-(j:ℤ)) := by
  rw [← mul_zpow]
  congr 1
  norm_cast
  field_simp

lemma sphereAxisIntegralND_scaled_direction {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (r D : ℝ) (hD : D ≠ 0) (z : V) (b : V → ℂ) :
    sphereAxisIntegralND (r*D) (D⁻¹ • z) b = sphereAxisIntegralND r z b := by
  unfold sphereAxisIntegralND
  apply integral_congr_ae
  filter_upwards with w
  rw [inner_smul_right]
  push_cast
  congr 2
  field_simp [show (D:ℂ) ≠ 0 by exact_mod_cast hD]

theorem weighted_euclidean_inverseND (ψ : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (b : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
      (R A r s : ℝ) (x y : EuclideanSpace ℝ (Fin (n+1))),
      0 < dist x y → 0 < r → 0 < s → 1 ≤ R → 1 ≤ A →
      R^κ ≤ r*dist x y → A ≤ R^2 → A^2/(r*dist x y) ≤ R^(-κ) →
      ψ =ᶠ[𝓝 ((dist x y)⁻¹ • (x-y))] (fun _ => 1) →
      ψ =ᶠ[𝓝 (-((dist x y)⁻¹ • (x-y)))] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ‖(((dist x y*s)^(-(n:ℝ)/2):ℝ):ℂ) *
          (Complex.exp (Complex.I*(r*dist x y))*b.1 ((dist x y)⁻¹ • (x-y))) -
        (((r/s)^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (((r/s:ℝ):ℂ)^(-(j:ℤ)) *
            (((dist x y*s:ℝ):ℂ)^(-(j:ℤ))*
              sphereAxisIntegralND r (x-y) (fun w => ψ w*(euclideanSphereBND j b).1 w))))‖ ≤
        (dist x y*s)^(-(n:ℝ)/2)*E*R^(-T) := by
  obtain ⟨J,E,hE,hEb⟩ := euclidean_sphere_inverseND ψ hψ κ T C hκ hC
  refine ⟨J,E,hE,?_⟩
  intro b R A r s x y hD hr hs hR hA hΛ hup hratio hplus hminus hb
  have he : ‖(dist x y)⁻¹ • (x-y)‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hD,← dist_eq_norm,
      inv_mul_cancel₀ hD.ne']
  have hh := hEb b R A (r*dist x y) ((dist x y)⁻¹ • (x-y))
    hR hA hΛ hup hratio he hplus hminus hb
  have hW : 0 ≤ (dist x y*s)^(-(n:ℝ)/2) := Real.rpow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_left hh hW
  have hcancel : (dist x y*s)^(-(n:ℝ)/2)*(r*dist x y)^((n:ℝ)/2) = (r/s)^((n:ℝ)/2) := by
    simpa only [neg_div] using inverse_weight_cancellationND (t := (n:ℝ)/2) hD hr hs
  have hnormW : ‖(((dist x y*s)^(-(n:ℝ)/2):ℝ):ℂ)‖ = (dist x y*s)^(-(n:ℝ)/2) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hW]
  conv_lhs at hmul => rw [← hnormW,← norm_mul]
  have heq : (((dist x y*s)^(-(n:ℝ)/2):ℝ):ℂ) *
      (Complex.exp (Complex.I*(r*dist x y))*b.1 ((dist x y)⁻¹ • (x-y)) -
        (((r*dist x y)^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), ((r*dist x y:ℝ):ℂ)^(-(j:ℤ)) *
            sphereAxisIntegralND (r*dist x y) ((dist x y)⁻¹ • (x-y))
              (fun w => ψ w*(euclideanSphereBND j b).1 w))) =
      (((dist x y*s)^(-(n:ℝ)/2):ℝ):ℂ) *
        (Complex.exp (Complex.I*(r*dist x y))*b.1 ((dist x y)⁻¹ • (x-y))) -
        (((r/s)^((n:ℝ)/2):ℝ):ℂ) *
        (∑ j ∈ Finset.range (J+1), (((r/s:ℝ):ℂ)^(-(j:ℤ)) *
          (((dist x y*s:ℝ):ℂ)^(-(j:ℤ))*
            sphereAxisIntegralND r (x-y) (fun w => ψ w*(euclideanSphereBND j b).1 w)))) := by
    rw [mul_sub]
    congr 1
    rw [← mul_assoc,← Complex.ofReal_mul,hcancel]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [inverse_order_splitND hs.ne',sphereAxisIntegralND_scaled_direction r _ hD.ne']
    ring
  simp only [Complex.ofReal_mul] at heq hmul
  rw [heq] at hmul
  simpa only [mul_assoc,Complex.ofReal_mul] using hmul

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
