import OAI.Analysis.CircleDomains.Sobolev.QuasiconformalSobolev

namespace OAI

/-! The actual conductivity equation implies bounded distortion. -/
open Set Function Filter MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem conductivity_frobenius_bound {k N aX aY vX vY : ℝ}
    (hk : 1 ≤ k) (hkN : k ≤ N) (hx : aX = k*vY) (hy : aY = -k*vX) :
    aX^2+aY^2+vX^2+vY^2 ≤ (N+1)*|aX*vY-aY*vX| := by
  have hS : 0 ≤ vX^2+vY^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hk0 : 0 ≤ k := by linarith
  have hc : k^2+1 ≤ (N+1)*k := by
    nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hkN)]
  rw [conductivity_jacobian hx hy, abs_of_nonneg (mul_nonneg hk0 hS), hx, hy]
  nlinarith [mul_le_mul_of_nonneg_right hc hS]

 theorem PlaneLocalWeakComplex.conductivity_boundedDistortion
    {φ : ℂ → ℂ} (D : PlaneLocalWeakComplex (fun x => φ (complexPlaneCoordinates x)))
    (F : Set EuclideanPlane) (n : ℕ) (hn : 1 ≤ n)
    (hsys : ∀ᵐ x ∂volume,
      D.realGradient x 0 = conductivityValue F n x * D.imagGradient x 1 ∧
      D.realGradient x 1 = -conductivityValue F n x * D.imagGradient x 0) :
    D.HasBoundedDistortion := by
  refine ⟨(n : ℝ)+1, by linarith [Nat.cast_nonneg (α := ℝ) n], ?_⟩
  filter_upwards [hsys] with x hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : 1 ≤ conductivityValue F n x := by
    classical
    simp only [conductivityValue]
    split <;> linarith
  have hkN : conductivityValue F n x ≤ n := by
    classical
    simp only [conductivityValue]
    split <;> linarith
  exact conductivity_frobenius_bound hk hkN hx.1 hx.2

end CircleDomainRigidity

end

end OAI
