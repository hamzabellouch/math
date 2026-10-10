import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularLeftBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFiniteOrder

namespace OAI

/-! Polynomial strip growth for the actual additive angular continuation,
derived from its functional equation and absolute initial series. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaAngularDirichletContinuation_polynomial_strip {q : Eisenstein}
    (hq : primary q) (x y : Eisenstein) (hxy : q∣9*x*y-1) (rev : Bool)
    {k : ℕ} (hk : 0<k) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0≤C ∧ ∀ s : ℂ, s.re∈Icc a b →
      ‖cubicThetaAngularDirichletContinuation q x y rev k s‖≤C*(1+|s.im|)^N := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1/2-a)
  let m := n+2
  let L : ℝ := 1/2-(m:ℝ)
  let R : ℝ := max (max a b) 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hLa : L<a := by dsimp [L,m]; push_cast; linarith
  have haR : a≤R := (le_max_left a b).trans (le_max_left _ _)
  have hbR : b≤R := (le_max_right a b).trans (le_max_left _ _)
  have hR2 : 2≤R := le_max_right _ _
  obtain ⟨C₀,hC₀,hleft⟩ := cubicThetaAngularDirichletContinuation_left_bound hq x y hxy rev hk hm
  let C₁ := 81*cubicThetaDirichletNormMass (2*R-1)
  have hC₁ : 0≤C₁ := mul_nonneg (by norm_num) (cubicThetaDirichletNormMass_nonneg _)
  let C := C₀+C₁
  have hC : 0≤C := add_nonneg hC₀ hC₁
  have hL : ∀ s : ℂ, s.re=L →
      ‖cubicThetaAngularDirichletContinuation q x y rev k s‖≤C*(1+|s.im|)^(4*m) := by
    intro s hs
    exact (hleft s hs).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hC₁) (by positivity))
  have hR : ∀ s : ℂ, s.re=R →
      ‖cubicThetaAngularDirichletContinuation q x y rev k s‖≤C*(1+|s.im|)^(4*m) := by
    intro s hs
    have H := cubicThetaAngularDirichletContinuation_right_bound hq x y hxy rev hk
      (σ := R) (by linarith) s hs
    calc
      _ ≤ C₁ := H
      _ ≤ C := le_add_of_nonneg_left hC₀
      _ ≤ _ := le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg s.im]))
  have H := polynomial_strip_of_finite_order (by linarith : L<R)
    (cubicThetaAngularDirichletContinuation_entire hq x y rev k)
    (cubicThetaAngularDirichletContinuation_finiteOrder hq x y rev k L R)
    hC (4*m) hL hR
  have hRL : 0 ≤ R-L+1 := by linarith
  refine ⟨C*2^(4*m)*(R-L+1)^(4*m),4*m,by positivity,?_⟩
  intro s hs
  exact H s ⟨hLa.le.trans hs.1,hs.2.trans hbR⟩

end CubicFirstMoment

end

end OAI
