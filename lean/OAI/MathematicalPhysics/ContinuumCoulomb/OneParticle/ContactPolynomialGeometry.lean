import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCalibratedGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SlowLogarithmicExtent

namespace OAI

/-! The fixed source spacing and rational precision imply precisely the
separation and spatial growth used by the continuum comparison. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator

theorem precision_ge_7200 {N h : ℕ} (hN : 2 ≤ N) (hh : 13 ≤ h) : 7200 ≤ N^h := by
  calc
    7200 ≤ 2^13 := by norm_num
    _ ≤ N^13 := Nat.pow_le_pow_left hN 13
    _ ≤ N^h := Nat.pow_le_pow_right (by omega) hh

theorem planar_norm_le_two (x : ContactPoint) {C : ℝ} (hC : 0 ≤ C)
    (hx : ∀ i, |x i| ≤ C) : ‖x‖ ≤ 2*C := by
  have hnorm : ‖x‖^2=(x 0)^2+(x 1)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
  have h0 := (sq_le_sq₀ (abs_nonneg (x 0)) hC).mpr (hx 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (x 1)) hC).mpr (hx 1)
  rw [sq_abs] at h0 h1
  nlinarith [norm_nonneg x,sq_nonneg C]

theorem polynomial_norm (d : SquareLatticeHeisenberg) {N k s P : ℕ}
    (hN : 2 ≤ N) (hk : 1100 ≤ k) {q : ℚ} (hq : 0 < q)
    (hqhi : (q:ℝ) ≤ 31*(k:ℝ)*Real.log N) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    (hcoord : ∀ j i, |(contactGridAxis (d.coordinate j) i:ℝ)| ≤ (N:ℝ)^s)
    (x : GlobalSite d) : ‖point d P q ℓ x‖ ≤ (N:ℝ)^(k/100+s+13) := by
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ (q:ℝ)*(17*(N:ℝ)^s+17) := by positivity
  calc
    _ ≤ 2*((q:ℝ)*(17*(N:ℝ)^s+17)) :=
      planar_norm_le_two _ hc (coordinate_bound d P hq ℓ hP hℓ hcoord x)
    _ ≤ 2*(31*(k:ℝ)*Real.log N)*(17*(N:ℝ)^s+17) := by
      have hm := mul_le_mul_of_nonneg_right hqhi (show 0 ≤ 17*(N:ℝ)^s+17 by positivity)
      nlinarith only [hm]
    _ ≤ _ := slow_logarithmic_extent k s hk hNR

theorem spacing_polynomial {N k s : ℕ} (hN : 2 ≤ N) (hk : 1100 ≤ k)
    {q : ℝ} (hqhi : q ≤ 31*(k:ℝ)*Real.log N) : q ≤ (N:ℝ)^(k/100+s+13) := by
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := le_trans (by norm_num) hNR
  have hx : 0 ≤ 31*(k:ℝ)*Real.log N :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Real.log_nonneg hN1)
  have hs := one_le_pow₀ hN1 (n := s)
  have hm : 31*(k:ℝ)*Real.log N ≤ 2*(31*(k:ℝ)*Real.log N)*(17*(N:ℝ)^s+17) := by
    nlinarith [mul_nonneg hx (show 0 ≤ 34*(N:ℝ)^s+33 by positivity)]
  exact hqhi.trans (hm.trans (slow_logarithmic_extent k s hk hNR))

theorem polynomial_separation (d : SquareLatticeHeisenberg) (W G P N k : ℕ)
    (hN : 2 ≤ N) {q : ℚ} (hq : 0 < q)
    (hqlo : (59/2:ℝ)*(k:ℝ)*Real.log N ≤ q) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    (x y : GlobalSite d) (hxy : x ≠ y) :
    25*(k:ℝ)*Real.log N ≤ ‖point d P q ℓ x-point d P q ℓ y‖ := by
  have hs := separation d W G P hq ℓ hP hℓ x y hxy
  rw [dist_eq_norm] at hs
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  nlinarith

theorem polynomial_nonedge_separation (d : SquareLatticeHeisenberg) (W G P N k : ℕ)
    (hN : 2 ≤ N) {q : ℚ} (hq : 0 < q)
    (hqlo : (59/2:ℝ)*(k:ℝ)*Real.log N ≤ q) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ e, (ℓ e:ℝ) ∈ Set.Icc (1-contactLengthTolerance) (1+contactLengthTolerance))
    (x y : GlobalSite d) (hxy : x ≠ y) (hn : Nonedge d W G x y) :
    35*(k:ℝ)*Real.log N ≤ ‖point d P q ℓ x-point d P q ℓ y‖ := by
  have hs := nonedge_separation d W G P hq ℓ hP hℓ x y hxy hn
  rw [dist_eq_norm] at hs
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  nlinarith

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
