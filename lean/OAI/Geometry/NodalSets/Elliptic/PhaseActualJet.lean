import OAI.Geometry.NodalSets.Elliptic.SmoothJet
import OAI.Geometry.NodalSets.Waves.NormalFrameWaveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma reval_zero_homogeneous (p : CPoly) :
    reval p 0 = reval (homogeneousComponent 0 p) 0 := by
  simp [reval, constantCoeff_eq]

lemma retained_phase_value (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 0 p = initialPhaseJet s v H 0) : reval p 0 = (s:ℂ) := by
  rw [reval_zero_homogeneous, h]
  simp [initialPhaseJet, reval]

lemma retained_phase_first (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ)
    (h : homogeneousComponent 1 p = initialPhaseJet s v H 1) (i : Fin 4) :
    reval (pderiv i p) 0 = v i := by
  rw [reval_zero_homogeneous, homogeneousComponent_pderiv, show 0+1=1 from rfl, h,
    initialPhaseJet_first]
  simp [reval]

lemma retained_phase_second (p : CPoly) (s : ℝ) (v : Fin 4 → ℂ)
    (H : Fin 4 → Fin 4 → ℂ) (hH : ∀ i j, H i j = H j i)
    (h : homogeneousComponent 2 p = initialPhaseJet s v H 2) (i j : Fin 4) :
    reval (pderiv j (pderiv i p)) 0 = H i j := by
  rw [reval_zero_homogeneous, homogeneousComponent_pderiv, homogeneousComponent_pderiv]
  rw [show 0+1+1=2 from rfl, h]
  simp only [initialPhaseJet, show (2:ℕ) ≠ 0 by omega, show (2:ℕ) ≠ 1 by omega,
    ite_false, ite_true, pderiv_twice_quadraticPhase H hH]
  simp [reval]

lemma iteratedFDeriv_two_reval (p : CPoly) (x u v : Coord) :
    iteratedFDeriv ℝ 2 (reval p) x ![u,v] =
      ∑ i, ∑ j, reval (pderiv j (pderiv i p)) x * (v i:ℂ) * (u j:ℂ) := by
  have hd := (reval_contDiff p).contDiffAt.differentiableAt_iteratedFDeriv
    (m := 1) (by simp : (1:ℕ∞ω) < ∞) (x := x)
  rw [hd.iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, Fin.tail, Matrix.cons_val_succ]
  have he : (fun y ↦ fderiv ℝ (reval p) y v) =
      fun y ↦ ∑ i, reval (pderiv i p) y * (v i:ℂ) := by
    funext y
    exact fderiv_reval p y v
  rw [he, fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_mul_const]
    simp only [smul_apply, smul_eq_mul, fderiv_reval, Finset.mul_sum]
    simp [mul_comm, mul_left_comm]
    · exact (reval_contDiff _).differentiable (by simp) x
  · intro i _
    exact ((reval_contDiff _).mul contDiff_const).differentiable (by simp) x

theorem retained_normal_phase_derivatives (p : CPoly) (s a b : ℝ)
    (H : Fin 4 → Fin 4 → ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hH : ∀ i j, H i j = H j i)
    (hkeep : ∀ k, k ≤ 2 → homogeneousComponent k p =
      initialPhaseJet s (normalFrameVector a b) (normalComplexHessian a b H) k) :
    (reval p 0).re = s ∧
    (∀ x : Coord, (fderiv ℝ (reval p) 0 x).re = a*x 0) ∧
    ∀ x : Coord, (iteratedFDeriv ℝ 2 (reval p) 0 (fun _ ↦ x)).re =
      (∑ i, ∑ j, H i j * x i * x j) -
        Yau.contactEta a b (H 0 0) (H 1 1) * ∑ i, (x i)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [retained_phase_value p s _ _ (hkeep 0 (by omega))]
    rfl
  · intro x
    rw [fderiv_reval]
    simp_rw [retained_phase_first p s _ _ (hkeep 1 (by omega))]
    simp [normalFrameVector, Fin.sum_univ_succ]
  · intro x
    have hx : (fun _ : Fin 2 ↦ x) = ![x,x] := by ext i; fin_cases i <;> rfl
    rw [hx, iteratedFDeriv_two_reval]
    simp_rw [retained_phase_second p s _ _ (normalComplexHessian_symmetric ha hb H hH)
      (hkeep 2 (by omega))]
    change Complex.reCLM (∑ i, ∑ j, normalComplexHessian a b H i j * (x i:ℂ) * (x j:ℂ)) = _
    simp only [map_sum]
    change (∑ i, ∑ j, (normalComplexHessian a b H i j * (x i:ℂ) * (x j:ℂ)).re) = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    simp_rw [normalComplexHessian_real, sub_mul, ite_mul, zero_mul]
    simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc, pow_two]

end
end Yau.Jets

end OAI
