import OAI.Analysis.Mahler.SphereFluxIntegral

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma normEnergy_twoForm_inner {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v,w] =
      -(inner ℝ v (I • w) : ℂ) := by
  rw [extDeriv_dc_normEnergy]
  have h : (∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re)) =
      -inner ℝ v (I • w) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [h, Complex.ofReal_neg]

lemma unitary_real_inner {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (v w : ComplexEuclidean n) :
    inner ℝ (L v) (L w) = inner ℝ v w := by
  let Lr : ComplexEuclidean n ≃ₗᵢ[ℝ] ComplexEuclidean n :=
    { L.toLinearEquiv.restrictScalars ℝ with norm_map' := L.norm_map }
  exact Lr.inner_map_map v w

lemma normEnergy_oneForm_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) :
    (oneForm (dcLinear (normEnergy n)) (L x)).toAlternatingMap.compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      (oneForm (dcLinear (normEnergy n)) x).toAlternatingMap := by
  ext v
  change dcLinear (normEnergy n) (L x) (L (v 0)) = dcLinear (normEnergy n) x (v 0)
  simp only [dcLinear_apply]
  rw [dc_normEnergy, dc_normEnergy, ← L.map_smul, unitary_real_inner]

lemma normEnergy_twoForm_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) (L x)).toAlternatingMap.compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap := by
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) = _
  have he : (fun i => L (![v 0,v 1] i)) = ![L (v 0), L (v 1)] := by
    ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) =
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v 0,v 1]
  rw [he, normEnergy_twoForm_inner, normEnergy_twoForm_inner, ← L.map_smul,
    unitary_real_inner]

/-- Unitary maps preserve the actual positive coordinate volume. The proof
uses the normalized symplectic top power, so no determinant sign is assumed. -/
theorem interleavedVolume_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) :
    (interleavedVolume n).compLinearMap (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      interleavedVolume n := by
  have h := congrArg (fun a => wedgePower a n) (normEnergy_twoForm_unitary L 0)
  rw [← wedgePower_compLinearMap, extDeriv_normEnergy_top, extDeriv_normEnergy_top] at h
  ext v
  have hv := congrArg (fun a => a v) h
  change (n.factorial : ℂ) * interleavedVolume n (fun i => L (v i)) =
    (n.factorial : ℂ) * interleavedVolume n v at hv
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n) hv

lemma normEnergy_boundary_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) (k : ℕ) :
    (wedge (oneForm (dcLinear (normEnergy n)) (L x)).toAlternatingMap
      (wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) (L x)).toAlternatingMap k)).compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
    wedge (oneForm (dcLinear (normEnergy n)) x).toAlternatingMap
      (wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap k) := by
  rw [wedge_compLinearMap, wedgePower_compLinearMap, normEnergy_oneForm_unitary,
    normEnergy_twoForm_unitary]

end Mahler

end OAI
