import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampledNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSeparatedPeriodization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomial

namespace OAI

/-! # Exact sampling of products with separated compact physical supports -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem mul_tsum_of_separated_support {ι : Type*} (u v : ι → ℂ)
    (hu : ∀ i j, u i ≠ 0 → u j ≠ 0 → i = j)
    (huv : ∀ i j, u i ≠ 0 → v j ≠ 0 → i = j) :
    (∑' i, u i) * (∑' i, v i) = ∑' i, u i * v i := by
  classical
  by_cases hh : ∃ i, u i ≠ 0
  · obtain ⟨i, hi⟩ := hh
    have hzu (j : ι) (hj : j ≠ i) : u j = 0 := by
      by_contra h
      exact hj (hu j i h hi)
    have hzv (j : ι) (hj : j ≠ i) : v j = 0 := by
      by_contra h
      exact hj (huv i j hi h).symm
    rw [tsum_eq_single i hzu, tsum_eq_single i hzv,
      tsum_eq_single i (fun j hj => by rw [hzu j hj, zero_mul])]
  · have hz : ∀ i, u i = 0 := by simpa only [not_exists, not_not] using hh
    simp only [hz, tsum_zero, zero_mul]

theorem separatedSchwartz_cross (D R : ℝ) (hD : 0 < D) (hDR : 2 * R < D)
    (K J : 𝓢(E, ℂ)) (hK : ∀ x : E, R < ‖x‖ → K x = 0)
    (hJ : ∀ x : E, R < ‖x‖ → J x = 0) (x : E)
    (m n : frequencyLattice) (hm : K (x + D • (m : E)) ≠ 0)
    (hn : J (x + D • (n : E)) ≠ 0) : m = n := by
  by_contra hmn
  have hmR : ‖x + D • (m : E)‖ ≤ R := le_of_not_gt (fun h => hm (hK _ h))
  have hnR : ‖x + D • (n : E)‖ ≤ R := le_of_not_gt (fun h => hn (hJ _ h))
  have hp : 1 ≤ ‖m - n‖ := one_le_norm_frequencyLattice (sub_ne_zero.mpr hmn)
  have hid : D • ((m - n : frequencyLattice) : E) =
      (x + D • (m : E)) - (x + D • (n : E)) := by
    simp only [Submodule.coe_sub, smul_sub]
    abel
  have hb := norm_sub_le (x + D • (m : E)) (x + D • (n : E))
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_pos hD, Submodule.norm_coe] at hb
  nlinarith

theorem schwartzTorusSample_product (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hLR : 2 * R < 2 * Real.pi * L)
    (K J : 𝓢(E, ℂ)) (hK : ∀ x : E, R < ‖x‖ → K x = 0)
    (hJ : ∀ x : E, R < ‖x‖ → J x = 0) :
    expandingProduct a k L ha ha1 hk hL
      (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel K))
      (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel J)) =
      schwartzTorusSample a k L ha1 hk hL
        (radianFourierKernel (SchwartzMap.smulLeftCLM ℂ K J)) := by
  ext n
  rw [← weight_mul_expandingFourierCoefficient a k L hL _ n,
    ← weight_mul_expandingFourierCoefficient a k L hL _ n]
  congr 1
  apply expandingFourierCoefficient_eq_of_torus_eq a k L ha ha1 hk hL
  intro x
  have hp : 0 < L := by linarith
  have hx : L⁻¹ • (L • x) = x := by rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [← hx, expandingTorusFunction_product, ContinuousMap.mul_apply,
    schwartzTorusSample_physical a k L ha ha1 hk hL,
    schwartzTorusSample_physical a k L ha ha1 hk hL,
    schwartzTorusSample_physical a k L ha ha1 hk hL]
  simp only [SchwartzMap.smulLeftCLM_apply_apply K.hasTemperateGrowth, smul_eq_mul]
  exact mul_tsum_of_separated_support _ _
    (separatedSchwartz_atMostOne _ R (by positivity) hLR K hK _)
    (separatedSchwartz_cross _ R (by positivity) hLR K J hK hJ _)

theorem schwartzTorusSample_conjugate (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (K : 𝓢(E, ℂ)) :
    fourierConjugate (schwartzTorusSample a k L ha1 hk hL (radianFourierKernel K)) =
      schwartzTorusSample a k L ha1 hk hL (radianFourierKernel (schwartzPointConjugate K)) := by
  ext n
  rw [← weight_mul_expandingFourierCoefficient a k L hL _ n,
    ← weight_mul_expandingFourierCoefficient a k L hL _ n]
  congr 1
  apply expandingFourierCoefficient_eq_of_torus_eq a k L ha ha1 hk hL
  intro x
  have hp : 0 < L := by linarith
  have hx : L⁻¹ • (L • x) = x := by rw [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [← hx, expandingTorusFunction_conjugate a k L ha ha1 hk hL,
    schwartzTorusSample_physical a k L ha ha1 hk hL,
    schwartzTorusSample_physical a k L ha ha1 hk hL, Complex.conj_tsum]
  simp only [schwartzPointConjugate_apply]

end DefocusingNLS

end OAI
