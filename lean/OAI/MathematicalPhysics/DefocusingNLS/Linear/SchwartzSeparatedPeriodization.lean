import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPhysicalSampling

namespace OAI

/-! # Disjointness of sufficiently separated compactly supported translates -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem norm_tsum_sq_of_atMostOne {ι : Type*} (v : ι → ℂ)
    (hv : ∀ i j, v i ≠ 0 → v j ≠ 0 → i = j) :
    ‖∑' i, v i‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  classical
  by_cases h : ∃ i, v i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz (j : ι) (hj : j ≠ i) : v j = 0 := by
      by_contra hji
      exact hj (hv j i hji hi)
    rw [tsum_eq_single i hz, tsum_eq_single i (fun j hj => by rw [hz j hj]; simp)]
  · have hz : ∀ i, v i = 0 := by simpa only [not_exists, not_not] using h
    simp only [hz, tsum_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

theorem separatedSchwartz_atMostOne (D R : ℝ) (hD : 0 < D) (hDR : 2 * R < D)
    (K : 𝓢(E, ℂ)) (hK : ∀ x : E, R < ‖x‖ → K x = 0) (x : E)
    (m n : frequencyLattice) (hm : K (x + D • (m : E)) ≠ 0)
    (hn : K (x + D • (n : E)) ≠ 0) : m = n := by
  by_contra hmn
  have hmR : ‖x + D • (m : E)‖ ≤ R := le_of_not_gt (fun h => hm (hK _ h))
  have hnR : ‖x + D • (n : E)‖ ≤ R := le_of_not_gt (fun h => hn (hK _ h))
  have hp : 1 ≤ ‖m - n‖ := one_le_norm_frequencyLattice (sub_ne_zero.mpr hmn)
  have hid : D • ((m - n : frequencyLattice) : E) =
      (x + D • (m : E)) - (x + D • (n : E)) := by
    simp only [Submodule.coe_sub, smul_sub]
    abel
  have hb := norm_sub_le (x + D • (m : E)) (x + D • (n : E))
  rw [← hid, norm_smul, Real.norm_eq_abs, abs_of_pos hD, Submodule.norm_coe] at hb
  nlinarith

theorem separatedSchwartz_norm_tsum_sq (D R : ℝ) (hD : 0 < D) (hDR : 2 * R < D)
    (K : 𝓢(E, ℂ)) (hK : ∀ x : E, R < ‖x‖ → K x = 0) (x : E) :
    ‖∑' n : frequencyLattice, K (x + D • (n : E))‖ ^ 2 =
      ∑' n : frequencyLattice, ‖K (x + D • (n : E))‖ ^ 2 :=
  norm_tsum_sq_of_atMostOne _ (separatedSchwartz_atMostOne D R hD hDR K hK x)

end DefocusingNLS

end OAI
