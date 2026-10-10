import OAI.Analysis.KadisonKastler.CompleteLinearOperations
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! # The limit of summably many completely bounded corrections -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Complete estimates on the successive differences produce an actual
continuous linear limit and the same complete estimate on its displacement. -/
theorem exists_complete_correction_limit
    (L : ℕ → A →L[ℂ] A) (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hsum : Summable c)
    (hstep : ∀ n, CompletelyBoundedBy
      ((L (n + 1)).toLinearMap - (L n).toLinearMap) (c n)) :
    ∃ T : A →L[ℂ] A, Tendsto L atTop (𝓝 T) ∧
      CompletelyBoundedBy (T.toLinearMap - (L 0).toLinearMap) (∑' n, c n) := by
  have hnorm (n : ℕ) : ‖L (n + 1) - L n‖ ≤ c n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (hc n)
    exact (hstep n).apply_norm_le
  have hdist : Summable (fun n => dist (L n) (L (n + 1))) := by
    apply hsum.of_nonneg_of_le (fun _ => dist_nonneg)
    intro n
    simpa only [dist_eq_norm, norm_sub_rev] using hnorm n
  obtain ⟨T, ht⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  refine ⟨T, ht, ?_⟩
  intro p q X
  let V (n : ℕ) := CStarMatrix.mapₗ (L n).toLinearMap X
  let W := CStarMatrix.mapₗ T.toLinearMap X
  have hV : Tendsto V atTop (𝓝 W) := by
    apply CStarMatrix.ofMatrixL.continuous.tendsto _ |>.comp
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (ContinuousLinearMap.apply ℂ A (X i j)).continuous.tendsto T |>.comp ht
  have hbound (n : ℕ) : dist (V n) (V (n + 1)) ≤ c n * ‖X‖ := by
    have h := hstep n p q X
    rw [matrix_map_sub, norm_sub_rev] at h
    simpa only [dist_eq_norm, V] using h
  have hsumX : Summable (fun n => c n * ‖X‖) := hsum.mul_right ‖X‖
  have h := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun n => c n * ‖X‖) hbound hsumX hV
  rw [matrix_map_sub, norm_sub_rev]
  simpa only [dist_eq_norm, V, W, tsum_mul_right] using h

/-- Summably small corrections which asymptotically intertwine a product
converge to an exact invertible star-preserving intertwiner. -/
theorem correction_of_summable_steps
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (L : ℕ → A →L[ℂ] A)
    (hzero : L 0 = ContinuousLinearMap.id ℂ A) (c d : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hsum : Summable c) (hsmall : (∑' n, c n) < 1)
    (hstep : ∀ n, CompletelyBoundedBy
      ((L (n + 1)).toLinearMap - (L n).toLinearMap) (c n))
    (hstar : ∀ n x, L n (star x) = star (L n x))
    (hd : Tendsto d atTop (𝓝 0))
    (hm : ∀ n x y, ‖L n (m x y) - L n x * L n y‖ ≤ d n * ‖x‖ * ‖y‖) :
    ∃ T : A ≃ₗ[ℂ] A,
      (∀ x y, T (m x y) = T x * T y) ∧
      (∀ x, T (star x) = star (T x)) ∧
      CompletelyBoundedBy (T.toLinearMap - LinearMap.id) (∑' n, c n) := by
  obtain ⟨F, hF, hcb⟩ := exists_complete_correction_limit L c hc hsum hstep
  have hclose : CompletelyBoundedBy (F.toLinearMap - LinearMap.id) (∑' n, c n) := by
    simpa only [hzero, ContinuousLinearMap.coe_id] using hcb
  have hsum0 : 0 ≤ ∑' n, c n := tsum_nonneg hc
  obtain ⟨T, hT⟩ := hclose.exists_equiv_add_id hsum0 hsmall
  have hTF : T.toLinearMap = F.toLinearMap := by rw [hT]; abel
  have ht (x : A) : Tendsto (fun n => L n x) atTop (𝓝 (F x)) :=
    (ContinuousLinearMap.apply ℂ A x).continuous.tendsto F |>.comp hF
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x y
    have hres := (ht (m x y)).sub ((ht x).mul (ht y))
    have hz : Tendsto (fun n => ‖L n (m x y) - L n x * L n y‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hm n x y)
      simpa only [zero_mul] using (hd.mul_const ‖x‖).mul_const ‖y‖
    have heq : F (m x y) - F x * F y = 0 := norm_eq_zero.mp
      (tendsto_nhds_unique hres.norm hz)
    change T.toLinearMap (m x y) = T.toLinearMap x * T.toLinearMap y
    rw [hTF]
    exact sub_eq_zero.mp heq
  · intro x
    have h : F (star x) = star (F x) := by
      apply tendsto_nhds_unique (ht (star x))
      simpa only [hstar] using (ht x).star
    have happ (z : A) : T z = F z := congrArg (fun R : A →ₗ[ℂ] A => R z) hTF
    rw [happ, happ]
    exact h
  · simpa only [hTF] using hclose

end

end KadisonKastler

end OAI
