import OAI.Combinatorics.BalancedRyser.Local.LocalFailureSummation
import OAI.Combinatorics.BalancedRyser.Local.LocalSummationArithmetic

namespace OAI

namespace Balanced.Local
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators Topology
universe u

theorem pencilLocal_of_reuse_and_size_bounds
    (hReuse : PencilReuseResult.{u})
    (hSmall : ∀ K : ℝ, 0 < K → ∃ a : ℕ, ∃ A L : ℝ,
      0 ≤ A ∧ 0 ≤ L ∧ ∃ q₀ : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
          KernelConditions Q w K → ∀ (p : Point F) (b κ : ℕ),
            3 ≤ b → b ≤ logBudget F → κ ≤ 2 →
            selectedProbability w (fun C => C.splitMultiplicity p = b ∧
              reuseCount C p = κ ∧ BadLocalCoverAt b p C) ≤
              L * (((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
                ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))) :
    PencilLocalResult.{u} := by
  intro K hK
  obtain ⟨C, hC, qR, hR⟩ := hReuse K hK
  obtain ⟨a, A, L, hA, hL, qS, hS⟩ := hSmall K hK
  obtain ⟨εL, hεL, hεL0, hlarge⟩ := large_pencil_uniform_error K hK.le
  let εS : ℕ → ℝ := fun q => (q : ℝ) ^ 2 *
    ∑ b ∈ Finset.Icc 3 (Nat.ceil (Real.log (q : ℝ))),
      ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
        ((Nat.ceil (Real.log (q : ℝ)) : ℝ) ^ 3 / (q : ℝ) ^ 3)
  have hεS : Tendsto εS atTop (𝓝 0) :=
    LocalAsymptotics.tendsto_plane_weighted_pencil_sum a A hA
      (fun q => Finset.Icc 3 (Nat.ceil (Real.log (q : ℝ))))
  have hinv : Tendsto (fun q : ℕ => C / (q : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  refine ⟨fun q => εL q + C / (q : ℝ) + 3 * L * εS q, ?_, ?_, max qR qS, ?_⟩
  · simpa using (hεL.add hinv).add (hεS.const_mul (3 * L))
  · intro q
    have hs : 0 ≤ εS q := by dsimp [εS]; positivity
    exact add_nonneg (add_nonneg (hεL0 q) (by positivity)) (by positivity)
  · intro F _ _ _ hq Q w hw
    have hR' := hR F ((le_max_left _ _).trans hq) Q w hw
    have hS' := hS F ((le_max_right _ _).trans hq) Q w hw
    have hlarge' : selectedProbability w LargePencilEvent ≤ εL (Fintype.card F) := by
      refine (KernelBridge.selectedProbability_mono w hw.1 ?_).trans (hlarge F Q w hw)
      intro X hX
      obtain ⟨p, hp⟩ := hX
      exact ⟨p, hp.le⟩
    have hhigh := high_reuse_probability_le w hw.1 C hR'
    have hsmall : selectedProbability w SmallBadLocalEvent ≤
        3 * L * εS (Fintype.card F) := by
      apply small_bad_local_probability_le_envelope w hw.1 L
        (fun b => ((b : ℝ) ^ a * A ^ b / (b.factorial : ℝ)) *
          ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))
      intro p b hb κ hk
      exact hS' p b κ (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
        (by have := Finset.mem_range.mp hk; omega)
    have hcases := selectedProbability_le_three_of_positive_imp w hw.1
      (fun X => ¬ X.LocalCondition) LargePencilEvent HighReuseEvent SmallBadLocalEvent
      (fun _ _ _ hbad => local_failure_cases _ hbad)
    exact hcases.trans (add_le_add (add_le_add hlarge' hhigh) hsmall)

theorem pencilLocal_of_three_reuse_estimates
    (hReuse : PencilReuseResult.{u}) (hSmall : PencilSmallReuseResult.{u})
    (hTwo : PencilTwoReusesResult.{u}) : PencilLocalResult.{u} := by
  apply pencilLocal_of_reuse_and_size_bounds hReuse
  intro K hK
  obtain ⟨hnorm, C, hC, d, qS, hS⟩ := hSmall
  obtain ⟨D, hD, qT, hT⟩ := hTwo
  refine ⟨d + 7, 1024 * K, 2048 * C + 256 * D,
    by positivity, by positivity, max qS qT, ?_⟩
  intro F _ _ _ hq Q w hw p b κ hb hB hk
  have hqR : (0 : ℝ) < Fintype.card F := by positivity
  have hBR : (1 : ℝ) ≤ logBudget F := by
    exact_mod_cast (show 1 ≤ logBudget F by omega)
  let W : ℝ := (((b : ℝ) ^ (d + 7) * (1024 * K) ^ b / (b.factorial : ℝ)) *
    ((logBudget F : ℝ) ^ 3 / (Fintype.card F : ℝ) ^ 3))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  by_cases hk2 : κ = 2
  · subst κ
    have hraw := bad_pencil_probability_le_common_factor Q w K hK.le hw p
      (by omega : 2 ≤ b) (by omega : 2 ≤ 2)
      (D * (b : ℝ) ^ 3 / Fintype.card F) (by positivity) (by
        intro P bits
        exact hT F ((le_max_right _ _).trans hq) b hb hB P bits p)
    have harith := two_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
      D (1024 * K) b (d + 7) hqR hBR (by omega) hD.le (by positivity) (by omega)
    refine hraw.trans (harith.trans ?_)
    change (256 * D) * W ≤ (2048 * C + 256 * D) * W
    exact mul_le_mul_of_nonneg_right (by linarith) hW
  · have hk1 : κ ≤ 1 := by omega
    have hraw := bad_pencil_probability_le_of_conditioned Q w K hK.le hw p
      (by omega : 2 ≤ b) hk
      (C * (b : ℝ) ^ d * (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ))
      (by positivity)
      (fun P a ha bits => hnorm F b κ hb hB hk P a ha bits p)
      (fun P a ha bits => hS F ((le_max_left _ _).trans hq) b κ hb hB hk1 P a ha bits p)
    have harith := small_reuse_envelope_le (Fintype.card F : ℝ) (logBudget F : ℝ)
      C (1024 * K) b d (d + 7) κ hqR hBR (by omega) hC.le (by positivity)
      (by omega) (by omega)
    refine hraw.trans (harith.trans ?_)
    change (2048 * C) * W ≤ (2048 * C + 256 * D) * W
    exact mul_le_mul_of_nonneg_right (by linarith) hW

end
end Balanced.Local

end OAI
