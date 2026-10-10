import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordFinalDecision

namespace OAI

/-! # Time and space guarantees for the bounded randomized decision procedure

`main_resources` bounds the work and storage counters with fixed threshold
`T`. `space_corollary` absorbs the polynomial storage factor for every rate
above .199. All resource quantifiers range over every random-word outcome,
while the procedure and threshold are independent of the polynomial-bit exponent.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordMain

open Filter

private theorem double_time (a b c : ℝ) : 2*((a*2)*b*c) = (4*a)*b*c := by ring

theorem main_resources (T : DecisionThreshold) (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ I : Instance n, inputBits I ≤ n^c →
      ∀ words : WordFinalDecision.Words I,
        ((WordFinalDecision.run T I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((WordFinalDecision.run T I words).2 : ℝ) ≤
          2*(inputScale I : ℝ)^15*(2 : ℝ)^((199/1000 : ℝ)*n) := by
  filter_upwards [eventually_mainGuard T.value c hc,eventually_ge_atTop 2] with n hg hn
  intro I hI words
  have hm : mainGuard T.value n (inputScale I) = true := hg (inputBits I) hI
  have hb := WordFinalDecision.main_bounds T I hm words
  constructor
  · have hnat : ((WordFinalDecision.run T I words).1.2 : ℝ) ≤
        ((2*(inputScale I^624*2^((n+1)/2)) : ℕ) : ℝ) := Nat.cast_le.mpr hb.1
    rw [Nat.cast_mul,Nat.cast_ofNat] at hnat
    apply hnat.trans
    have h := mul_le_mul_of_nonneg_left (WordExecutionAsymptotics.time c hc n hn I hI)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [double_time] using h
  · have hnat : ((WordFinalDecision.run T I words).2 : ℝ) ≤
        ((2*writableWordLimit I : ℕ) : ℝ) := Nat.cast_le.mpr hb.2
    simp only [writableWordLimit,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hnat
    rw [←mul_assoc] at hnat
    exact hnat.trans (mul_le_mul_of_nonneg_left (PreparedAsymptotics.capacity_upper n)
      (by positivity))

theorem space_corollary (T : DecisionThreshold) (rho : ℝ)
    (hrho : (199/1000 : ℝ) < rho) (c : ℕ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ I : Instance n, inputBits I ≤ n^c →
      ∀ words : WordFinalDecision.Words I,
        ((WordFinalDecision.run T I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((WordFinalDecision.run T I words).2 : ℝ) ≤
          (2*(3 : ℝ)^15)*(2 : ℝ)^(rho*n) := by
  filter_upwards [main_resources T c hc,absorb_space_polynomial hrho c hc] with n hm hs
  intro I hI words
  refine ⟨(hm I hI words).1,(hm I hI words).2.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left (hs (inputBits I) hI) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [inputScale,Nat.cast_add,Nat.cast_ofNat,mul_assoc] using h

/-- One-sided correctness and one-fifth-exponential storage for any fixed
threshold satisfying the large-input conditions. -/
theorem conditional_main (T : DecisionThreshold) :
    (∀ (n : ℕ) (I : Instance n) (words : WordFinalDecision.Words I),
      (WordFinalDecision.run T I words).1.1 = true → Solvable I) ∧
    (∀ (n : ℕ) (I : Instance n), Solvable I →
      (2/3 : ℝ) ≤ (FiniteLaw.uniform : FiniteLaw (WordFinalDecision.Words I)).probability
        (fun words => (WordFinalDecision.run T I words).1.1 = true)) ∧
    (∀ c : ℕ, 0 < c → ∀ᶠ n : ℕ in atTop,
      ∀ I : Instance n, inputBits I ≤ n^c → ∀ words : WordFinalDecision.Words I,
        ((WordFinalDecision.run T I words).1.2 : ℝ) ≤
          (4*(3 : ℝ)^624)*(n : ℝ)^(624*c)*(2 : ℝ)^((1/2 : ℝ)*n) ∧
        ((WordFinalDecision.run T I words).2 : ℝ) ≤
          (2*(3 : ℝ)^15)*(2 : ℝ)^((1/5 : ℝ)*n)) := by
  refine ⟨fun _ I words => WordFinalDecision.sound T I words,
    fun _ I => WordFinalDecision.probability T I,?_⟩
  intro c hc
  exact space_corollary T (1/5) (by norm_num) c hc

end LowSpaceSubsetSum.WordMain

end

end OAI
