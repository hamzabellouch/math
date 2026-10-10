import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryGuesses

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling Guided

theorem recoveryTrial_uniform_exponential : ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [Fintype V] [LinearOrder V] [PseudoMetricSpace V],
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V) (hSF : S ⊆ F), O ⊆ F → ∀ (hS : S.Nonempty)
      (Δ : ℝ) (hΔ : 1 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ),
      (∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) →
      0 < comparisonCost D C.assign → 0 < C.bad.card →
      Real.exp (-c*C.bad.card) ≤
        probability (fun seed : IntegralBits D Δ C.bad.card × (Fin (localTapeBound F C.bad.card) → Bool) =>
          realCost D (recoveryTrial D F S hD hSF hS Δ (comparisonCost D C.assign)
            (by linarith) hbound C.bad.card seed) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨c,hc,hsample⟩ := sampling_exponential
  obtain ⟨d,hd,hcompletion⟩ := completion_exponential
  refine ⟨c+d,add_pos hc hd,?_⟩
  intro V _ _ _ D S O C hD F hSF hOF hS Δ hΔ hbound hsep hP hm
  calc
    _ = Real.exp (-c*C.bad.card)*Real.exp (-d*C.bad.card) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card) *
        ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)) :=
      mul_le_mul (hsample C.bad.card) (hcompletion C.bad.card hm)
        (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (hsample C.bad.card))
    _ ≤ _ := C.recoveryTrial_success hD F hSF hOF hS Δ hΔ hbound hsep hP hm

theorem recoveryAll_uniform_guarantees : ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type*) [Fintype V] [LinearOrder V] [PseudoMetricSpace V],
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V) (hSF : S ⊆ F), O ⊆ F → ∀ (hS : S.Nonempty)
      (M : ℕ) (hM : 1 ≤ M) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ M),
      (∀ p ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist p f) →
      (∀ p ∈ D, ∀ f ∈ F, ∃ d : ℕ, dist p f = (d:ℝ)) →
      ∀ L : ℕ, C.bad.card ≤ L → ∀ ζ : ℝ, 0 < ζ → ∀ n : ℕ,
      Real.log (1/ζ)/Real.exp (-c*L) ≤ (n:ℝ) →
      probability (fun seed : RecoverySeed D F M L (D.card*M) n =>
        realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed) ≤
          (197/100:ℝ)*comparisonCost D C.assign) ≥ 1-ζ ∧
      average (fun seed : RecoverySeed D F M L (D.card*M) n =>
        realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed)) ≤
          (197/100:ℝ)*comparisonCost D C.assign + realCost D S*ζ := by
  classical
  obtain ⟨c,hc,hsuccess⟩ := recoveryTrial_uniform_exponential
  refine ⟨c,hc,?_⟩
  intro V _ _ _ D S O C hD F hSF hOF hS M hM hbound hsep hint L hL ζ hζ n hn
  have hMreal : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hP := C.comparison_cost_positive hD F hOF hsep
  have hnonneg : 0 ≤ realCost D S := by
    simp only [realCost,dite_eq_left hS]
    exact Finset.sum_nonneg (fun _ _ => distanceTo_nonneg _ _ _)
  have hpoint (seed : RecoverySeed D F M L (D.card*M) n) :=
    (recoveryAll_feasible D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed).2.2.2
  have hprob : 1-ζ ≤ probability (fun seed : RecoverySeed D F M L (D.card*M) n =>
        realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed) ≤
          (197/100:ℝ)*comparisonCost D C.assign) := by
    by_cases hm : C.bad.card = 0
    · have hexact : ∀ seed : RecoverySeed D F M L (D.card*M) n,
          realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed) ≤
            (197/100:ℝ)*comparisonCost D C.assign := by
        intro seed
        exact (hpoint seed).trans ((C.no_bad_proxy_cost hS hm).trans (by nlinarith))
      rw [probability_congr (fun seed => iff_true_intro (hexact seed))]
      simp only [probability,ite_true,average_const]
      linarith
    · have hmpos : 0 < C.bad.card := Nat.pos_of_ne_zero hm
      have hint' : ∀ p f : V, ∃ d : ℕ, p ∈ D → f ∈ F → dist p f = (d:ℝ) := by
        intro p f
        by_cases hp : p ∈ D
        · by_cases hf : f ∈ F
          · obtain ⟨d,hd⟩ := hint p hp f hf
            exact ⟨d,fun _ _ => hd⟩
          · exact ⟨0,fun _ h => False.elim (hf h)⟩
        · exact ⟨0,fun h _ => False.elim (hp h)⟩
      choose δ hδ using hint'
      obtain ⟨P,hPU,hPeq⟩ := C.integer_comparison_cost F hOF δ M
        (fun p hp f hf => (hδ p f hp hf).symm)
        (fun p hp f hf => by exact_mod_cast (hδ p f hp hf ▸ hbound p f hf))
      let guess : RecoveryGuesses L (D.card*M) :=
        (⟨C.bad.card,Nat.lt_succ_of_le hL⟩,⟨P,Nat.lt_succ_of_le hPU⟩)
      have hs := hsuccess V C hD F hSF hOF hS M hMreal hbound hsep hP hmpos
      have hexp : Real.exp (-c*L) ≤ Real.exp (-c*C.bad.card) := by
        apply Real.exp_le_exp.mpr
        have hLreal : (C.bad.card:ℝ) ≤ L := by exact_mod_cast hL
        nlinarith
      have hamplified := (amplified_output (realCost D) S
        (recoveryTrial D F S hD hSF hS M (comparisonCost D C.assign)
          (by positivity) hbound C.bad.card)
        (by positivity : (0:ℝ) ≤ (197/100:ℝ)*comparisonCost D C.assign)
        hnonneg le_rfl (Real.exp_pos _) (hexp.trans hs) hζ n hn).2.1
      have hbranch : 1-ζ ≤ probability (fun bits =>
          realCost D (recoveryRepeat D F S hD hSF hS M (guess.2.val:ℝ)
            (by positivity) hbound guess.1.val n bits) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
        dsimp only [guess]
        rw [← hPeq]
        exact hamplified
      exact enumerateBranches_success (realCost D) S
        (fun guess : RecoveryGuesses L (D.card*M) =>
          recoveryRepeat D F S hD hSF hS M guess.2.val (by positivity) hbound guess.1.val n)
        guess _ _ hbranch
  refine ⟨hprob,?_⟩
  have hfail : probability (fun seed : RecoverySeed D F M L (D.card*M) n =>
        (197/100:ℝ)*comparisonCost D C.assign <
          realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed)) ≤ ζ := by
    rw [show (fun seed : RecoverySeed D F M L (D.card*M) n =>
        (197/100:ℝ)*comparisonCost D C.assign <
          realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed)) =
        (fun seed => ¬realCost D (recoveryAll D F S hD hSF hS M (by positivity) hbound L (D.card*M) n seed) ≤
          (197/100:ℝ)*comparisonCost D C.assign) from by funext seed; exact propext not_le.symm,
      probability_compl]
    linarith
  exact (average_le_threshold_add_failure _ (B := (197/100:ℝ)*comparisonCost D C.assign) (by positivity) hpoint).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hfail hnonneg])

end MetricKMedianRecovery.Sampling.Comparison

end OAI
