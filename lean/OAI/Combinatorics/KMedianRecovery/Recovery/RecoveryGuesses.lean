import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RecoveryRepeat
import OAI.Combinatorics.KMedianRecovery.Branching.EnumerateBranches

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Guided Comparison
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

abbrev RecoveryGuesses (L U : ℕ) := Fin (L+1) × Fin (U+1)
noncomputable abbrev RecoverySeed (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :=
  ∀ guess : RecoveryGuesses L U,
    Fin n → IntegralBits D Δ guess.1.val × (Fin (localTapeBound F guess.1.val) → Bool)

noncomputable def recoveryAll (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (L U n : ℕ)
    (seed : RecoverySeed D F Δ L U n) : Finset V :=
  enumerateBranches (realCost D) S (fun guess : RecoveryGuesses L U =>
    recoveryRepeat D F S hD hSF hS Δ guess.2.val hΔ hbound guess.1.val n) seed

lemma recoveryAll_feasible (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (L U n : ℕ)
    (seed : RecoverySeed D F Δ L U n) :
    recoveryAll D F S hD hSF hS Δ hΔ hbound L U n seed ⊆ F ∧
    (recoveryAll D F S hD hSF hS Δ hΔ hbound L U n seed).card ≤ S.card ∧
    (recoveryAll D F S hD hSF hS Δ hΔ hbound L U n seed).Nonempty ∧
    realCost D (recoveryAll D F S hD hSF hS Δ hΔ hbound L U n seed) ≤ realCost D S := by
  apply enumerateBranches_feasible (realCost D) S _
    (fun T => T ⊆ F ∧ T.card ≤ S.card ∧ T.Nonempty ∧ realCost D T ≤ realCost D S)
    ⟨hSF,le_rfl,hS,le_rfl⟩
  intro guess bits
  exact recoveryRepeat_feasible D F S hD hSF hS Δ guess.2.val hΔ hbound guess.1.val n bits

lemma recoveryAll_le (D F S : Finset V) (hD : D.Nonempty)
    (hSF : S ⊆ F) (hS : S.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ) (L U n : ℕ)
    (seed : RecoverySeed D F Δ L U n) (guess : RecoveryGuesses L U) :
    realCost D (recoveryAll D F S hD hSF hS Δ hΔ hbound L U n seed) ≤
    realCost D (recoveryRepeat D F S hD hSF hS Δ guess.2.val hΔ hbound guess.1.val n (seed guess)) :=
  (enumerateBranches_le _ _ _ seed).2 guess

namespace Comparison
variable {D S O : Finset V}

omit [Fintype V] in
lemma no_bad_proxy_cost (C : Comparison D S O) (hS : S.Nonempty) (hm : C.bad.card = 0) :
    realCost D S ≤ (101/100:ℝ)*comparisonCost D C.assign := by
  have hOS : O ⊆ C.good := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)
  have he : C.good = O := Finset.Subset.antisymm C.good_subset hOS
  have hpart := cluster_partition D C.good C.assign (fun p hp => hOS (C.assigned p hp))
    (distanceTo S hS)
  have hc : realCost D S ≤ ∑ o ∈ C.good, ∑ p ∈ cluster D C.assign o, dist p (C.proxy o) := by
    simp only [realCost,dite_eq_left hS]
    rw [← hpart]
    apply Finset.sum_le_sum
    intro o ho
    exact Finset.sum_le_sum (fun p _ => distanceTo_le hS p (C.proxy_mem o ho))
  have hcO := comparisonCost_eq D O C.assign C.assigned
  have hcost := C.proxy_cost
  rw [he,hcO] at hcost
  rw [he] at hc
  linarith

omit [Fintype V] in
lemma integer_comparison_cost (C : Comparison D S O) (F : Finset V) (hOF : O ⊆ F)
    (δ : V → V → ℕ) (M : ℕ)
    (hδ : ∀ p ∈ D, ∀ f ∈ F, (δ p f:ℝ) = dist p f)
    (hM : ∀ p ∈ D, ∀ f ∈ F, δ p f ≤ M) :
    ∃ P : ℕ, P ≤ D.card*M ∧ comparisonCost D C.assign = (P:ℝ) := by
  refine ⟨∑ p ∈ D, δ p (C.assign p),?_,?_⟩
  · calc
      _ ≤ ∑ _p ∈ D, M := Finset.sum_le_sum (fun p hp => hM p hp _ (hOF (C.assigned p hp)))
      _ = _ := by simp
  · simp only [comparisonCost,Nat.cast_sum]
    exact Finset.sum_congr rfl (fun p hp => (hδ p hp _ (hOF (C.assigned p hp))).symm)

omit [Fintype V] in
lemma comparison_cost_positive (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F)
    (hsep : ∀ p ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist p f) : 0 < comparisonCost D C.assign := by
  unfold comparisonCost
  exact Finset.sum_pos (fun p hp => lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hsep p hp _ (hOF (C.assigned p hp)))) hD

theorem recoveryAll_guarantees : ∃ c : ℝ, 0 < c ∧
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
  obtain ⟨c,hc,hsuccess⟩ := recoveryTrial_exponential (V := V)
  refine ⟨c,hc,?_⟩
  intro D S O C hD F hSF hOF hS M hM hbound hsep hint L hL ζ hζ n hn
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
      have hs := hsuccess C hD F hSF hOF hS M hMreal hbound hsep hP hmpos
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

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
