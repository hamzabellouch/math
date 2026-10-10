import OAI.NumberTheory.TotientAsymptotic.NormalityAlignment

namespace OAI

/-! Monotonicity and prime-removal bridges for the normality intervals. -/
noncomputable section
namespace TotientAsymptotic

lemma omegaIn_mono (n : ℕ) {U₁ U₂ T₁ T₂ : ℝ} (hU : U₂≤U₁) (hT : T₁≤T₂) :
    omegaIn n U₁ T₁ ≤ omegaIn n U₂ T₂ := by
  classical
  unfold omegaIn
  rw [← List.countP_eq_length_filter,← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro p _ hp
  simp only [decide_eq_true_eq] at hp ⊢
  exact ⟨hU.trans_lt hp.1,hp.2.trans hT⟩

lemma omegaIn_prime_le_one {p : ℕ} (hp : p.Prime) (U T : ℝ) :
    omegaIn p U T≤1 := by
  unfold omegaIn
  rw [Nat.primeFactorsList_prime hp]
  exact (List.length_filter_le _ _).trans (by simp)

lemma omegaIn_remove_prime {b q : ℕ} (hb : b≠0) (hq : q.Prime) (U T : ℝ) :
    omegaIn b U T ≤ omegaIn (b*q) U T ∧
      omegaIn (b*q) U T ≤ omegaIn b U T+1 := by
  rw [omegaIn_mul hb hq.ne_zero]
  have hh := omegaIn_prime_le_one hq U T
  omega

lemma prime_removal_deviation {b q : ℕ} (hb : b≠0) (hq : q.Prime)
    (U T M H : ℝ) (hbad : H≤|(omegaIn (b*q) U T:ℝ)-M|) :
    H-1≤|(omegaIn b U T:ℝ)-M| := by
  have hdiff := omegaIn_remove_prime hb hq U T
  have hl : (omegaIn b U T:ℝ)≤omegaIn (b*q) U T := by exact_mod_cast hdiff.1
  have hu : (omegaIn (b*q) U T:ℝ)≤(omegaIn b U T:ℝ)+1 := by exact_mod_cast hdiff.2
  have hab : |(omegaIn (b*q) U T:ℝ)-(omegaIn b U T:ℝ)|≤1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have htri := abs_sub_le (omegaIn (b*q) U T:ℝ) (omegaIn b U T:ℝ) M
  linarith

end TotientAsymptotic

end

end OAI
