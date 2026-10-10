import OAI.NumberTheory.TotientAsymptotic.NormalityIntervals
import OAI.NumberTheory.TotientAsymptotic.PublishedNormality

namespace OAI

/-! Transfer of a failed normality condition to the cofactor after one prime is removed. -/
noncomputable section
namespace TotientAsymptotic

lemma nonnormal_prime_cofactor {b q : ℕ} (hb : b≠0) (hq : q.Prime)
    (hp : (b*q+1).Prime) (S : ℝ) (hbad : ¬IsNormalPrime S (b*q+1)) :
    2*B S-1 < (omegaIn b 1 S:ℝ) ∨
      ∃ U T : ℝ, S≤U ∧ U<T ∧ T≤(b*q:ℕ) ∧
        Real.sqrt (B S*B T)-1≤|(omegaIn b U T:ℝ)-(B T-B U)| := by
  simp only [IsNormalPrime,hp,true_and,Nat.add_sub_cancel,not_and_or] at hbad
  rcases hbad with hsmall|hinterval
  · left
    have hh := (omegaIn_remove_prime hb hq 1 S).2
    have hhR : (omegaIn (b*q) 1 S:ℝ)≤(omegaIn b 1 S:ℝ)+1 := by exact_mod_cast hh
    push Not at hsmall
    linarith
  · right
    push Not at hinterval
    obtain ⟨U,T,hSU,hUT,hT,hh⟩ := hinterval
    exact ⟨U,T,hSU,hUT,hT,prime_removal_deviation hb hq U T (B T-B U)
      (Real.sqrt (B S*B T)) hh⟩

end TotientAsymptotic

end

end OAI
