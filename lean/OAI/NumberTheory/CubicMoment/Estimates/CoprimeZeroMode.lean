import OAI.NumberTheory.CubicMoment.Estimates.WidePoissonRecurrence

namespace OAI

/-! Keep the zero frequency explicitly when a common-factor quotient
contains the unit row. No nonunit assumption is imposed on that support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma hasSum_frequencyDyad_sub_zero (F : Eisenstein → ℂ) (hF : Summable F) :
    HasSum (fun j : ℕ => ∑ h ∈ frequencyDyad j, F h) ((∑' h, F h)-F 0) := by
  have hs : HasSum (fun h : Eisenstein => if h = 0 then 0 else F h) ((∑' h, F h)-F 0) :=
    hasSum_ite_sub_hasSum hF.hasSum 0
  have hd := hasSum_frequencyDyad _ hs.summable (by simp)
  rw [hs.tsum_eq] at hd
  apply hd.congr_fun
  intro j
  apply Finset.sum_congr rfl
  intro h hh
  exact (ite_eq_right (mem_frequencyDyad.mp hh).1).symm

lemma coprimeGramForm_poisson_all (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun h : Eisenstein => coprimePoissonDyad S {h} u W Z) (coprimeGramForm S u W Z) := by
  unfold coprimePoissonDyad coprimeGramForm
  simp only [Finset.sum_singleton]
  apply hasSum_sum
  intro a ha
  apply hasSum_sum
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    have hs := (summable_gramDualTerm (hS a ha).1 (hS b hb).1 W hW hW' hZ).hasSum.mul_left
      (u a*star (u b)*(Z/(9*Real.sqrt (norm (a*b))):ℝ)*(gauss a*star (gauss b)))
    convert hs using 1
    rw [primaryCharacterGram_poisson_normalized (hS a ha).1 (hS b hb).1
      (hS a ha).2 (hS b hb).2 hab W hW hW' hZ]
    ring
  · simp only [ite_eq_right hab]
    exact hasSum_zero

 theorem hasSum_coprimePoissonDyad_with_zero (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 0 < Z) :
    HasSum (fun j : ℕ => coprimePoissonDyad S (frequencyDyad j) u W Z)
      (coprimeGramForm S u W Z-coprimePoissonDyad S {0} u W Z) := by
  have hs := coprimeGramForm_poisson_all S hS u W hW hW' hZ
  have hd := hasSum_frequencyDyad_sub_zero _ hs.summable
  rw [hs.tsum_eq] at hd
  apply hd.congr_fun
  intro j
  symm
  unfold coprimePoissonDyad
  simp only [Finset.sum_singleton]
  simp_rw [Finset.sum_comm (s := frequencyDyad j) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,Finset.mul_sum]
  · simp only [ite_eq_right hab,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
