import OAI.NumberTheory.CubicMoment.Estimates.CoprimeZeroMode

namespace OAI

/-! The sole zero-frequency contribution of coprime squarefree rows
comes from the literal unit row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramDualTerm_unit_zero (W : ℝ → ℂ) (Z : ℝ) :
    gramDualTerm 1 1 W Z 0 = normProfileFourier W 0 := by
  simp [gramDualTerm,cubicSymbol_one_lower,tracePair]

lemma coprimePoissonDyad_unit_frequency (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (u : Eisenstein → ℂ) (W : ℝ → ℂ) (Z : ℝ) :
    coprimePoissonDyad S {0} u W Z =
      if (1:Eisenstein) ∈ S then
        u 1*star (u 1)*(Z/9:ℝ)*normProfileFourier W 0 else 0 := by
  let F (a b : Eisenstein) : ℂ := if IsCoprime a b then
    u a*star (u b)*(Z/(9*Real.sqrt (norm (a*b))):ℝ)*(gauss a*star (gauss b))*
      gramDualTerm a b W Z 0 else 0
  have hz (a b : Eisenstein) (ha : a ∈ S) (hb : b ∈ S)
      (hab1 : ¬(a = 1 ∧ b = 1)) : F a b = 0 := by
    dsimp only [F]
    by_cases hab : IsCoprime a b
    · rw [ite_eq_left hab]
      have hne : a ≠ b := by
        intro he
        have hdiag : IsCoprime a a := by simpa only [← he] using hab
        have hunit : IsUnit a := isCoprime_self.mp hdiag
        have ha1 := primary_unit_eq_one hunit (hS a ha).1
        exact hab1 ⟨ha1,he ▸ ha1⟩
      rw [gramDualTerm_zero (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2 hab hne]
      ring
    · exact ite_eq_right hab
  have hval : F 1 1 = u 1*star (u 1)*(Z/9:ℝ)*normProfileFourier W 0 := by
    simp [F,isCoprime_one_left,gramDualTerm_unit_zero,gauss_one,norm]
  unfold coprimePoissonDyad
  simp only [Finset.sum_singleton]
  change (∑ a ∈ S, ∑ b ∈ S, F a b) = _
  by_cases h1 : (1:Eisenstein) ∈ S
  · rw [ite_eq_left h1]
    calc
      _ = ∑ b ∈ S, F 1 b := Finset.sum_eq_single_of_mem 1 h1 (by
        intro a ha ha1
        exact Finset.sum_eq_zero (fun b hb => hz a b ha hb (fun hab => ha1 hab.1)))
      _ = F 1 1 := Finset.sum_eq_single_of_mem 1 h1 (by
        intro b hb hb1
        exact hz 1 b h1 hb (fun hab => hb1 hab.2))
      _ = _ := hval
  · rw [ite_eq_right h1]
    exact Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero
      (fun b hb => hz a b ha hb (fun hab => h1 (hab.1 ▸ ha))))

end CubicFirstMoment

end

end OAI
