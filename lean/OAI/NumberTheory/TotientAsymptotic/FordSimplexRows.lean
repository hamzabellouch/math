import OAI.NumberTheory.TotientAsymptotic.SmallTerminalPrefix

namespace OAI

/-! Assemble Ford's stated simplex condition from the full row inequalities. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_simplex_of_full_rows {x : ℝ} {Ψ n : ℕ} (hΨ : Ψ < m x)
    (htail : 2 < fordPrimeCoordinate n (m x-Ψ))
    (hcap : fordPrimeCoordinate n 1 ≤ B x)
    (hrows : ∀ i < m x-Ψ,fordRowSum (m x) (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i)) :
    fordSimplexCondition x Ψ n := by
  let J := m x-Ψ
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hB : 0 ≤ B x := (le_max_left _ _).trans hcap
  refine ⟨htail,?_,?_⟩
  · intro i hi
    obtain ⟨hi1,hiJ⟩ := Finset.mem_Icc.mp hi
    exact ⟨ford_coordinate_antitone n hiJ,(ford_coordinate_antitone n hi1).trans hcap⟩
  · intro i hi
    obtain ⟨_,hiJ⟩ := Finset.mem_Ico.mp hi
    change i < J at hiJ
    by_cases hlast : i+1=J
    · rw [ite_eq_left hlast]
      by_cases hi0 : i=0
      · subst i
        have he : J=1 := by omega
        change fordSimplexCoordinate x n J ≤ xi x 0*fordSimplexCoordinate x n 0
        rw [he]
        change fordPrimeCoordinate n 1 ≤ xi x 0*B x
        exact hcap.trans (by nlinarith only [(xi_bounds x 0).1,hB])
      · have ho := ford_coordinate_antitone n (show i ≤ J by omega)
        have hn : 0 ≤ fordPrimeCoordinate n i := le_max_left _ _
        have hx := (xi_bounds x i).1
        change fordSimplexCoordinate x n J ≤ xi x i*fordSimplexCoordinate x n i
        simp only [fordSimplexCoordinate,ite_eq_right (by omega : J≠0),ite_eq_right hi0]
        exact ho.trans (by nlinarith only [hx,hn])
    · rw [ite_eq_right hlast]
      have he : (∑ r ∈ Finset.Icc (i+1) J,a (r-i)*fordSimplexCoordinate x n r) =
          fordRowSum J (fordPrimeCoordinate n) i := by
        unfold fordRowSum
        apply Finset.sum_congr rfl
        intro r hr
        have hr := Finset.mem_Icc.mp hr
        rw [fordSimplexCoordinate,ite_eq_right (by omega : r≠0)]
      rw [he]
      exact (fordRowSum_truncate (Nat.sub_le _ _) _ (fun _ => le_max_left _ _)).trans (hrows i hiJ)

end TotientAsymptotic

end

end OAI
