import OAI.NumberTheory.TwoPoint.Halasz.HalaszCenteredEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalDensity

namespace OAI

/-! The exact dyadic atypical count in terms of the translated probability
used by the proved MRT density theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_typical_dyadic_count {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (N : ℕ) [NeZero N] :
    (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) =
      (N : ℝ) * (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical J P (N + 1 + n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [mul_one_div_cancel hN, one_mul]
  calc
    _ = ∑ n ∈ Ioc N (2 * N), if ¬mrtTypical J P n then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp
    _ = _ := by
      symm
      apply sum_bij (fun n : Fin N => fun _ => N + 1 + n.val)
      · intro n _
        apply mem_Ioc.mpr
        have hn := n.isLt
        omega
      · intro n _ m _ he
        apply Fin.ext
        omega
      · intro n hn
        refine ⟨⟨n - (N + 1), ?_⟩, mem_univ _, ?_⟩
        · have hn := mem_Ioc.mp hn
          omega
        · have hn := mem_Ioc.mp hn
          change N + 1 + (n - (N + 1)) = n
          omega
      · intro n _
        simp

lemma halasz_typical_dyadic_density_bound {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) {N : ℕ} [NeZero N] (δ : ℝ)
    (hδ : (uniformFiniteLaw (Fin N)).probability
      (fun n => ¬mrtTypical J P (N + 1 + n.val)) ≤ δ) :
    (((Ioc N (2 * N)).filter (fun n => ¬mrtTypical J P n)).card : ℝ) / N ≤ δ := by
  rw [halasz_typical_dyadic_count]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simpa [mul_div_cancel_left₀ _ hNr] using hδ

end TwoPointCorrelations

end OAI
