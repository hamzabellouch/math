import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonStatement
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter

theorem single_provider_of_universal_estimates (d : Decomposition)
    (hest : ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀ k : ℕ,2≤k →
      ActualUniversalEstimates d BD Bz k) :
    ActualSingleComparisonProvider d 17 := by
  intro BD Bz hBD hBz k hk
  refine ⟨1,by norm_num,?_⟩
  filter_upwards [hest BD Bz hBD hBz k hk] with L hL
  intro P hP hZ E C hsource j hj
  exact (hL P hP hZ E C hsource j (Nat.le_of_lt hj)).1

theorem bad_provider_of_universal_estimates (d : Decomposition)
    (hest : ∀ BD Bz : ℝ,0≤BD → 9≤Bz → ∀ k : ℕ,2≤k →
      ActualUniversalEstimates d BD Bz k) :
    ActualBadCovarianceComparisonProvider d 17 := by
  intro BD Bz hBD hBz k hk
  refine ⟨1,by norm_num,?_⟩
  filter_upwards [hest BD Bz hBD hBz k hk] with L hL
  intro P hP hZ E C hsource a b _
  apply ((hL P hP hZ E C hsource k le_rfl).2 a b).trans
  apply Real.exp_le_exp.mpr
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
