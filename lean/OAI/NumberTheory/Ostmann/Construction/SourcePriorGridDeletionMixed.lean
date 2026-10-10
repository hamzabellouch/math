import OAI.NumberTheory.Ostmann.Construction.DiagonalExternalMeasure
import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.SourcePriorGridDeletion

theorem weighted_grid_deletion_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (S : Finset ℕ) (w : ℕ→ℝ) (hw : ∀n∈S,0≤w n) (H : ℕ→ℕ→ℂ)
    {A : ℝ} (hA : 0≤A)
    (hH : ∀n∈S,w n≠0→∀p∈logCellPrimes G,logCellWeight G p≠0→‖H n p‖≤A) :
    ‖(∑n∈S,(w n:ℂ)*gridMean G E (H n))-
      (∑n∈S,(w n:ℂ)*(logCellPrimeSource G E hZ).law.cmean (fun p => H n p))‖≤
      (∑n∈S,w n)*(deletionCap G E*A) := by
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  calc
    _ ≤ ∑n∈S,‖(w n:ℂ)*(gridMean G E (H n)-
        (logCellPrimeSource G E hZ).law.cmean (fun p => H n p))‖ := norm_sum_le _ _
    _ ≤ ∑n∈S,w n*(deletionCap G E*A) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hz : w n=0
      · simp [hz]
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw n hn)]
        exact mul_le_mul_of_nonneg_left
          (gridMean_sub_source_cmean_le G E hZ (H n) hA (hH n hn hz)) (hw n hn)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem integer_prime_grid_deletion_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (H : ℕ→ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hH : ∀n∈integerPivotCell G,externalPivotWeight G n≠0→
      ∀p∈logCellPrimes G,logCellWeight G p≠0→‖H n p‖≤A) :
    ‖(∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*gridMean G E (H n))-
      (∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*
        (logCellPrimeSource G E hZ).law.cmean (fun p => H n p))‖≤
      (∑n∈integerPivotCell G,externalPivotWeight G n)*(deletionCap G E*A) :=
  weighted_grid_deletion_le G E hZ (integerPivotCell G) (externalPivotWeight G)
    (fun n _ => externalPivotWeight_nonneg G n) H hA hH

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
