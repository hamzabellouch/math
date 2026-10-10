import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionBasic

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction.SourcePriorGridDeletion

theorem pointCap_nonneg (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    0≤pointCap G E := div_nonneg (Real.exp_pos _).le hZ.le

theorem deletionCap_nonneg (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    0≤deletionCap G E := mul_nonneg (Nat.cast_nonneg _) (pointCap_nonneg G E hZ)

theorem fullMassRatio_nonneg (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    0≤fullMassRatio G E := div_nonneg (logCellMass_nonneg _ _) hZ.le

theorem fullMassRatio_le_one_add (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E) :
    fullMassRatio G E≤1+deletionCap G E := by
  have h := (finite_deletion_bound (logCellPrimes G) E (logCellWeight G)
    (Real.exp_pos (1-G)).le (logCellWeight_nonneg G) (logCellWeight_le_exp G)).2
  have hm : logCellMass G ∅≤logCellMass G E+E.card*Real.exp (1-G) := by
    simp only [logCellMass,Finset.sdiff_empty] at ⊢
    linarith
  unfold fullMassRatio deletionCap pointCap
  calc
    _ ≤ (logCellMass G E+E.card*Real.exp (1-G))/logCellMass G E :=
      div_le_div_of_nonneg_right hm hZ.le
    _ = _ := by field_simp

theorem deletedMean_sub (G : ℝ) (E : Finset ℕ) (F H : ℕ→ℂ) :
    deletedMean G E (fun p => F p-H p)=deletedMean G E F-deletedMean G E H := by
  simp only [deletedMean,mul_sub,Finset.sum_sub_distrib]

theorem deletedMean_norm_le (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (F : ℕ→ℂ) {A : ℝ} (_hA : 0≤A)
    (hF : ∀p∈logCellPrimes G,logCellWeight G p≠0→‖F p‖≤A) :
    ‖deletedMean G E F‖≤A := by
  calc
    _ ≤ ∑p∈logCellPrimes G\E,‖((logCellWeight G p/logCellMass G E:ℝ):ℂ)*F p‖ := norm_sum_le _ _
    _ ≤ ∑p∈logCellPrimes G\E,(logCellWeight G p/logCellMass G E)*A := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hz : logCellWeight G p=0
      · simp [hz]
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (logCellWeight_nonneg G p) hZ.le)]
        exact mul_le_mul_of_nonneg_left (hF p (Finset.mem_sdiff.mp hp).1 hz)
          (div_nonneg (logCellWeight_nonneg G p) hZ.le)
    _ = A := by
      rw [←Finset.sum_mul,←Finset.sum_div]
      change logCellMass G E/logCellMass G E*A=A
      rw [div_self hZ.ne',one_mul]

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
