import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SumPeriodBlocks

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical Filter OrdinaryCorrelations.FiniteIntegration

lemma integerResidues_add (S : PrimeSystem) (m n : ℤ) :
    S.integerResidues (m+n) = S.integerResidues m + S.integerResidues n := by
  funext p
  exact Int.cast_add _ _

lemma period_sum_shift (S : PrimeSystem) (F : S.Residues → ℝ) (z : ℤ) :
    (∑ n ∈ range S.modulus, F (S.integerResidues ((n : ℤ)+z))) = ∑ x, F x := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he := (S.residueEquiv).sum_comp (fun x => F (x + S.integerResidues z))
  simp only [residueEquiv,Equiv.ofBijective_apply,← integerResidues_add] at he
  rw [he]
  exact Equiv.sum_comp (Equiv.addRight (S.integerResidues z)) F

lemma origin_periodic (S : PrimeSystem) (F : S.Residues → ℝ) (z : ℤ) :
    Function.Periodic (fun n : ℕ => F (S.integerResidues ((n : ℤ)+z))) S.modulus := by
  intro n
  have hp := S.integerResidues_periodic ((n : ℤ)+z)
  simpa only [Nat.cast_add,add_right_comm] using congrArg F hp

theorem integer_origin_discrepancy (S : PrimeSystem) (F : S.Residues → ℝ) (z : ℤ) (N : ℕ) :
    |(∑ n ∈ range N, F (S.integerResidues ((n : ℤ)+z))) - (N : ℝ)*avg F| ≤
      2*∑ x, |F x| := by
  have hd := OrdinaryCorrelations.PeriodicOrigin.discrepancy S.modulus N S.modulus_pos
    (fun n => F (S.integerResidues ((n : ℤ)+z))) (S.origin_periodic F z)
  rw [S.period_sum_shift F z,S.period_sum_shift (fun x => |F x|) z] at hd
  simpa only [avg,S.residues_card,div_eq_mul_inv,mul_comm (∑ x, F x)] using hd

theorem real_origin_discrepancy (S : PrimeSystem) (F : S.Residues → ℝ) (z : ℤ)
    (X : ℝ) (hX : 0 < X) :
    |(∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z)))/X - avg F| ≤
      (2*∑ x, |F x| + |avg F|)/X := by
  have hd := S.integer_origin_discrepancy F z ⌊X⌋₊
  have hfloor : (0 : ℝ) ≤ X-(⌊X⌋₊ : ℕ) := sub_nonneg.mpr (Nat.floor_le hX.le)
  have hfloor_le : X-(⌊X⌋₊ : ℕ) ≤ (1 : ℝ) := by linarith [Nat.lt_floor_add_one X]
  have hb : |(∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z)))-X*avg F| ≤
      2*∑ x, |F x| + |avg F| := by
    calc
      _ = |((∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z))) - (⌊X⌋₊ : ℕ)*avg F)
          - (X-(⌊X⌋₊ : ℕ))*avg F| := by congr 1; ring
      _ ≤ |(∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z))) - (⌊X⌋₊ : ℕ)*avg F|
          + |(X-(⌊X⌋₊ : ℕ))*avg F| := abs_sub _ _
      _ ≤ _ := by
        apply add_le_add hd
        rw [abs_mul,abs_of_nonneg hfloor]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfloor_le (abs_nonneg (avg F))
  have he : (∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z)))/X - avg F =
      ((∑ n ∈ range ⌊X⌋₊, F (S.integerResidues ((n : ℤ)+z)))-X*avg F)/X := by
    field_simp
  rw [he,abs_div,abs_of_pos hX]
  exact div_le_div_of_nonneg_right hb hX.le

theorem real_origin_tendsto (S : PrimeSystem) (F : S.Residues → ℝ) (z : ℝ → ℤ) :
    Tendsto (fun X : ℝ => (∑ n ∈ range ⌊X⌋₊,
      F (S.integerResidues ((n : ℤ)+z X)))/X) atTop (𝓝 (avg F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    simpa only [Real.norm_eq_abs] using S.real_origin_discrepancy F (z X) X hX
  · exact tendsto_const_nhds.div_atTop tendsto_id

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
