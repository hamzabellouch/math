import Mathlib
import OAI.Analysis.LaughlinFock.CopyAverage
import OAI.Analysis.LaughlinFock.FourTraces

namespace OAI

/-! Four Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem trace_column_bilinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C D : Matrix ι κ ℂ) (M : Matrix ι ι ℂ) :
    (Cᴴ*M*D).trace = ∑ k, star (fun b => C b k) ⬝ᵥ (M *ᵥ fun b => D b k) := by
  rw [Matrix.mul_assoc]
  rfl

 

theorem fourCopy_row_trace {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    ((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace = (rowFourTrace Q D t a r s : ℂ) := by
  have hr := r.val.isLt
  have hs := s.val.isLt
  rw [trace_column_bilinear]
  erw [fourCopyColumns, ite_eq_left (by omega : D+r.val.val ≤ 2*Q),
    fourCopyColumns, ite_eq_left (by omega : D+s.val.val ≤ 2*Q)]
  have hd : fourSpinDegree Q D+1 = 4*Q-1-2*D := by
    dsimp [fourSpinDegree]
    omega
  convert sourceRowFourKernel_copyTrace hQ hD a r s using 1
  rw [hd]

 

theorem fourCopy_row_trace_above_support {Q D t : ℕ} (hQ : 24 ≤ Q) (hD : 23 < D)
    (a : RowEntry t → ℝ) (r s : CopyLabel D) :
    ((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace = 0 := by
  by_cases hr : D+r.val.val ≤ 2*Q
  · by_cases hs : D+s.val.val ≤ 2*Q
    · rw [trace_column_bilinear]
      erw [fourCopyColumns, ite_eq_left hr, fourCopyColumns, ite_eq_left hs]
      apply Finset.sum_eq_zero
      intro k _
      have hrl : r.val.val ≤ D := Nat.le_of_lt_succ r.val.isLt
      have hsl : s.val.val ≤ D := Nat.le_of_lt_succ s.val.isLt
      have he := rowFourPrewedge_coupled_bilinear hrl hsl (by omega : D ≤ D+k.val)
        (by omega : r.val.val ≤ Q) (by omega : s.val.val ≤ Q) r.property s.property
        (sourceRowFourP (by omega : 8 ≤ Q)) (sourceRowI (by omega : 8 ≤ Q))
        (sourceRowJ (by omega : 8 ≤ Q)) a
      simp only [Nat.add_sub_cancel_left] at he
      rw [sourceRowFourKernel, he]
      have hz : (∑ b : RowEntry t, ∑ c : RowEntry t, a b*a c *
          sphericalCopyCoefficient Q D (D+k.val) r.val.val (rowP b) (rowJ b) (rowI c) *
          sphericalCopyCoefficient Q D (D+k.val) s.val.val (rowP c) (rowJ c) (rowI b)) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        apply Finset.sum_eq_zero
        intro c _
        have hl := rowFourLevel_le b c
        have hn : rowP b+rowJ b+rowI c ≠ D+k.val := by
          dsimp [rowFourLevel] at hl
          omega
        rw [sphericalCopyCoefficient_level _ _ _ _ _ _ _ hn, mul_zero, zero_mul]
      simp only [sourceRowFourP, sourceRowI, sourceRowJ, hz, neg_zero, Complex.ofReal_zero]
    · simp [fourCopyColumns, hs]
  · simp [fourCopyColumns, hr]

 

def fourCopyLift (Q D : ℕ) (r s : CopyLabel D) : FockMatrix Q :=
  exteriorLift Q 4 (fourCopyWedge Q D r*(fourCopyWedge Q D s)ᴴ)

 

theorem fockAverage_rowFourBody {Q t : ℕ} (hQ : 24 ≤ Q) (a : RowEntry t → ℝ) :
    fockAverage Q (rowFourBody Q rowP (sourceRowI (by omega : 8 ≤ Q))
      (sourceRowJ (by omega : 8 ≤ Q)) a) =
      ∑ D ∈ Finset.Icc 1 23, ∑ r : CopyLabel D, ∑ s : CopyLabel D,
        ((rowFourTrace Q D t a r s : ℂ)/(fourSpinDegree Q D+1 : ℂ)) •
          fourCopyLift Q D r s := by
  have hs (c : ℂ) (M : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ) :
      exteriorLift Q 4 (c • M) = c • exteriorLift Q 4 M := (exteriorLiftLinear Q 4).map_smul c M
  rw [← sourceRowFourKernel_lift (by omega : 8 ≤ Q) a, fockAverage_exteriorLift,
    sectorAverage_four_kernel (by omega)]
  simp only [exteriorLift_sum, hs]
  let f (D : ℕ) := ∑ r : CopyLabel D, ∑ s : CopyLabel D,
    (((fourCopyColumns Q D r)ᴴ * sourceRowFourKernel (by omega : 8 ≤ Q) a *
      fourCopyColumns Q D s).trace / (fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s
  change (∑ D : Fin (2*Q), f D.val) = _
  rw [Fin.sum_univ_eq_sum_range f (2*Q)]
  calc
    _ = ∑ D ∈ Finset.Icc 1 23, f D := by
      symm
      apply Finset.sum_subset
      · intro D hD
        simp only [Finset.mem_Icc] at hD
        simp only [Finset.mem_range]
        omega
      · intro D hDr hD
        by_cases hz : D=0
        · subst D
          have he : IsEmpty (CopyLabel 0) := ⟨fun r => by have := r.val.isLt; have := r.property.pos; omega⟩
          let := he
          simp [f]
        · have hd : 23 < D := by simp only [Finset.mem_Icc] at hD; omega
          dsimp [f]
          simp only [fourCopy_row_trace_above_support hQ hd, zero_div, zero_smul, Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      dsimp [f]
      simp only [fourCopy_row_trace hQ (Finset.mem_Icc.mp hD).2]

end LaughlinFock
end

end OAI
