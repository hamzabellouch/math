import Mathlib
import OAI.Analysis.LaughlinGap.AuxiliaryComparison
import OAI.Analysis.LaughlinGap.RealSpinSquare

namespace OAI

/-! Global Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

noncomputable def rowEta (rows : ι → RowData) : ℝ := ∑ r, (rows r).lam^2

noncomputable def auxiliaryThree {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) : FockMatrix (Q+1) :=
  ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (∑ r, rowThree hQ (rows r))
noncomputable def auxiliaryFour {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) : FockMatrix (Q+1) :=
  ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (∑ r, rowFour hQ (rows r))

lemma auxiliary_positive {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) :
    0 ≤ rowEta rows • physicalHamiltonian Q + auxiliaryThree hQ rows + auxiliaryFour hQ rows := by
  have hh (r : ι) := smul_nonneg (show (0:ℝ) ≤ ((2*Q-1:ℕ):ℝ) by positivity)
    (average_positive (rotationCommutant (fockLowering Q))
      (transpose_square_positive (rowAnnihilator hQ (rows r)))).nonneg
  simp only [rowSquare_average] at hh
  have h := Finset.sum_nonneg (fun r (_ : r ∈ (Finset.univ : Finset ι)) => hh r)
  simpa only [Finset.sum_add_distrib,← Finset.sum_smul,← Finset.smul_sum,← map_sum,
    rowEta,auxiliaryThree,auxiliaryFour] using h

noncomputable def threeRetained {Q : ℕ} (hQ : 15 ≤ Q) : FockMatrix (Q+1) :=
  ∑ z : Fin 16, threeBodyGramCoefficient Q z.val •
    threeSpinLift (by omega : 2 ≤ Q) (show z.val ≤ Q by omega)

lemma spin_sum_split {Q : ℕ} (hQ : 15 ≤ Q) :
    (∑ z : Fin (Q+1), threeBodyGramCoefficient Q z.val •
      threeSpinLift (by omega : 2 ≤ Q) (Nat.le_of_lt_succ z.isLt)) =
      threeRetained hQ + threeTailLift (by omega : 2 ≤ Q) := by
  classical
  let f : ℕ → FockMatrix (Q+1) := fun z => if hz : z ≤ Q then
    threeBodyGramCoefficient Q z • threeSpinLift (by omega) hz else 0
  have hret : threeRetained hQ = ∑ z : Fin (Q+1), if z.val ≤ 15 then f z.val else 0 := by
    rw [← sum_fin_extend hQ]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [f,threeRetained]
    rw [dite_eq_left (by omega)]
  have htail : threeTailLift (by omega : 2 ≤ Q) =
      ∑ z : Fin (Q+1), if 16 ≤ z.val then f z.val else 0 := by
    unfold threeTailLift
    apply Finset.sum_congr rfl
    intro z hz
    simp only [f,dite_eq_left (Nat.le_of_lt_succ z.isLt)]
  rw [hret,htail,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : z.val ≤ 15 <;> simp [h,show (16 ≤ z.val) ↔ ¬ z.val ≤ 15 by omega,f,Nat.le_of_lt_succ z.isLt]

lemma physical_spin_square_split {Q : ℕ} (hQ : 15 ≤ Q) :
    physicalHamiltonian Q * physicalHamiltonian Q = physicalHamiltonian Q +
      (threeRetained hQ + threeTailLift (by omega : 2 ≤ Q)) + fourTarget Q := by
  rw [physical_spin_square_real (by omega : 2 ≤ Q),spin_sum_split hQ]

lemma comparison_additive_step {A : Type*} [AddCommGroup A] [PartialOrder A] [IsOrderedAddMonoid A]
    {h s a b c t η e f τ : A} (hid : s = h+(c+t)+f) (haux : 0 ≤ η+a+b)
    (ha : a ≤ c) (hb : b ≤ f+e) (ht : -τ ≤ t) :
    h-η-τ-e ≤ s := by
  have hr := haux.trans (add_le_add (add_le_add (le_refl η) ha) hb)
  have hh := add_le_add (le_refl (h-η-e)) (add_le_add hr ht)
  convert hh using 1 <;> (try rw [hid]) <;> abel

lemma physical_square_of_comparisons {Q : ℕ} (hQ : 24 ≤ Q)
    (rows : ι → RowData) (δ : ℝ)
    (hthree : auxiliaryThree (by omega) rows ≤ threeRetained (by omega : 15 ≤ Q))
    (hfour : auxiliaryFour (by omega) rows ≤ fourTarget Q + δ • physicalHamiltonian Q) :
    (1-rowEta rows-threeBodyTail Q-δ) • physicalHamiltonian Q ≤
      physicalHamiltonian Q * physicalHamiltonian Q := by
  have ht := threeTailLift_le (by omega : 4 ≤ Q)
  rw [neg_smul] at ht
  have hh := comparison_additive_step (physical_spin_square_split (by omega : 15 ≤ Q))
    (auxiliary_positive (by omega : 8 ≤ Q) rows) hthree hfour ht
  simpa only [sub_smul,one_smul] using hh

end LaughlinGap.RealOccupation

end

end OAI
