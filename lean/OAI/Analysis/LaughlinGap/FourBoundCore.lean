import Mathlib
import OAI.Analysis.LaughlinGap.Four
import OAI.Analysis.LaughlinGap.FourTransfer

namespace OAI

/-! Four Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

lemma localPair_average {Q L : ℕ} (hQ : 2 ≤ Q) (hL : L ≤ 2*Q-1) :
    ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
      (∑ p : Fin L, (physicalPair Q p.val).transpose * physicalPair Q p.val) =
        (L:ℝ) • physicalHamiltonian Q := by
  have he (p : Fin L) := physicalPair_single_val hQ (show p.val < 2*Q-1 by omega)
  simp only [map_sum,he,← Finset.sum_smul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    smul_smul]
  congr 1
  have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  field_simp

lemma fourAverage_identity (Q D : ℕ) :
    fourAverage Q D 1 = ∑ r : FourCopy D, fourHighestAverage Q D r.val.val r.val.val := by
  simp only [fourAverage,LinearMap.comp_apply,lift_identity,map_sum,fourHighestAverage]

lemma fourAverage_lower {Q D : ℕ} (hQ : 24 ≤ Q) (C : Matrix (FourCopy D) (FourCopy D) ℝ)
    (ρ : ℝ) (h : -ρ • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
        lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) C) :
    -(24*ρ) • physicalHamiltonian Q ≤ ((2*Q-1:ℕ):ℝ) • fourAverage Q D C := by
  have hh := smul_le_smul_of_nonneg_left
    (average_mono (rotationCommutant (fockLowering Q)) h)
    (Nat.cast_nonneg (α := ℝ) (2*Q-1))
  simp only [map_smul] at hh
  rw [smul_comm ((2*Q-1:ℕ):ℝ) (-ρ),localPair_average (by omega : 2 ≤ Q) (by omega)] at hh
  convert hh using 1 <;> simp [smul_smul,mul_comm,fourAverage]

lemma retained_orbitalTriple_count_fin :
    (∑ d : Fin 23, Fintype.card (OrbitalTriple (d.val+1))) = 1222 := by
  simp_rw [orbitalTriple_card]
  norm_num [Fin.sum_univ_succ]

lemma fourAllowance_le {Q : ℕ} (hQ : 24 ≤ Q) :
    ((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1) ≤
      (1222:ℝ) • physicalHamiltonian Q := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun d (_ : d ∈ (Finset.univ : Finset (Fin 23))) =>
    fourHighest_average_bessel (by omega : 2 ≤ Q) (show d.val+1 ≤ Q by omega))
  simpa only [fourAverage_identity,← Finset.smul_sum,← Finset.sum_smul,
    ← Nat.cast_sum,retained_orbitalTriple_count_fin,fourHighestAverage,Nat.cast_ofNat] using hh

noncomputable def retainedFourTarget (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ d : Fin 23, ((4*Q-1-2*(d.val+1):ℕ):ℝ) • fourHighestAverage Q (d.val+1) 1 1

lemma retainedFourTarget_le {Q : ℕ} (hQ : 24 ≤ Q) :
    retainedFourTarget Q ≤ fourTarget Q := fourTarget_retained (by omega) (by omega)

variable {ι : Type*} [Fintype ι]

lemma fourComparison_difference {Q : ℕ} (hQ : 24 ≤ Q) (rows : ι → RowData) (ε : ℝ) :
    ((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) (fourComparison rows ε Q (d.val+1))) =
      retainedFourTarget Q - ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q))
        (∑ r, rowFour (by omega) (rows r)) +
          ε • (((2*Q-1:ℕ):ℝ) • (∑ d : Fin 23, fourAverage Q (d.val+1) 1)) := by
  simp only [fourComparison,map_add,map_sub,map_smul,map_sum,Finset.smul_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,smul_add,smul_sub,
    rowFour_average_retained (by omega : 23 ≤ Q)]
  rw [Finset.sum_comm (f := fun r (d : Fin 23) => _)]
  congr 2
  · unfold retainedFourTarget
    apply Finset.sum_congr rfl
    intro d hd
    rw [smul_smul,fourAverage_copyTarget Q (by omega),
      fourDimensionRatio_eq (by omega : 2 ≤ Q) (by omega)]
    have hn : ((2*Q-1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
    congr 1
    field_simp
  · simp only [smul_smul]
    funext d
    rw [mul_comm]

end LaughlinGap.RealOccupation

end

end OAI
