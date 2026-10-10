import Mathlib
import OAI.Analysis.LaughlinFock.CrossOrbit
import OAI.Analysis.LaughlinFock.FiniteComparison
import OAI.Analysis.LaughlinFock.ThreeOrbit
import OAI.Analysis.LaughlinFock.ThreeTraces

namespace OAI

/-! Three Rows. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem matrix_complete_column_sandwich {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (n : ι → ℕ) (C : ∀ i, Matrix κ (Fin (n i+1)) ℂ)
    (hC : ∑ i, C i * (C i)ᴴ = 1)
    (W : Matrix ν κ ℂ) (M : Matrix κ κ ℂ) :
    W*M*Wᴴ = ∑ i, ∑ j, (W*C i)*((C i)ᴴ*M*C j)*(W*C j)ᴴ := by
  calc
    _ = W * (∑ i, C i * (C i)ᴴ) * M * (∑ j, C j * (C j)ᴴ) * Wᴴ := by
      rw [hC, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [Finset.sum_comm]

 

theorem sectorAverage_of_complete_spin {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] {Q k : ℕ}
    (n : ι → ℕ) (hn : Function.Injective n) (C : ∀ i, Matrix κ (Fin (n i+1)) ℂ)
    (hC : ∑ i, C i * (C i)ᴴ = 1)
    (W : Matrix (SectorOccupation Q k) κ ℂ)
    (hW : ∀ i s, sectorOneBody Q k (spinGenerator Q s)*(W*C i) =
      (W*C i)*spinGenerator (n i) s)
    (M : Matrix κ κ ℂ) :
    sectorAverage Q k (W*M*Wᴴ) =
      ∑ i, (((C i)ᴴ*M*C i).trace / (n i+1:ℂ)) • ((W*C i)*(W*C i)ᴴ) := by
  classical
  rw [matrix_complete_column_sandwich n C hC W M, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum, Finset.sum_eq_single i]
  · exact sectorAverage_spin_mixed_sandwich (W*C i) (W*C i) (hW i) (hW i) _
  · intro j _ hji
    exact sectorAverage_spin_cross_sandwich (fun hij => hji (hn hij).symm)
      (W*C i) (W*C j) (hW i) (hW j) _
  · simp

 
theorem threeSpinColumns_complete {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), threeSpinColumns Q z.val * (threeSpinColumns Q z.val)ᴴ) = 1 := by
  have h := threeSpinProjection_sum Q hQ
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [threeSpinProjection_columns hQ (Nat.le_of_lt_succ (Fin.isLt _))] using h

 

theorem sectorAverage_three_kernel {Q : ℕ} (hQ : 2 ≤ Q)
    (M : Matrix (PairLabel Q × Orbital Q) (PairLabel Q × Orbital Q) ℂ) :
    sectorAverage Q 3 (threeWedgeMatrix Q*M*(threeWedgeMatrix Q)ᴴ) =
      threeWedgeMatrix Q * (∑ z ∈ Finset.range (Q+1),
        ((threeSpinProjection Q z*M).trace / ((3*Q-1-2*z : ℕ) : ℂ)) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ := by
  have hn : Function.Injective (fun z : Fin (Q+1) => 2*Q-2+Q-2*z.val) := by
    intro z w h
    have hz := z.isLt
    have hw := w.isLt
    apply Fin.ext
    dsimp only at h
    omega
  have h := sectorAverage_of_complete_spin _ hn (fun z : Fin (Q+1) => threeSpinColumns Q z.val)
    (threeSpinColumns_complete hQ) (threeWedgeMatrix Q)
    (fun z => threeSpinWedge_intertwines hQ (by have := z.isLt; omega)) M
  rw [h, ← Fin.sum_univ_eq_sum_range, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have hz : z.val ≤ Q := Nat.le_of_lt_succ z.isLt
  have hd : ((2*Q-2+Q-2*z.val : ℕ) : ℂ)+1 = ((3*Q-1-2*z.val : ℕ) : ℂ) := by
    rw [← Nat.cast_add_one]
    congr 1
    omega
  have ht : ((threeSpinColumns Q z.val)ᴴ * M * threeSpinColumns Q z.val).trace =
      (threeSpinProjection Q z.val*M).trace := by
    rw [threeSpinProjection_columns hQ hz, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [hd, ht]
  exact congrArg (_ • ·) (threeSpinWedge_gram hQ hz)

 

theorem fockAverage_rowThreeBody {Q t : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    fockAverage Q (rowThreeBody Q t ℓ rowP (sourceRowI (by omega : 8 ≤ Q))
      (sourceRowJ (by omega : 8 ≤ Q)) a) =
      exteriorLift Q 3 (threeWedgeMatrix Q * (∑ z ∈ Finset.range 16,
        ((rowThreeTrace Q z t ℓ a : ℂ) / ((3*Q-1-2*z : ℕ) : ℂ)) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ) := by
  rw [← sourceRowThreeKernel_lift (by omega : 8 ≤ Q) ht ℓ a,
    fockAverage_exteriorLift, sectorAverage_three_kernel (by omega)]
  congr 2
  congr 1
  calc
    _ = ∑ z ∈ Finset.range (Q+1),
        ((rowThreeTrace Q z t ℓ a : ℂ) / ((3*Q-1-2*z : ℕ) : ℂ)) • threeSpinProjection Q z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [sourceRowThreeKernel_projectionTrace hQ ht (by have := Finset.mem_range.mp hz; omega)]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro z hz hnz
      rw [rowThreeTrace_above_support (by simp only [Finset.mem_range] at hnz; omega) ℓ a]
      simp

theorem spinRatio_eq_dimensions {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    spinRatio Q z = ((3*Q-1-2*z : ℕ) : ℝ) / ((2*Q-1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ 3*Q := by omega
  have h2 : 2*z ≤ 3*Q-1 := by omega
  have h3 : 1 ≤ 2*Q := by omega
  simp only [spinRatio, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

 
theorem fockAverage_rowThreeBody_scaled {Q t : ℕ} (hQ : 16 ≤ Q) (ht : t ≤ 7)
    (ℓ : ℝ) (a : RowEntry t → ℝ) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
      (rowThreeBody Q t ℓ rowP (sourceRowI (by omega : 8 ≤ Q))
        (sourceRowJ (by omega : 8 ≤ Q)) a) =
      exteriorLift Q 3 (threeWedgeMatrix Q * (∑ z ∈ Finset.range 16,
        ((rowThreeTrace Q z t ℓ a / spinRatio Q z : ℝ) : ℂ) •
          threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ) := by
  rw [fockAverage_rowThreeBody hQ ht]
  change ((2*Q-1 : ℕ) : ℂ) • (exteriorLiftLinear Q 3) _ = (exteriorLiftLinear Q 3) _
  rw [← map_smul]
  congr 1
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, Finset.smul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro z hz
  rw [smul_smul, Complex.ofReal_div, spinRatio_eq_dimensions (by omega)
    (by have := Finset.mem_range.mp hz; omega), Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_natCast]
  congr 1
  have hn : ((2*Q-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2*Q-1 ≠ 0 by omega)
  rw [div_div_eq_mul_div]
  ring

 
def averagedRowsFour {ι : Type*} [Fintype ι] {Q : ℕ} (hQ : 8 ≤ Q)
    (rows : ι → ComparisonRow) : FockMatrix Q :=
  ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ i,
    rowFourBody Q rowP (sourceRowI hQ) (sourceRowJ hQ) (rows i).alpha)

 

theorem fockAverage_rowsThreeBody {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q) :
    ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
      (∑ i, rowThreeBody Q (rows i).t.val (rows i).ell rowP
        (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) (rows i).alpha) =
      threeTraceForm rows Q := by
  rw [map_sum, Finset.smul_sum]
  have hi (i : ι) := fockAverage_rowThreeBody_scaled hQ
    (Nat.le_of_lt_succ (rows i).t.isLt) (rows i).ell (rows i).alpha
  simp_rw [hi]
  unfold threeTraceForm rowsThreeTrace
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    exteriorLift_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Finset.sum_div, Complex.ofReal_sum, Finset.sum_smul, exteriorLift_sum,
    Complex.ofReal_div]

 

theorem averagedRows_positive {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q) :
    (rowsEta rows • hamiltonian Q + threeTraceForm rows Q +
      averagedRowsFour (by omega : 8 ≤ Q) rows).PosSemidef := by
  classical
  let F (i : ι) := auxiliaryRow Q (rows i).t.val (rows i).ell rowP
    (sourceRowI (by omega : 8 ≤ Q)) (sourceRowJ (by omega : 8 ≤ Q)) (rows i).alpha
  have hp := fockAverage_posSemidef Q _
    (Matrix.posSemidef_sum Finset.univ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (F i)))
  have h := hp.smul (show (0:ℂ) ≤ ((2*Q-1 : ℕ) : ℂ) by exact_mod_cast Nat.zero_le _)
  dsimp [F] at h
  simp_rw [auxiliaryRow_square] at h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, map_add, map_add,
    smul_add, smul_add, fockAverage_rowsThreeBody rows hQ] at h
  have he : ((2*Q-1 : ℕ) : ℂ) • fockAverage Q (∑ i, rowTwoBody Q (rows i).t.val (rows i).ell) =
      rowsEta rows • hamiltonian Q := by
    rw [map_sum, Finset.smul_sum]
    unfold rowTwoBody rowsEta
    have hh (i : ι) : ((2*Q-1 : ℕ) : ℂ) • fockAverage Q
        ((rows i).ell^2 • ((pairAnnihilator Q (rows i).t.val)ᴴ * pairAnnihilator Q (rows i).t.val)) =
        (rows i).ell^2 • hamiltonian Q := by
      rw [(fockAverage Q).map_smul_of_tower, smul_comm _ ((rows i).ell^2),
        fockAverage_pair_energy_scaled (by omega) (by have := (rows i).t.isLt; omega)]
    simp_rw [hh]
    exact Finset.sum_smul.symm
  rw [he] at h
  exact h

end LaughlinFock
end

end OAI
