import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionContextCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionPassCells
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedPreparedCompressionPass

namespace OAI

/-! # Prepaid four-context compression setup and its live data -/

namespace LowSpaceSubsetSum.CompressionPreparedCells

open CompressionPassCells (Fits Ready)
open PreparedCompressionPass (Arrays)
variable {n : ℕ}

theorem context_fits (left right : Array ℤ) (P : ℤ) (hP : 0 < P) (mode : FilteredStream.Mode)
    (C : ℕ) (hL : left.size ≤ C) (hR : right.size ≤ C) (hC : C ≤ 2^n) :
    Fits n C (CompressionContextCells.build left right P hP mode).1.1 := by
  rw [congrArg Prod.fst (CompressionContextCells.build_value left right P hP mode)]
  constructor
  · change (CompressionContext.sort P right).1.size ≤ C
    rwa [CompressionContext.sort_size]
  · change Nat.clog 2 left.size ≤ n
    exact Nat.clog_le_of_le_pow (hL.trans hC)
  · change 2^(Nat.clog 2 left.size+1) ≤ 4*(C+1)
    have h := Tournament.padded_nodes_le left.size
      (Tournament.build (fun _ : Unit => (0 : ℤ)) (Nat.clog 2 left.size) (fun _ => none))
    rw [Tournament.nodes_exact] at h
    exact h.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hL 1))

def prepare (A : Arrays) (P t z : ℤ) (hP : 0 < P) :
    (BudgetedCompressionPass.Data P t z × ℕ) × ℕ :=
  let a := CompressionContextCells.build (A.first 0) (A.second 0) P hP .direct
  let b := CompressionContextCells.build (A.first 1) (A.second 1) P hP (.complementary z)
  let c := CompressionContextCells.build (A.first 2) (A.second 2) P hP .direct
  let d := CompressionContextCells.build (A.first 3) (A.second 3) P hP (.complementary (t-z))
  let out : BudgetedCompressionPass.Data P t z :=
    ⟨a.1.1,b.1.1,c.1.1,d.1.1,
      (A.first 0).size*(A.second 0).size,(A.first 1).size*(A.second 1).size,
      (A.first 2).size*(A.second 2).size,(A.first 3).size*(A.second 3).size⟩
  ((out,a.1.2+b.1.2+c.1.2+d.1.2+16),a.2+b.2+c.2+d.2+
    CompressionPassCells.resident out+4*PreparedCompressionPass.size A+64)

theorem prepare_value (A : Arrays) (P t z : ℤ) (hP : 0 < P) :
    (prepare A P t z hP).1 = PreparedCompressionPass.prepare A P t z hP := by
  simp only [prepare,CompressionContextCells.build_value,PreparedCompressionPass.prepare]

theorem prepare_ready (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (C : ℕ) (hL : ∀ i, (A.first i).size ≤ C) (hR : ∀ i, (A.second i).size ≤ C) (hC : C ≤ 2^n) :
    Ready n C (prepare A P t z hP).1.1 := by
  constructor
  · exact context_fits _ _ _ _ _ C (hL 0) (hR 0) hC
  · exact context_fits _ _ _ _ _ C (hL 1) (hR 1) hC
  · exact context_fits _ _ _ _ _ C (hL 2) (hR 2) hC
  · exact context_fits _ _ _ _ _ C (hL 3) (hR 3) hC

theorem arrays_size (A : Arrays) (C : ℕ) (hL : ∀ i, (A.first i).size ≤ C)
    (hR : ∀ i, (A.second i).size ≤ C) : PreparedCompressionPass.size A ≤ 8*C+1 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Nat.add_le_add (hL i) (hR i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  unfold PreparedCompressionPass.size
  omega

theorem prepare_cells (I : Instance n) (hn : 10000 ≤ n) (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (C : ℕ) (hL : ∀ i, (A.first i).size ≤ C) (hR : ∀ i, (A.second i).size ≤ C) (hC : C ≤ 2^n) :
    (prepare A P t z hP).2 ≤ inputScale I^7*(C+1) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have ha := CompressionContextCells.build_cells I hn (A.first 0) (A.second 0) P hP .direct C (hL 0) (hR 0) hC
  have hb := CompressionContextCells.build_cells I hn (A.first 1) (A.second 1) P hP (.complementary z)
    C (hL 1) (hR 1) hC
  have hc := CompressionContextCells.build_cells I hn (A.first 2) (A.second 2) P hP .direct C (hL 2) (hR 2) hC
  have hd := CompressionContextCells.build_cells I hn (A.first 3) (A.second 3) P hP (.complementary (t-z))
    C (hL 3) (hR 3) hC
  have hready := prepare_ready A P t z hP C hL hR hC
  have hresident := CompressionPassCells.resident_bound C (prepare A P t z hP).1.1 hready
  have hsize := arrays_size A C hL hR
  have hlarge : 1024 ≤ u^6 := by
    have hp : u ≤ u^6 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 6)
    omega
  have hm : 6*u^6*(C+1) ≤ u^7*(C+1) := by
    apply Nat.mul_le_mul_right
    calc
      _ ≤ u*u^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change _ ≤ u^7*(C+1)
  change _+_+_+_+CompressionPassCells.resident (prepare A P t z hP).1.1+
    4*PreparedCompressionPass.size A+64 ≤ _
  calc
    _ ≤ 6*u^6*(C+1) := by nlinarith only [ha,hb,hc,hd,hresident,hsize,hlarge]
    _ ≤ _ := hm

def run (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P) (budget : ℕ) :=
  if BudgetedPreparedCompressionPass.charge I A ≤ budget then
    let prep := prepare A P t z hP
    let out := CompressionPassCells.run I C B prep.1.1
      (budget-BudgetedPreparedCompressionPass.charge I A)
    ((out.1.1,(prep.1.2+1)+out.1.2),prep.2+out.2+4*PreparedCompressionPass.size A+64)
  else ((none,1),4*PreparedCompressionPass.size A+16)

theorem value (I : Instance n) (C B : ℕ) (A : Arrays) (P t z : ℤ) (hP : 0 < P) (budget : ℕ) :
    (run I C B A P t z hP budget).1 = BudgetedPreparedCompressionPass.run I C B A P t z hP budget := by
  simp only [run,prepare_value,CompressionPassCells.value,BudgetedPreparedCompressionPass.run,
    BudgetedSeparatorCall.run]
  split <;> rfl

theorem cells (I : Instance n) (hn : 10000 ≤ n) (C B : ℕ) (A : Arrays)
    (P t z : ℤ) (hP : 0 < P) (budget : ℕ) (hB : B ≤ C)
    (hL : ∀ i, (A.first i).size ≤ C) (hR : ∀ i, (A.second i).size ≤ C) (hC : C ≤ 2^n) :
    (run I C B A P t z hP budget).2 ≤ inputScale I^8*(C+1) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hp := prepare_cells I hn A P t z hP C hL hR hC
  have hs := arrays_size A C hL hR
  have hr := CompressionPassCells.cells I C B (prepare A P t z hP).1.1
    (budget-BudgetedPreparedCompressionPass.charge I A) hn hB (prepare_ready A P t z hP C hL hR hC)
  have h67 : u^6 ≤ u^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have hlarge : 100 ≤ u^7 := by
    have hp : u ≤ u^7 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ u by omega) (by decide : 1 ≤ 7)
    omega
  have hm : 3*u^7*(C+1) ≤ u^8*(C+1) := by
    apply Nat.mul_le_mul_right
    calc
      _ ≤ u*u^7 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hmul := Nat.mul_le_mul_right (C+1) h67
  change _ ≤ u^8*(C+1)
  unfold run
  split <;> dsimp only <;> nlinarith only [hp,hs,hr,hlarge,hm,hmul]

end LowSpaceSubsetSum.CompressionPreparedCells

end OAI
