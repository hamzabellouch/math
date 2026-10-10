import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.SparseScalarCost
import OAI.Analysis.MatrixSigning.Optimization.TerminalWitnessMachine

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01 KS.W07

theorem raw_length_le (n : ℕ) : (Computability.encodeNat n).length ≤ n := by
  rw [encodeNat_length_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem zero_payload_length (n : ℕ) :
    ((TerminalVectorReplace.zeroPayloads n).flatMap KS.W01.frame).length = 11*n := by
  rw [← TerminalVectorReplace.zeroTape_eq,KS.W11.ZeroArrayConstructor.zeroTape_length,
    KS.W11.ZeroArrayConstructor.zeroFrame_length]
  omega

theorem head_payload_length (n : ℕ) (c : ℚ) :
    (((TerminalVectorReplace.zeroPayloads (n+1)).set 0 (encodeRat c)).flatMap KS.W01.frame).length =
      2*ratLength c+1+11*n := by
  have he : ((TerminalVectorReplace.zeroPayloads (n+1)).set 0 (encodeRat c)).flatMap KS.W01.frame =
      KS.W01.frame (encodeRat c) ++ (TerminalVectorReplace.zeroPayloads n).flatMap KS.W01.frame := by
    simp [TerminalVectorReplace.zeroPayloads,List.replicate_succ]
  rw [he,List.length_append,KS.W01.length_frame,zero_payload_length]
  rfl

theorem assemblyTicks_linear (n : ℕ) (j : Fin (n+1)) (c : ℚ) :
    TerminalSparseAssembly.ticks (n+1) j.val c ≤ 100*((n+1)+ratLength c+1) := by
  have hn := raw_length_le (n+1)
  have hj := raw_length_le j.val
  have hji := j.isLt
  have hone : TerminalVectorReplace.oneFrame.length = 15 := by decide
  unfold TerminalSparseAssembly.ticks TerminalSparseAssembly.headTicks TerminalZeroVector.ticks
  simp only [zero_payload_length,head_payload_length,hone,KS.W01.length_frame]
  dsimp only [ratLength]
  omega

theorem coefficient_length (a b : ℚ) :
    ratLength (SparseScalarNodes.coefficient a b) ≤ 80*(ratLength a+ratLength b+10) := by
  have h1 := ratLength_add_le a 1
  have h2 := ratLength_mul_le 2 b
  have h3 := ratLength_neg_le (a+1)
  have h4 := SparseScalarNodes.ratLength_div_le (-(a+1)) (2*b)
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  rw [l1] at h1
  rw [l2] at h2
  change ratLength (-(a+1)/(2*b)) ≤ _
  omega

theorem cleanupTicks_linear {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    KS.W04.CleanRationalCompare.clearListTicks SparseCoefficientStage.cleanupPorts
      (SparseCoefficientStage.after (collected saved M j)
        (DenseRatMatrix.decode M j j) (DenseRatMatrix.decode M 0 j)) ≤
      300*(ratLength (DenseRatMatrix.decode M j j)+ratLength (DenseRatMatrix.decode M 0 j)+j.val+1) := by
  let a := DenseRatMatrix.decode M j j
  let b := DenseRatMatrix.decode M 0 j
  have h1 := ratLength_add_le a 1
  have h2 := ratLength_mul_le 2 b
  have h3 := ratLength_neg_le (a+1)
  have hj := raw_length_le j.val
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  rw [l1] at h1
  rw [l2] at h2
  change (ratLength a+1) + ((ratLength b+1) + ((ratLength (a+1)+1) +
    ((ratLength (2*b)+1) + ((ratLength (1 : ℚ)+1) + ((ratLength (2 : ℚ)+1) +
    ((ratLength (-(a+1))+1) + ((Computability.encodeNat j.val).length+1+1))))))) ≤
      300*(ratLength a+ratLength b+j.val+1)
  omega

theorem ticks_polynomial {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (B L : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^B)
    (hn : n+1 ≤ L) (hB : B ≤ L) (j : Fin (n+1)) :
    ticks saved M B j ≤ 1000000000000000000*(L+1)^3 := by
  let a := DenseRatMatrix.decode M j j
  let b := DenseRatMatrix.decode M 0 j
  have la : ratLength a ≤ 4*L+7 := by
    have h := ratLength_le_of_parts a B B (hnum j j) (hden j j)
    omega
  have lb : ratLength b ≤ 4*L+7 := by
    have h := ratLength_le_of_parts b B B (hnum 0 j) (hden 0 j)
    omega
  have lj := raw_length_le j.val
  have ln := raw_length_le (n+1)
  have hj := j.isLt
  have lp : L+1 ≤ (L+1)^3 := Nat.le_self_pow (by decide) _
  have hread : (n+1+1)^2*(B+1) ≤ (L+1)^3 := by
    calc
      _ ≤ (L+1)^2*(L+1) := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
      _ = (L+1)^3 := by ring
  have hcollect : collectTicks saved M B j ≤ 100000*(L+1)^3 := by
    unfold collectTicks TerminalReadStage.readTicks KS.W07.SchurReadStage.prepareTicks
    simp [TerminalReadStage.ports,KS.W07.SchurReadStage.rowSource,KS.W07.SchurReadStage.colSource,inputState]
    change ratLength (DenseRatMatrix.decode M j j) ≤ _ at la
    change ratLength (DenseRatMatrix.decode M 0 j) ≤ _ at lb
    nlinarith [Nat.mul_le_mul_left 1024 hread]
  have hbase : 200*(ratLength a+ratLength b+1) ≤ 3000*(L+1) := by omega
  have hscalar := (SparseScalarNodes.ticks_polynomial a b).trans
    (Nat.mul_le_mul_left 3000000 (Nat.pow_le_pow_left hbase 3))
  have hclean := cleanupTicks_linear saved M j
  have hcoeff := coefficient_length a b
  have hassemble := assemblyTicks_linear n j (coefficient M j)
  unfold ticks scalarTicks SparseCoefficientStage.ticks
  change collectTicks saved M B j + (SparseScalarNodes.ticks a b + _ + _) ≤ _
  change ratLength (coefficient M j) ≤ _ at hcoeff
  rw [mul_pow] at hscalar
  norm_num only [show (3000 : ℕ)^3 = 27000000000 by decide] at hscalar
  dsimp only [a,b] at la lb hscalar hcoeff ⊢
  omega

end KS.W19.TerminalWitnessMachine

end

end OAI
