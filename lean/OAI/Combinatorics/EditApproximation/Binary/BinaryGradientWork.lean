import OAI.Combinatorics.EditApproximation.Binary.BinaryLogWork

namespace OAI

/-! A bit-operation bound for each actually materialized gradient coordinate. -/

namespace EditApproximation
namespace BinaryFraction

def smoothingStorageBudget (G : ℕ) : ℕ := 3 + 50 * (Nat.size G + 2)

def shiftedStorageBudget (G pointBits : ℕ) : ℕ := 4 * pointBits + 2 * smoothingStorageBudget G + 8

def gradientLogStorageBudget (G pointBits : ℕ) : ℕ :=
  UnreducedRational.logarithmStorageBudget (shiftedStorageBudget G pointBits) (G ^ 60)

def gradientCellBitBudget (G pointBits linearBits : ℕ) : ℕ :=
  let S := smoothingStorageBudget G
  let R := shiftedStorageBudget G pointBits
  let L := gradientLogStorageBudget G pointBits
  (1 + 50 * (2000 * (generalPowerWordBudget (nat G) 50 + 1) ^ 2 + 1)) +
    (4 * S + 3) + 6000 * (pointBits + S + 2) ^ 2 + logarithmBitBudget R (G ^ 60) +
    (6000 * (L + 4) ^ 2 + 1) + 6000 * (linearBits + 2 * L + 9) ^ 2 + Nat.size G + 70

theorem gradientCellWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCellWithWork G linear point i).2 ≤
      gradientCellBitBudget G (point.get i).width (linear.get i).width := by
  let smoothing := powWithWork (nat G) 50
  let shifted := canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1
  let logarithm := logarithmWithWork shifted.1 (G ^ 60)
  let deficit := subWithWork logarithm.1.neg one
  let S := smoothingStorageBudget G
  let R := shiftedStorageBudget G (point.get i).width
  let L := gradientLogStorageBudget G (point.get i).width
  have hsm : smoothing.1.representation.storageBits ≤ S := by
    rw [powWithWork_representation, nat_representation]
    simpa only [UnreducedRational.storageBits_nat, S, smoothingStorageBudget] using
      UnreducedRational.pow_storageBits (UnreducedRational.nat G) 50
  have hsw : smoothing.1.width ≤ S := (powWithWork_width_le_storageBits (nat G) 50).trans hsm
  have his : smoothing.1.invWithWork.1.representation.storageBits ≤ S + 2 := by
    rw [invWithWork_representation]
    exact (UnreducedRational.storageBits_inv _).trans (Nat.add_le_add_right hsm 2)
  have hsi : smoothing.1.invWithWork.1.width ≤ S + 1 :=
    (invWithWork_width smoothing.1).trans (Nat.add_le_add_right hsw 1)
  have hps := representation_storageBits_le (point.get i)
  have hshift : shifted.1.representation.storageBits ≤ R := by
    change (canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1).1.representation.storageBits ≤ R
    rw [canonicalAddWithWork_representation]
    have h := UnreducedRational.storageBits_add (point.get i).representation smoothing.1.invWithWork.1.representation
    dsimp only [R, shiftedStorageBudget]
    omega
  have hshiftw : shifted.1.width ≤ R := (canonicalAddWithWork_self_width _ _).trans hshift
  have hshiftpos : 0 ≤ shifted.1.value := by
    change 0 ≤ (canonicalAddWithWork (point.get i) smoothing.1.invWithWork.1).1.value
    rw [← representation_value, canonicalAddWithWork_representation, invWithWork_representation,
      powWithWork_representation, nat_representation]
    simp only [UnreducedRational.value_add, UnreducedRational.value_inv,
      UnreducedRational.value_pow, UnreducedRational.value_nat, representation_value]
    exact add_nonneg hpoint (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg G) 50))
  have hlogs : logarithm.1.representation.storageBits ≤ L := by
    rw [logarithmWithWork_representation]
    exact (UnreducedRational.logarithm_storageBits_poly shifted.1.representation (G ^ 60) hshiftpos).trans
      (UnreducedRational.logarithmStorageBudget_mono hshift _)
  have hlogw : logarithm.1.width ≤ L := (logarithmWithWork_width_le_storageBits _ _).trans hlogs
  have hdeficit : deficit.1.width ≤ 2 * L + 8 := by
    have hwidth := canonicalAddWithWork_self_width logarithm.1.neg one.neg
    change deficit.1.width ≤ deficit.1.representation.storageBits at hwidth
    rw [subWithWork_representation, neg_representation, one_representation] at hwidth
    have h := UnreducedRational.storageBits_sub logarithm.1.representation.neg UnreducedRational.one
    rw [UnreducedRational.storageBits_neg, UnreducedRational.storageBits_one] at h
    omega
  have csm := powWithWork_cost_general (nat G) 50
  have csi := invWithWork_cost smoothing.1
  have cshift := canonicalAddWithWork_cost (point.get i) smoothing.1.invWithWork.1
    ((point.get i).width + S + 1) (by omega) (by omega)
  have clog := (logarithmWithWork_cost shifted.1 (G ^ 60) hshiftpos).trans
    (logarithmBitBudget_mono hshiftw _)
  have cdef := subWithWork_cost logarithm.1.neg one (L + 3)
    (by rw [neg_width]; omega) (by have h := one_width; omega)
  have cfinal := canonicalAddWithWork_cost deficit.1 (linear.get i)
    ((linear.get i).width + 2 * L + 8) (by omega) (by omega)
  change smoothing.2 + smoothing.1.invWithWork.2 + shifted.2 + logarithm.2 + deficit.2 +
    (canonicalAddWithWork deficit.1 (linear.get i)).2 + Nat.size G + 70 ≤ _
  change _ ≤ (1 + 50 * (2000 * (generalPowerWordBudget (nat G) 50 + 1) ^ 2 + 1)) +
    (4 * S + 3) + 6000 * ((point.get i).width + S + 2) ^ 2 + logarithmBitBudget R (G ^ 60) +
    (6000 * (L + 4) ^ 2 + 1) + 6000 * ((linear.get i).width + 2 * L + 9) ^ 2 + Nat.size G + 70
  change logarithm.2 ≤ logarithmBitBudget R (G ^ 60) at clog
  change deficit.2 ≤ 6000 * (L + 3 + 1) ^ 2 + 1 at cdef
  change smoothing.2 ≤ _ at csm
  nlinarith only [csm, csi, cshift, clog, cdef, cfinal, hsw]

theorem gradientCellBitBudget_mono (G : ℕ) {A B C D : ℕ} (hpoint : A ≤ B) (hlinear : C ≤ D) :
    gradientCellBitBudget G A C ≤ gradientCellBitBudget G B D := by
  have hR : shiftedStorageBudget G A ≤ shiftedStorageBudget G B := by
    unfold shiftedStorageBudget
    omega
  have hL : gradientLogStorageBudget G A ≤ gradientLogStorageBudget G B :=
    UnreducedRational.logarithmStorageBudget_mono hR _
  have hc := logarithmBitBudget_mono hR (G ^ 60)
  have h1 := Nat.mul_self_le_mul_self
    (show A + smoothingStorageBudget G + 2 ≤ B + smoothingStorageBudget G + 2 by omega)
  have h2 := Nat.mul_self_le_mul_self
    (show gradientLogStorageBudget G A + 4 ≤ gradientLogStorageBudget G B + 4 by omega)
  have h3 := Nat.mul_self_le_mul_self
    (show C + 2 * gradientLogStorageBudget G A + 9 ≤ D + 2 * gradientLogStorageBudget G B + 9 by omega)
  simp only [← pow_two] at h1 h2 h3
  unfold gradientCellBitBudget
  dsimp only
  omega

theorem vectorMapWithWork_cost_le {α : Type*} (d : ℕ) (f : Fin d → α × ℕ)
    (C : ℕ) (hC : ∀ i, (f i).2 ≤ C) :
    (vectorMapWithWork d f).2 ≤ d * (C + 6) := by
  simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
    List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs : (∑ i : Fin d, (f i).2) ≤ d * C := by
    calc
      _ ≤ ∑ _ : Fin d, C := Finset.sum_le_sum (fun i _ => hC i)
      _ = d * C := by simp
  nlinarith only [hs]

theorem gradientWithWork_cost {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (P L : ℕ) (hp : ∀ i, 0 ≤ (point.get i).value)
    (hpw : ∀ i, (point.get i).width ≤ P) (hlw : ∀ i, (linear.get i).width ≤ L) :
    (gradientWithWork G linear point).2 ≤ d * (gradientCellBitBudget G P L + 6) := by
  apply vectorMapWithWork_cost_le
  intro i
  exact (gradientCellWithWork_cost G linear point i (hp i)).trans
    (gradientCellBitBudget_mono G (hpw i) (hlw i))

end BinaryFraction
end EditApproximation

end OAI
