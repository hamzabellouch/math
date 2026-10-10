import OAI.Combinatorics.EditApproximation.Queries.QueryGapStateCost
import OAI.Combinatorics.EditApproximation.Binary.BinaryCellGridWork
import OAI.Combinatorics.EditApproximation.Queries.QueryCodeBounds

namespace OAI

namespace EditApproximation.BinaryFraction

def queryRoundedStatesBitBudget (left right exponent B : ℕ) : ℕ :=
  100000 * (32 * B + 210) ^ 2 + queryGapStatesBitBudget left right (32 * B + 200) + exponent + 12

private theorem rounded_square_bound (k c B : ℕ) (hk : k ≤ 32 * B + 210) (hc : c ≤ 5000) :
    c * k ^ 2 ≤ 5000 * (32 * B + 210) ^ 2 :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_left hk 2)

private theorem rounded_spacing_budget_bound (B : ℕ) :
    roundedSpacingBitBudget B ≤ 5000 * (32 * B + 210) ^ 2 := by
  unfold roundedSpacingBitBudget
  nlinarith only [Nat.zero_le B]

private theorem rounded_add_bound (a b B : ℕ)
    (ha : Nat.size a ≤ 32 * B + 200) (hb : Nat.size b ≤ 32 * B + 200) :
    (binaryNaturalAddWithWork a b).2 ≤ 5000 * (32 * B + 210) ^ 2 := by
  have h := binaryNaturalAddWithWork_cost a b
  nlinarith only [h, ha, hb, Nat.zero_le B]

private theorem rounded_sub_bound (a b B : ℕ)
    (ha : Nat.size a ≤ 32 * B + 200) (hb : Nat.size b ≤ 32 * B + 200) :
    (saturatingSubtractWithWork a b).2 ≤ 5000 * (32 * B + 210) ^ 2 := by
  have h := saturatingSubtractWithWork_cost a b
  nlinarith only [h, ha, hb, Nat.zero_le B]

private theorem rounded_mul_bound (a b B : ℕ)
    (ha : Nat.size a ≤ 32 * B + 200) (hb : Nat.size b ≤ 32 * B + 200) :
    (binaryNaturalMulWithWork a b).2 ≤ 5000 * (32 * B + 210) ^ 2 := by
  have h := queryNaturalMul_cost a b (32 * B + 200) ha hb
  nlinarith only [h, Nat.zero_le B]

theorem queryGroupRoundedStatesWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent B left right : ℕ) (cell : ℕ × ℕ) (i : Fin M) (h : BinaryFraction)
    (hB : 4 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hc : Nat.size cell.1 ≤ B)
    (he : exponent + 1 ≤ B) (hh : h.width ≤ B)
    (hleft : 2 * (12 * b) / groupRoundSpacing exponent h.value + 2 ≤ left)
    (hright : 2 * ⌈2 * h.value⌉₊ / groupRoundSpacing exponent h.value + 2 ≤ right) :
    (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1.length ≤ left * right ∧
    (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).2 ≤
      queryRoundedStatesBitBudget left right exponent B := by
  let theta := inversePowerTwo exponent
  let spacing := roundedSpacingWithWork theta h
  let child := sourceChildWithWork parent i
  let offset := saturatingSubtractWithWork child.1.lo parent.lo
  let base := canonicalMulWithWork (nat cell.1) theta
  let position := canonicalMulWithWork base.1 (nat b)
  let floor := naturalFloorWithWork position.1
  let anchor := binaryNaturalAddWithWork (bitWordValue floor.1) (bitWordValue offset.1)
  let radius := binaryNaturalMulWithWork 12 b
  let length := saturatingSubtractWithWork child.1.hi child.1.lo
  let twice := canonicalMulWithWork (nat 2) h
  let gap := naturalCeilingWithWork twice.1
  let C := 32 * B + 200
  have ht : theta.width ≤ B := by rw [inversePowerTwo_width]; exact he
  have hsp := roundedSpacingWithWork_bounds theta h B ht hh
  have hchild := sourceChildWithWork_cost parent i B hnx hM
  have hcl : Nat.size child.1.lo ≤ B := (Nat.size_le_size (child.1.ordered.trans child.1.valid)).trans hnx
  have hch : Nat.size child.1.hi ≤ B := (Nat.size_le_size child.1.valid).trans hnx
  have hplo : Nat.size parent.lo ≤ B := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
  have hoff : Nat.size (bitWordValue offset.1) ≤ B := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans hcl
  have hbase := canonicalMulWithWork_width (nat cell.1) theta (B + 2)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hpos := canonicalMulWithWork_width base.1 (nat b) (4 * B + 10)
    (by change base.1.width ≤ _ at hbase; omega) ((nat_width_le _).trans (by omega))
  have hfloor := naturalFloorWithWork_bounds position.1
  have hfsize : Nat.size (bitWordValue floor.1) ≤ 16 * B + 42 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans
      (hfloor.1.trans (by change position.1.width ≤ _ at hpos; omega))
  have hasize : Nat.size (bitWordValue anchor.1) ≤ C := by
    rw [binaryNaturalAddWithWork_value]
    apply (binaryNaturalAdd_size_le _ _).trans
    dsimp only [C]
    omega
  have hrsize : Nat.size (bitWordValue radius.1) ≤ C := by
    rw [binaryNaturalMulWithWork_value]
    have htwelve : Nat.size 12 = 4 := by decide
    have hp := queryNaturalMul_size 12 b
    rw [htwelve] at hp
    dsimp only [C]
    omega
  have hlsize : Nat.size (bitWordValue length.1) ≤ C := by
    rw [saturatingSubtractWithWork_value]
    exact (Nat.size_le_size (Nat.sub_le _ _)).trans (hch.trans (by dsimp only [C]; omega))
  have htwice := canonicalMulWithWork_width (nat 2) h B
    (by exact (nat_width_le 2).trans (by rw [show Nat.size 2 = 2 by decide]; omega)) hh
  have hgsize : Nat.size (bitWordValue gap.1) ≤ C :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans
      ((naturalCeilingWithWork_length twice.1).trans (by
        change twice.1.width ≤ _ at htwice
        dsimp only [C]
        omega))
  have hspsize : Nat.size (bitWordValue spacing.1) ≤ C :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans (hsp.1.trans (by
      unfold roundedSpacingWordBudget
      dsimp only [C]
      omega))
  have hspvalue : bitWordValue spacing.1 = groupRoundSpacing exponent h.value := by
    simp only [spacing, roundedSpacingWithWork_value, theta, inversePowerTwo_value, groupRoundSpacing]
  have hradvalue : bitWordValue radius.1 = 12 * b := binaryNaturalMulWithWork_value _ _
  have hgapvalue : bitWordValue gap.1 = ⌈2 * h.value⌉₊ := by
    simp only [gap, naturalCeilingWithWork_value, twice, canonicalMulWithWork_value, nat_value, Nat.cast_ofNat]
  have hstates := queryGapStatesWithWork_bounds ny (bitWordValue spacing.1) (bitWordValue anchor.1)
    (bitWordValue radius.1) (bitWordValue length.1) (bitWordValue gap.1) left right C
    (roundedSpacingWithWork_pos theta h) (by dsimp only [C]; omega) hspsize hasize hrsize hlsize hgsize
    (by simpa only [hspvalue, hradvalue] using hleft) (by simpa only [hspvalue, hgapvalue] using hright)
  have hbasec := canonicalMulWithWork_cost (nat cell.1) theta (B + 2)
    ((nat_width_le _).trans (by omega)) (by omega)
  have hposc := canonicalMulWithWork_cost base.1 (nat b) (4 * B + 10)
    (by change base.1.width ≤ _ at hbase; omega) ((nat_width_le _).trans (by omega))
  have hfloorc := hfloor.2.trans (Nat.mul_le_mul_left 200
    (Nat.pow_le_pow_left (by change position.1.width ≤ _ at hpos; omega : position.1.width + 1 ≤ 16 * B + 43) 2))
  have htc := canonicalMulWithWork_cost (nat 2) h B
    (by exact (nat_width_le 2).trans (by rw [show Nat.size 2 = 2 by decide]; omega)) hh
  have hgc := (naturalCeilingWithWork_cost twice.1).trans (Nat.mul_le_mul_left 500
    (Nat.pow_le_pow_left (by change twice.1.width ≤ _ at htwice; omega : twice.1.width + 1 ≤ 4 * B + 3) 2))
  have hs1 : spacing.2 ≤ 5000 * (32 * B + 210) ^ 2 := hsp.2.trans (rounded_spacing_budget_bound B)
  have hs2 : child.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    hchild.trans (rounded_square_bound (B + 3) 2200 B (by omega) (by decide))
  have hs3 : offset.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    rounded_sub_bound child.1.lo parent.lo B (by omega) (by omega)
  have hs4 : base.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    hbasec.trans (rounded_square_bound (B + 2 + 1) 2000 B (by omega) (by decide))
  have hs5 : position.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    hposc.trans (rounded_square_bound (4 * B + 10 + 1) 2000 B (by omega) (by decide))
  have hs6 : floor.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    hfloorc.trans (rounded_square_bound (16 * B + 43) 200 B (by omega) (by decide))
  have hs7 : anchor.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    rounded_add_bound (bitWordValue floor.1) (bitWordValue offset.1) B (by omega) (by omega)
  have hs8 : radius.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    rounded_mul_bound 12 b B (by rw [show Nat.size 12 = 4 by decide]; omega) (by omega)
  have hs9 : length.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    rounded_sub_bound child.1.hi child.1.lo B (by omega) (by omega)
  have hs10 : twice.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    htc.trans (rounded_square_bound (B + 1) 2000 B (by omega) (by decide))
  have hs11 : gap.2 ≤ 5000 * (32 * B + 210) ^ 2 :=
    hgc.trans (rounded_square_bound (4 * B + 3) 500 B (by omega) (by decide))
  have hsetup : spacing.2 + child.2 + offset.2 + base.2 + position.2 + floor.2 + anchor.2 +
      radius.2 + length.2 + twice.2 + gap.2 ≤ 100000 * (32 * B + 210) ^ 2 := by omega
  constructor
  · simpa only [queryGroupRoundedStatesWithWork] using hstates.1
  · simpa only [queryGroupRoundedStatesWithWork, queryRoundedStatesBitBudget, C,
      Nat.add_assoc, Nat.reduceAdd] using
      Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hsetup hstates.2) exponent) 12

end EditApproximation.BinaryFraction

end OAI
