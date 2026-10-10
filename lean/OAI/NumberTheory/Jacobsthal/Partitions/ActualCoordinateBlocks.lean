import Mathlib
import OAI.NumberTheory.Jacobsthal.Primes.OriginalPrimeBlocks

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceEffective

noncomputable def intervalK (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) : ℕ :=
  ((-(C0 : ZMod p))*(↑((ZMod.unitOfCoprime H hHp)⁻¹) : ZMod p)).val

noncomputable def intervalM0 (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) : ℤ :=
  (C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ))/(p : ℤ)

theorem intervalK_lt (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    intervalK p H hHp C0 < p := ZMod.val_lt _

theorem interval_numerator_dvd (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    (p : ℤ) ∣ C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,intervalK,ZMod.natCast_zmod_val]
  have hu : (H : ZMod p)*(↑((ZMod.unitOfCoprime H hHp)⁻¹) : ZMod p) = 1 := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime H hHp).mul_inv
  calc
    _ = (C0 : ZMod p)-(C0 : ZMod p)*((H : ZMod p)*↑((ZMod.unitOfCoprime H hHp)⁻¹)) := by ring
    _ = 0 := by rw [hu];ring

theorem intervalM0_identity (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    (p : ℤ)*intervalM0 p H hHp C0 = C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ) := by
  rw [intervalM0,mul_comm]
  exact Int.ediv_mul_cancel (interval_numerator_dvd p H hHp C0)

theorem intervalM0_modEq (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) :
    Int.ModEq (H : ℤ) ((p : ℤ)*intervalM0 p H hHp C0) C0 := by
  rw [intervalM0_identity]
  change (C0+(H : ℤ)*(intervalK p H hHp C0 : ℤ))%(H : ℤ) = C0%(H : ℤ)
  simp

theorem intervalM0_bounds (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) (hH : 0 < H) :
    (C0 : ℝ)/(p : ℝ) ≤ (intervalM0 p H hHp C0 : ℝ) ∧
      (intervalM0 p H hHp C0 : ℝ) < (C0 : ℝ)/(p : ℝ)+(H : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hk0 : (0 : ℝ) ≤ intervalK p H hHp C0 := Nat.cast_nonneg _
  have hkp : (intervalK p H hHp C0 : ℝ) < p := by exact_mod_cast intervalK_lt p H hHp C0
  have he : (p : ℝ)*(intervalM0 p H hHp C0 : ℝ) = (C0 : ℝ)+(H : ℝ)*(intervalK p H hHp C0 : ℝ) := by
    exact_mod_cast intervalM0_identity p H hHp C0
  have hd : (C0 : ℝ)/(p : ℝ)*(p : ℝ) = C0 := div_mul_cancel₀ _ hp.ne'
  constructor
  · apply (div_le_iff₀ hp).mpr
    nlinarith
  · have hmul := mul_lt_mul_of_pos_left hkp hH'
    nlinarith

theorem intervalM0_unique (p H : ℕ) [NeZero p] (hHp : H.Coprime p) (C0 : ℤ) (hH : 0 < H)
    (x : ℤ) (hx : (C0 : ℝ)/(p : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) < (C0 : ℝ)/(p : ℝ)+(H : ℝ))
    (hcong : Int.ModEq (H : ℤ) ((p : ℤ)*x) C0) : x = intervalM0 p H hHp C0 := by
  have he := hcong.trans (intervalM0_modEq p H hHp C0).symm
  have hem : (p : ZMod H)*(x : ZMod H) = (p : ZMod H)*(intervalM0 p H hHp C0 : ZMod H) := by
    simpa only [Int.cast_mul,Int.cast_natCast] using (ZMod.intCast_eq_intCast_iff _ _ _).mpr he
  let v := ZMod.unitOfCoprime p hHp.symm
  have he' := congrArg (fun y : ZMod H => (↑(v⁻¹) : ZMod H)*y) hem
  have hu : (↑(v⁻¹) : ZMod H)*(p : ZMod H) = 1 := by
    simpa only [v,ZMod.coe_unitOfCoprime] using v.inv_mul
  have hxm : (x : ZMod H) = (intervalM0 p H hHp C0 : ZMod H) := by
    simpa only [← mul_assoc,hu,one_mul] using he'
  have hdiv := ((ZMod.intCast_eq_intCast_iff _ _ _).mp hxm).dvd
  have hm := intervalM0_bounds p H hHp C0 hH
  have habs : |((intervalM0 p H hHp C0-x : ℤ) : ℝ)| < (H : ℝ) := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have hnat : (intervalM0 p H hHp C0-x).natAbs < (H : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    have hnatR : ((intervalM0 p H hHp C0-x).natAbs : ℝ) < (H : ℝ) := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using habs
    exact_mod_cast hnatR
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hnat
  omega

end ErdosVarianceEffective



namespace ErdosLargeHeightBlocks


theorem actual_m0_block_interval (C0 : ℤ) (R xi : ℝ) (H i p : ℕ) [NeZero p]
    (hR : 0 < R) (hxi : 0 < xi) (hH : 0 < H) (hHp : H.Coprime p)
    (hp : p ∈ blockPrimes C0 R xi H i) :
    (ErdosVarianceEffective.intervalM0 p H hHp C0 : ℝ) ∈
      Set.Ico (coordinateLower C0 R xi H i) (coordinateUpper C0 R xi H i) ∧
      coordinateUpper C0 R xi H i-coordinateLower C0 R xi H i ≤ 2*(H : ℝ) := by
  have hb := (mem_blockPrimes C0 R xi H i p hR hxi).mp hp
  have hm := ErdosVarianceEffective.intervalM0_bounds p H hHp C0 hH
  exact ⟨block_coordinate_containment C0 R xi H i hR hxi p _ hb.2.1.le hb.2.2 hm.1 hm.2,
    block_coordinate_width C0 R xi H i hR hxi hH⟩

theorem actual_large_height_blocks (C0 : ℤ) (R xi Z : ℝ) (H : ℕ)
    (hR : 0 < R) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hH : 0 < H) (hZ : 2 ≤ Z)
    (hsize : max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ Z^12) :
    0 < blockCount C0 R xi H ∧ (blockCount C0 R xi H : ℝ) ≤ Z^13 ∧
    (Finset.univ : Finset (Fin (blockCount C0 R xi H))).biUnion
      (fun i => blockPrimes C0 R xi H i) = ErdosInversePrimeBin.primeBin R xi ∧
    Pairwise (fun i j : Fin (blockCount C0 R xi H) =>
      Disjoint (blockPrimes C0 R xi H i) (blockPrimes C0 R xi H j)) ∧
    (∑ i : Fin (blockCount C0 R xi H),
      (blockRight C0 R xi H i-blockLeft C0 R xi H i)) = xi*R ∧
    ∀ (i : Fin (blockCount C0 R xi H)) (p : ℕ) [NeZero p] (hHp : H.Coprime p),
      p ∈ blockPrimes C0 R xi H i →
      (ErdosVarianceEffective.intervalM0 p H hHp C0 : ℝ) ∈
        Set.Ico (coordinateLower C0 R xi H i) (coordinateUpper C0 R xi H i) ∧
      coordinateUpper C0 R xi H i-coordinateLower C0 R xi H i ≤ 2*(H : ℝ) := by
  refine ⟨blockCount_pos C0 R xi H,blockCount_source_bound C0 R xi Z H hR hxi.le hxi1 hH hZ hsize,
    block_partition C0 R xi H hR hxi,block_pairwise_disjoint C0 R xi H hR hxi,
    block_width_sum C0 R xi H,?_⟩
  intro i p instP hHp hp
  exact actual_m0_block_interval C0 R xi H i p hR hxi hH hHp hp

end ErdosLargeHeightBlocks


end Erdos970

end OAI
