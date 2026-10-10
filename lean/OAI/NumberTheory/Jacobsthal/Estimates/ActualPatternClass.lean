import OAI.NumberTheory.Jacobsthal.Estimates.SmallModelSourceScales

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceSmallModel
open ErdosHyperbolaError

noncomputable def coordinateUnit (w : ℝ) (H : ℕ) (m : ℤ) (hm : m.natAbs.Coprime H) :
    (ZMod (H*divisorModulus w H))ˣ :=
  ZMod.unitOfIsCoprime m (by
    have hgm : Int.gcd m (H : ℤ) = 1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hm.gcd_eq_one
    have hh := source_product_coprime H (divisorModulus w H) (divisorModulus_dvd_H w H) m 0 hgm
    simpa only [mul_zero,add_zero] using hh)

noncomputable def liftedNumeratorUnit (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (k : ZMod (divisorModulus w H)) :
    (ZMod (H*divisorModulus w H))ˣ :=
  ZMod.unitOfIsCoprime (C0+(H : ℤ)*(k.val : ℤ))
    (source_product_coprime H (divisorModulus w H) (divisorModulus_dvd_H w H) C0 k.val hC0)

noncomputable def restrictionUnit (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H)
    (k : ZMod (divisorModulus w H)) : (ZMod (H*divisorModulus w H))ˣ :=
  liftedNumeratorUnit w H C0 hC0 k*(coordinateUnit w H m hm)⁻¹

noncomputable def patternClass (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H) (s : Pattern w H) : ℕ :=
  (Nat.chineseRemainder (effective_pattern_coprime w H)
    (restrictionUnit w H C0 hC0 m hm s.2).val.val s.1.val.val).val

theorem patternClass_components (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H) (s : Pattern w H) :
    Nat.ModEq (H*divisorModulus w H) (patternClass w H C0 hC0 m hm s)
      (restrictionUnit w H C0 hC0 m hm s.2).val.val ∧
    Nat.ModEq (coprimeModulus w H) (patternClass w H C0 hC0 m hm s) s.1.val.val :=
  (Nat.chineseRemainder (effective_pattern_coprime w H)
    (restrictionUnit w H C0 hC0 m hm s.2).val.val s.1.val.val).property

theorem patternClass_coprime (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H) (s : Pattern w H) :
    (patternClass w H C0 hC0 m hm s).Coprime (H*divisorModulus w H*coprimeModulus w H) := by
  have hh := patternClass_components w H C0 hC0 m hm s
  have h0 : (patternClass w H C0 hC0 m hm s).Coprime (H*divisorModulus w H) := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hh.1,ZMod.natCast_zmod_val]
    exact (restrictionUnit w H C0 hC0 m hm s.2).isUnit
  have h1 : (patternClass w H C0 hC0 m hm s).Coprime (coprimeModulus w H) := by
    apply (ZMod.isUnit_iff_coprime _ _).mp
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hh.2,ZMod.natCast_zmod_val]
    exact s.1.isUnit
  exact h0.mul_right h1

end ErdosVarianceSmallModel

end

section

namespace ErdosVarianceSmallModel

theorem actual_pattern_class (w : ℝ) (H : ℕ) [NeZero H] (C0 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (m : ℤ) (hm : m.natAbs.Coprime H)
    (s : Pattern w H) (p k : ℕ)
    (hEquation : (p : ℤ)*m = C0+(H : ℤ)*(k : ℤ))
    (hp1 : (p : ZMod (coprimeModulus w H)) = (s.1 : ZMod (coprimeModulus w H)))
    (hk0 : (k : ZMod (divisorModulus w H)) = s.2) :
    Int.ModEq ((H*divisorModulus w H*coprimeModulus w H : ℕ) : ℤ)
      (p : ℤ) (patternClass w H C0 hC0 m hm s : ℤ) := by
  have hkNat : Nat.ModEq (divisorModulus w H) k s.2.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hk0
  have hkInt := Int.natCast_modEq_iff.mpr hkNat
  have hlift : Int.ModEq ((H : ℤ)*(divisorModulus w H : ℤ))
      ((H : ℤ)*(k : ℤ)) ((H : ℤ)*(s.2.val : ℤ)) := hkInt.mul_left'
  have hpm : Int.ModEq ((H*divisorModulus w H : ℕ) : ℤ) ((p : ℤ)*m)
      (C0+(H : ℤ)*(s.2.val : ℤ)) := by
    simpa only [Nat.cast_mul,← hEquation] using hlift.add_left C0
  have hpmZ : (p : ZMod (H*divisorModulus w H))*(m : ZMod (H*divisorModulus w H)) =
      (liftedNumeratorUnit w H C0 hC0 s.2 : ZMod (H*divisorModulus w H)) := by
    simpa only [liftedNumeratorUnit,ZMod.coe_unitOfIsCoprime,Int.cast_mul,Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hpm
  have hminv : (m : ZMod (H*divisorModulus w H))*
      (↑((coordinateUnit w H m hm)⁻¹) : ZMod (H*divisorModulus w H)) = 1 := by
    simpa only [coordinateUnit,ZMod.coe_unitOfIsCoprime] using (coordinateUnit w H m hm).mul_inv
  have hmul := congrArg (fun x : ZMod (H*divisorModulus w H) =>
    x*(↑((coordinateUnit w H m hm)⁻¹) : ZMod (H*divisorModulus w H))) hpmZ
  have hpUnit : (p : ZMod (H*divisorModulus w H)) =
      (restrictionUnit w H C0 hC0 m hm s.2 : ZMod (H*divisorModulus w H)) := by
    simpa only [mul_assoc,hminv,mul_one,restrictionUnit,Units.val_mul] using hmul
  have hp0 : Nat.ModEq (H*divisorModulus w H) p (restrictionUnit w H C0 hC0 m hm s.2).val.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hpUnit
  have hp1' : Nat.ModEq (coprimeModulus w H) p s.1.val.val := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [ZMod.natCast_zmod_val]
    exact hp1
  exact Int.natCast_modEq_iff.mpr (Nat.chineseRemainder_modEq_unique (effective_pattern_coprime w H) hp0 hp1')

end ErdosVarianceSmallModel

end

end Erdos970

end OAI
