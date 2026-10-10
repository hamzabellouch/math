import OAI.NumberTheory.JointDickman.Amplification.ReducedArcLifts
import Mathlib.Data.Rat.Lemmas

namespace OAI

/-! # Reduced rational representatives modulo the integer period -/

namespace JointDickman

theorem isUnit_intCast_of_natAbs_coprime {q : ℕ} (n : ℤ) (hn : n.natAbs.Coprime q) :
    IsUnit (n : ZMod q) := by
  have hunit := (ZMod.unitOfCoprime n.natAbs hn).isUnit
  rw [ZMod.coe_unitOfCoprime] at hunit
  by_cases hsign : 0 ≤ n
  · have he : (n.natAbs : ZMod q) = (n : ZMod q) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hsign]
    rwa [he] at hunit
  · have he : (n.natAbs : ZMod q) = -(n : ZMod q) := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_neg (lt_of_not_ge hsign),Int.cast_neg]
    rw [he] at hunit
    simpa only [neg_neg] using hunit.neg

theorem rational_eq_unit_fraction_add_int (r : ℚ) :
    let : NeZero r.den := ⟨r.pos.ne'⟩
    ∃ (u : (ZMod r.den)ˣ) (k : ℤ),
      (r : ℝ) = ((u : ZMod r.den).val : ℝ)/r.den+k := by
  let : NeZero r.den := ⟨r.pos.ne'⟩
  obtain ⟨u,hu⟩ := isUnit_intCast_of_natAbs_coprime r.num r.reduced
  have he : (((u : ZMod r.den).val : ℕ) : ZMod r.den) = (r.num : ZMod r.den) := by
    rw [ZMod.natCast_zmod_val,hu]
  have hd : (r.den : ℤ) ∣ r.num-((u : ZMod r.den).val : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
    simpa only [Int.cast_natCast] using he
  obtain ⟨k,hk⟩ := hd
  refine ⟨u,k,?_⟩
  have hr : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.pos.ne'
  have hk' : (r.num : ℝ)-((u : ZMod r.den).val : ℝ) = (r.den : ℝ)*k := by
    exact_mod_cast hk
  rw [Rat.cast_def]
  apply (div_eq_iff hr).mpr
  field_simp
  nlinarith

theorem unit_fraction_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    (((u : ZMod q).val : ℚ)/q).den = q := by
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  have hc : (((u : ZMod q).val : ℤ).natAbs).Coprime ((q : ℤ).natAbs) := by
    simpa only [Int.natAbs_natCast] using ZMod.val_coe_unit_coprime u
  have h := Rat.den_div_eq_of_coprime hq hc
  apply Int.ofNat_inj.mp
  simpa only [Int.cast_natCast] using h

theorem unit_fraction_add_int_den {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (k : ℤ) :
    ((((u : ZMod q).val : ℚ)/q)+(k : ℚ)).den = q := by
  rw [Rat.add_intCast_den,unit_fraction_den]

theorem unit_fraction_add_int_injective {q : ℕ} [NeZero q]
    (u v : (ZMod q)ˣ) (k l : ℤ)
    (he : ((u : ZMod q).val : ℝ)/q+k = ((v : ZMod q).val : ℝ)/q+l) :
    u = v ∧ k = l := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hu : 0 ≤ ((u : ZMod q).val : ℝ)/q := by positivity
  have hv : 0 ≤ ((v : ZMod q).val : ℝ)/q := by positivity
  have hu1 : ((u : ZMod q).val : ℝ)/q < 1 :=
    (div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt (u : ZMod q))
  have hv1 : ((v : ZMod q).val : ℝ)/q < 1 :=
    (div_lt_one hq).mpr (by exact_mod_cast ZMod.val_lt (v : ZMod q))
  have hkl : k < l+1 := by
    exact_mod_cast (show (k : ℝ) < (l : ℝ)+1 by linarith)
  have hlk : l < k+1 := by
    exact_mod_cast (show (l : ℝ) < (k : ℝ)+1 by linarith)
  have hkeq : k = l := by omega
  refine ⟨?_,hkeq⟩
  apply Units.val_injective
  apply ZMod.val_injective
  have he' : ((u : ZMod q).val : ℝ)/q = ((v : ZMod q).val : ℝ)/q := by
    rw [hkeq] at he
    linarith
  have hv' := (div_left_inj' hq.ne').mp he'
  exact_mod_cast hv'

end JointDickman

end OAI
