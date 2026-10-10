import OAI.NumberTheory.JointDickman.Amplification.RamanujanRoots

namespace OAI

/-! # The exact unit-frequency Ramanujan sum -/

namespace JointDickman

open Finset
open scoped ArithmeticFunction.Moebius

open Classical in
theorem primitiveRoots_image_units (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = univ.image (fun r : (ZMod q)ˣ => ZMod.stdAddChar (r : ZMod q)) := by
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), mem_image]
  constructor
  · intro hz
    obtain ⟨i, _, hic, hi⟩ := (Complex.isPrimitiveRoot_iff z q (NeZero.ne q)).mp hz
    refine ⟨ZMod.unitOfCoprime i hic, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, stdAddChar_natCast]
    calc
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((i : ℂ) / q)) := by congr 1; ring
      _ = z := hi
  · rintro ⟨r, _, rfl⟩
    have hc : (r : ZMod q).val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa only [ZMod.natCast_zmod_val] using r.isUnit
    rw [← ZMod.natCast_zmod_val (r : ZMod q), stdAddChar_natCast]
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((r : ZMod q).val : ℂ) / q =
        2 * (Real.pi : ℂ) * Complex.I * (((r : ZMod q).val : ℂ) / q) := by ring
    rw [he]
    exact Complex.isPrimitiveRoot_exp_of_coprime _ _ (NeZero.ne q) hc

open Classical in
theorem sum_stdAddChar_units (q : ℕ) [NeZero q] :
    ∑ r : (ZMod q)ˣ, ZMod.stdAddChar (r : ZMod q) = (μ q : ℂ) := by
  rw [← sum_primitiveRoots_eq_moebius q (NeZero.pos q), primitiveRoots_image_units,
    sum_image]
  exact fun _ _ _ _ h => Units.val_injective (ZMod.injective_stdAddChar h)

open Classical in
theorem ramanujan_sum_unit_frequency {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ∑ r : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * (r : ZMod q)) = (μ q : ℂ) := by
  rw [← sum_stdAddChar_units q]
  simpa only [Units.val_mul] using
    Fintype.sum_bijective (fun r : (ZMod q)ˣ => u * r) (Equiv.mulLeft u).bijective
      (fun r : (ZMod q)ˣ => ZMod.stdAddChar ((u : ZMod q) * (r : ZMod q)))
      (fun r : (ZMod q)ˣ => ZMod.stdAddChar (r : ZMod q)) (fun _ => rfl)

theorem norm_stdAddChar {q : ℕ} [NeZero q] (r : ZMod q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle r).norm_coe

end JointDickman

end OAI
