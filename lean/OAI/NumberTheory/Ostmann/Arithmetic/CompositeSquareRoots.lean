import OAI.NumberTheory.Ostmann.Arithmetic.CompositeSquareRootsGcd
import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth

namespace OAI

namespace Ostmann.Arithmetic

def rootOneCode (n : ℕ) [NeZero n] (x : {x : ZMod n // x ^ 2 = 1}) :
    {d : ℕ // d ∈ n.divisors} × Fin 2 := by
  refine (⟨Int.gcd (n : ℤ) ((x.val.val : ℤ) - 1), ?_⟩,
    ⟨2 * x.val.val / n, ?_⟩)
  · apply Nat.mem_divisors.mpr
    refine ⟨?_, NeZero.ne n⟩
    exact_mod_cast Int.gcd_dvd_left (n : ℤ) ((x.val.val : ℤ) - 1)
  · apply (Nat.div_lt_iff_lt_mul (NeZero.pos n)).mpr
    have h := x.val.val_lt
    omega

theorem square_one_int_factor_dvd (n : ℕ) [NeZero n]
    (x : {x : ZMod n // x ^ 2 = 1}) :
    (n : ℤ) ∣ ((x.val.val : ℤ) - 1) * ((x.val.val : ℤ) + 1) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  calc
    (x.val - 1) * (x.val + 1) = x.val ^ 2 - 1 := by ring
    _ = 0 := by rw [x.property]; ring

theorem rootOneCode_injective (n : ℕ) [NeZero n] :
    Function.Injective (rootOneCode n) := by
  intro x y h
  have hg := congrArg (fun z => z.1.val) h
  have hq := congrArg (fun z => z.2.val) h
  apply Subtype.ext
  apply ZMod.val_injective n
  apply nat_eq_of_two_sub_dvd_of_halfIndex_eq (NeZero.pos n) x.val.val_lt y.val.val_lt
  · exact int_dvd_two_sub_of_square_gcd_eq n x.val.val y.val.val
      (square_one_int_factor_dvd n x) (square_one_int_factor_dvd n y) hg
  · exact hq

theorem card_square_one_le_two_divisors (n : ℕ) [NeZero n] :
    Nat.card {x : ZMod n // x ^ 2 = 1} ≤ 2 * n.divisors.card := by
  have h := Nat.card_le_card_of_injective (rootOneCode n) (rootOneCode_injective n)
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fin, Nat.mul_comm] using h

theorem card_square_fiber_le_one {G : Type*} [CommGroup G] [Finite G] (a : G) :
    Nat.card {x : G // x ^ 2 = a} ≤ Nat.card {x : G // x ^ 2 = 1} := by
  classical
  by_cases h : ∃ x : G, x ^ 2 = a
  · obtain ⟨r, hr⟩ := h
    let f : {x : G // x ^ 2 = a} → {x : G // x ^ 2 = 1} := fun x =>
      ⟨x.val / r, by simp [div_pow, x.property, hr]⟩
    apply Nat.card_le_card_of_injective f
    intro x y hxy
    apply Subtype.ext
    exact div_left_inj.mp (congrArg Subtype.val hxy)
  · have hempty : IsEmpty {x : G // x ^ 2 = a} := ⟨fun x => h ⟨x.val, x.property⟩⟩
    simp

theorem card_unit_square_fiber_le_two_divisors (n : ℕ) [NeZero n]
    (a : (ZMod n)ˣ) :
    Nat.card {x : (ZMod n)ˣ // x ^ 2 = a} ≤ 2 * n.divisors.card := by
  apply (card_square_fiber_le_one a).trans
  apply le_trans ?_ (card_square_one_le_two_divisors n)
  let f : {x : (ZMod n)ˣ // x ^ 2 = 1} → {x : ZMod n // x ^ 2 = 1} :=
    fun x => ⟨x.val.val, by exact congrArg Units.val x.property⟩
  apply Nat.card_le_card_of_injective f
  intro x y h
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

theorem card_unit_square_fiber_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ [NeZero n], ∀ a : (ZMod n)ˣ,
      (Nat.card {x : (ZMod n)ˣ // x ^ 2 = a} : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := divisors_card_le_rpow ε hε
  refine ⟨2 * C, by positivity, fun n _ a => ?_⟩
  have h : (Nat.card {x : (ZMod n)ˣ // x ^ 2 = a} : ℝ) ≤ 2 * n.divisors.card := by
    exact_mod_cast card_unit_square_fiber_le_two_divisors n a
  calc
    _ ≤ 2 * (n.divisors.card : ℝ) := h
    _ ≤ 2 * (C * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hbound n (NeZero.pos n)) (by norm_num)
    _ = (2 * C) * (n : ℝ) ^ ε := by ring

end Ostmann.Arithmetic

end OAI
