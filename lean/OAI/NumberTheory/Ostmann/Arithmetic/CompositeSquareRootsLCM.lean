import OAI.NumberTheory.Ostmann.Arithmetic.CompositeSquareRoots

namespace OAI

namespace Ostmann.Arithmetic

theorem card_square_map_fiber_le_one {G H : Type*} [CommGroup G] [CommGroup H]
    [Finite G] (f : G →* H) (hf : Function.Injective f) (a : H) :
    Nat.card {x : G // (f x) ^ 2 = a} ≤ Nat.card {x : G // x ^ 2 = 1} := by
  classical
  by_cases h : ∃ x : G, (f x) ^ 2 = a
  · obtain ⟨r, hr⟩ := h
    let g : {x : G // (f x) ^ 2 = a} → {x : G // x ^ 2 = 1} := fun x =>
      ⟨x.val / r, by
        apply hf
        rw [map_pow, map_div, map_one]
        simp only [div_pow, x.property, hr, div_self']⟩
    apply Nat.card_le_card_of_injective g
    intro x y hxy
    apply Subtype.ext
    exact div_left_inj.mp (congrArg Subtype.val hxy)
  · have hempty : IsEmpty {x : G // (f x) ^ 2 = a} := ⟨fun x => h ⟨x.val, x.property⟩⟩
    simp

def lcmUnitsMap (m n : ℕ) :
    (ZMod (m.lcm n))ˣ →* (ZMod m × ZMod n)ˣ :=
  Units.map (ZMod.castHom dvd_rfl (ZMod m × ZMod n)).toMonoidHom

theorem lcmUnitsMap_injective (m n : ℕ) : Function.Injective (lcmUnitsMap m n) := by
  intro x y h
  apply Units.ext
  apply (ZMod.castHom_injective (R := ZMod m × ZMod n))
  exact congrArg Units.val h

theorem card_lcm_unit_square_fiber_le_two_divisors (m n : ℕ) [NeZero (m.lcm n)]
    (a : (ZMod m × ZMod n)ˣ) :
    Nat.card {x : (ZMod (m.lcm n))ˣ // (lcmUnitsMap m n x) ^ 2 = a} ≤
      2 * (m.lcm n).divisors.card := by
  exact (card_square_map_fiber_le_one (lcmUnitsMap m n) (lcmUnitsMap_injective m n) a).trans
    (card_unit_square_fiber_le_two_divisors (m.lcm n) 1)

end Ostmann.Arithmetic

end OAI
