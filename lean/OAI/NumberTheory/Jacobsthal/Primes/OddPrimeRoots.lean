import OAI.NumberTheory.Jacobsthal.Partitions.StationaryFibres

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

def primeReduction (p s : ℕ) (hs : 0 < s) : ZMod (p^s) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)

theorem isUnit_iff_primeReduction_ne_zero (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (x : ZMod (p^s)) : IsUnit x ↔ primeReduction p s hs x ≠ 0 := by
  have hx : primeReduction p s hs x = (x.val : ZMod p) := by
    rw [primeReduction, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hx, ne_eq, ZMod.natCast_eq_zero_iff]
  nth_rw 1 [← x.natCast_zmod_val]
  exact ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hs

theorem eq_or_neg_of_sq_eq_odd (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (hp2 : p ≠ 2)
    (x y : ZMod (p^s)) (hy : IsUnit y) (hxy : x^2 = y^2) : x = y ∨ x = -y := by
  let f := primeReduction p s hs
  have hyf : f y ≠ 0 := (isUnit_iff_primeReduction_ne_zero p s hs y).mp hy
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2'
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hp2 hp2'
  have hfactor : (x-y)*(x+y) = 0 := by linear_combination hxy
  have hunits : IsUnit (x-y) ∨ IsUnit (x+y) := by
    rw [isUnit_iff_primeReduction_ne_zero p s hs,
      isUnit_iff_primeReduction_ne_zero p s hs]
    change f (x-y) ≠ 0 ∨ f (x+y) ≠ 0
    by_cases hm : f (x-y) = 0
    · right
      have he : f x = f y := sub_eq_zero.mp (by simpa only [map_sub] using hm)
      rw [map_add, he, ← two_mul]
      exact mul_ne_zero htwo hyf
    · exact Or.inl hm
  rcases hunits with hm | hp
  · right
    exact eq_neg_of_add_eq_zero_left ((hm.mul_right_eq_zero).mp hfactor)
  · left
    exact sub_eq_zero.mp ((hp.mul_left_eq_zero).mp hfactor)

theorem quadraticUnitRoots_card_le_two (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (hp2 : p ≠ 2) (a b : ZMod (p^s)) (ha : IsUnit a) :
    (quadraticUnitRoots (p^s) a b).card ≤ 2 := by
  by_cases hempty : (quadraticUnitRoots (p^s) a b).Nonempty
  · obtain ⟨y, hy⟩ := hempty
    obtain ⟨hyunit, hyeq⟩ := (Finset.mem_filter.mp hy).2
    have hsubset : quadraticUnitRoots (p^s) a b ⊆ {y,-y} := by
      intro x hx
      obtain ⟨_, hxeq⟩ := (Finset.mem_filter.mp hx).2
      have hsq : x^2 = y^2 := by
        rcases ha with ⟨u, rfl⟩
        have h := congrArg (fun z : ZMod (p^s) => (↑u⁻¹ : ZMod (p^s)) * z)
          (hxeq.trans hyeq.symm)
        simpa only [Units.inv_mul_cancel_left] using h
      rcases eq_or_neg_of_sq_eq_odd p s hs hp2 x y hyunit hsq with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
    exact (Finset.card_le_card hsubset).trans (by simpa using Finset.card_insert_le y ({-y} : Finset (ZMod (p^s))))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
