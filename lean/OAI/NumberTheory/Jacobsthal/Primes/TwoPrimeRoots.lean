import OAI.NumberTheory.Jacobsthal.Estimates.TwoPowerDivisibility

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

theorem two_sq_eq_reduction (s : ℕ) (x y : ZMod (2 * 2^s)) (hy : IsUnit y)
    (hxy : x^2 = y^2) :
    reduction 2 (2^s) x = reduction 2 (2^s) y ∨
      reduction 2 (2^s) x = -reduction 2 (2^s) y := by
  have hycast : IsUnit (y.val : ZMod (2*2^s)) := by
    simpa only [ZMod.natCast_zmod_val] using hy
  have hcop : y.val.Coprime 2 :=
    Nat.Coprime.of_dvd_right (dvd_mul_right 2 (2^s))
      ((ZMod.isUnit_iff_coprime y.val (2*2^s)).mp hycast)
  have hyodd : ¬(2 : ℤ) ∣ (y.val : ℤ) := by
    exact_mod_cast (Nat.prime_two.coprime_iff_not_dvd.mp hcop.symm)
  have hdiv : (2 : ℤ)^(s+1) ∣ (x.val : ℤ)^2-(y.val : ℤ)^2 := by
    have hz : (((x.val : ℤ)^2-(y.val : ℤ)^2 : ℤ) : ZMod (2*2^s)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact sub_eq_zero.mpr hxy
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2*2^s)).mp hz
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, pow_succ'] using h
  rcases two_power_square_congruence s (x.val : ℤ) (y.val : ℤ) hyodd hdiv with hm | hp
  · left
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((x.val : ℤ)-(y.val : ℤ)) (2^s)).mpr (by exact_mod_cast hm)
    push_cast at hz
    rw [reduction_apply_val, reduction_apply_val]
    exact sub_eq_zero.mp hz
  · right
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((x.val : ℤ)+(y.val : ℤ)) (2^s)).mpr (by exact_mod_cast hp)
    push_cast at hz
    rw [reduction_apply_val, reduction_apply_val]
    exact eq_neg_of_add_eq_zero_left hz

theorem quadraticUnitRoots_card_le_four_twice (s : ℕ) (a b : ZMod (2*2^s))
    (ha : IsUnit a) : (quadraticUnitRoots (2*2^s) a b).card ≤ 4 := by
  by_cases hempty : (quadraticUnitRoots (2*2^s) a b).Nonempty
  · obtain ⟨y, hy⟩ := hempty
    obtain ⟨hyunit, hyeq⟩ := (Finset.mem_filter.mp hy).2
    let S : Finset (ZMod (2^s)) := {reduction 2 (2^s) y, -reduction 2 (2^s) y}
    have hsubset : quadraticUnitRoots (2*2^s) a b ⊆
        Finset.univ.filter (fun x => reduction 2 (2^s) x ∈ S) := by
      intro x hx
      obtain ⟨_, hxeq⟩ := (Finset.mem_filter.mp hx).2
      have hsq : x^2 = y^2 := by
        rcases ha with ⟨u, rfl⟩
        have h := congrArg (fun z : ZMod (2*2^s) => (↑u⁻¹ : ZMod (2*2^s)) * z)
          (hxeq.trans hyeq.symm)
        simpa only [Units.inv_mul_cancel_left] using h
      have hc := two_sq_eq_reduction s x y hyunit hsq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [S, Finset.mem_insert,
        Finset.mem_singleton] using hc⟩
    have hScard : S.card ≤ 2 := by
      simpa only [Finset.card_singleton] using
        Finset.card_insert_le (reduction 2 (2^s) y) ({-reduction 2 (2^s) y} : Finset _)
    calc
      _ ≤ (Finset.univ.filter (fun x => reduction 2 (2^s) x ∈ S)).card :=
        Finset.card_le_card hsubset
      _ = S.card * 2 := reduction_preimage_card 2 (2^s) S
      _ ≤ 4 := by omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp

theorem quadraticUnitRoots_card_le_four (s : ℕ) (hs : 0 < s) (a b : ZMod (2^s))
    (ha : IsUnit a) : (quadraticUnitRoots (2^s) a b).card ≤ 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have transport (n : ℕ) (hn : n = 2*2^t) [NeZero n]
      (a b : ZMod n) (ha : IsUnit a) : (quadraticUnitRoots n a b).card ≤ 4 := by
    subst n
    exact quadraticUnitRoots_card_le_four_twice t a b ha
  exact transport (2^t.succ) Nat.pow_succ' a b ha

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
