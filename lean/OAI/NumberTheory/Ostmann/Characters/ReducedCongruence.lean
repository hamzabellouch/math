import OAI.NumberTheory.Ostmann.Characters.GCDReduction

namespace OAI

noncomputable section
namespace Ostmann.Characters

theorem unit_congruence_div (n g : ℕ) [NeZero n] (hg : 0<g) (hgn : g∣n)
    (v w : ℤ) (hgv : (g:ℤ)∣v) (hgw : (g:ℤ)∣w)
    (u u' : (ZMod n)ˣ) (h : (v:ZMod n)*u=(w:ZMod n)*u') :
    ((v/(g:ℤ):ℤ):ZMod (n/g)) *
        (ZMod.unitsMap (Nat.div_dvd_of_dvd hgn) u : (ZMod (n/g))ˣ) =
      ((w/(g:ℤ):ℤ):ZMod (n/g)) *
        (ZMod.unitsMap (Nat.div_dvd_of_dvd hgn) u' : (ZMod (n/g))ˣ) := by
  let U : ℤ := (u.val.val:ℕ)
  let V : ℤ := (u'.val.val:ℕ)
  have hd : (n:ℤ)∣v*U-w*V := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    simp only [Int.cast_sub, Int.cast_mul, U, V, Int.cast_natCast,
      ZMod.natCast_zmod_val]
    exact sub_eq_zero.mpr h
  have hd' := cancel_common_divisor n g hg hgn v w U V hgv hgw hd
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (n/g)).mpr hd'
  simp only [Int.cast_sub, Int.cast_mul] at hh
  let φ := ZMod.castHom (Nat.div_dvd_of_dvd hgn) (ZMod (n/g))
  have hu : φ (u:ZMod n)=(U:ZMod (n/g)) := by
    simpa only [map_natCast, Int.cast_natCast, U] using
      (congrArg φ (ZMod.natCast_zmod_val (u:ZMod n))).symm
  have hu' : φ (u':ZMod n)=(V:ZMod (n/g)) := by
    simpa only [map_natCast, Int.cast_natCast, V] using
      (congrArg φ (ZMod.natCast_zmod_val (u':ZMod n))).symm
  change ((v/(g:ℤ):ℤ):ZMod (n/g))*φ (u:ZMod n)=
    ((w/(g:ℤ):ℤ):ZMod (n/g))*φ (u':ZMod n)
  rw [hu,hu']
  exact sub_eq_zero.mp hh

theorem reduce_unit_congruence (n : ℕ) [NeZero n] (v w : ℤ)
    (u u' : (ZMod n)ˣ) (h : (v:ZMod n)*u=(w:ZMod n)*u') :
    let g := v.natAbs.gcd n
    let a := n/g
    IsUnit ((v/(g:ℤ):ℤ):ZMod a) ∧ IsUnit ((w/(g:ℤ):ℤ):ZMod a) ∧
      ((v/(g:ℤ):ℤ):ZMod a) *
          (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)) u : (ZMod a)ˣ) =
        ((w/(g:ℤ):ℤ):ZMod a) *
          (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)) u' : (ZMod a)ˣ) := by
  dsimp only
  have he := gcd_eq_of_unit_congruence n v w u u' h
  refine ⟨reduced_frequency_isUnit n v, ?_, ?_⟩
  · rw [he]
    exact reduced_frequency_isUnit n w
  · apply unit_congruence_div n _ (Nat.gcd_pos_of_pos_right _ (NeZero.pos n))
      (Nat.gcd_dvd_right _ _) v w _ _ u u' h
    · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    · rw [he]
      exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)

end Ostmann.Characters

end

end OAI
