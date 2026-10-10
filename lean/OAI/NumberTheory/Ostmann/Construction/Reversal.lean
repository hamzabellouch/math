import OAI.NumberTheory.Ostmann.Arithmetic.ReversalCoprimality

namespace OAI

namespace Ostmann.Construction

theorem reversal_transform_left {F : Type*} [Field F]
    {v w Hp Hm s P : F} (heq : v*Hm-w*Hp=s*P)
    (hHp : Hp=0) (hP : P≠0) (hHm : Hm≠0) : v/P=s/Hm := by
  apply (div_eq_div_iff hP hHm).mpr
  simpa [hHp] using heq

theorem reversal_transform_right {F : Type*} [Field F]
    {v w Hp Hm s P : F} (heq : v*Hm-w*Hp=s*P)
    (hHm : Hm=0) (hP : P≠0) (hHp : Hp≠0) : (-w)/P=s/Hp := by
  apply (div_eq_div_iff hP hHp).mpr
  simpa [hHm] using heq

theorem common_divisor_dvd_frequency {R : Type*} [CommRing R]
    {v w Hp Hm s P q : R} (heq : v*Hm-w*Hp=s*P)
    (hplus : q∣Hp) (hminus : q∣Hm) (hunit : IsCoprime q P) : q∣s := by
  apply hunit.dvd_of_dvd_mul_right
  rw [← heq]
  exact dvd_sub (dvd_mul_of_dvd_right hminus v) (dvd_mul_of_dvd_right hplus w)

theorem no_large_common_divisor {v w Hp Hm s P : ℤ} {q : ℕ}
    (heq : v*Hm-w*Hp=s*P) (hs : s≠0) (hq : s.natAbs<q)
    (hunit : IsCoprime (q : ℤ) P) : ¬ ((q : ℤ)∣Hp ∧ (q : ℤ)∣Hm) := by
  rintro ⟨hplus,hminus⟩
  have hd := common_divisor_dvd_frequency heq hplus hminus hunit
  have hle := Int.natAbs_le_of_dvd_ne_zero hd hs
  simpa only [Int.natAbs_natCast] using (not_le_of_gt hq hle)

theorem integral_pivot_unique {v w Hp Hm s u p p' : ℤ}
    (hs : s≠0) (hu : u≠0)
    (hp : v*Hm-w*Hp=s*u*p) (hp' : v*Hm-w*Hp=s*u*p') : p=p' := by
  apply mul_left_cancel₀ (mul_ne_zero hs hu)
  exact hp.symm.trans hp'

theorem reversal_frequency_unique {v w Hp Hm s s' u p : ℤ}
    (hp0 : p≠0) (hu : u≠0)
    (hs : v*Hm-w*Hp=s*u*p) (hs' : v*Hm-w*Hp=s'*u*p) : s=s' := by
  have h : (s*u)*p=(s'*u)*p := hs.symm.trans hs'
  exact mul_right_cancel₀ hu (mul_right_cancel₀ hp0 h)

end Ostmann.Construction

end OAI
