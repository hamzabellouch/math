import OAI.NumberTheory.Ostmann.Construction.Coefficient
import OAI.NumberTheory.Ostmann.Construction.Reversal

namespace OAI

namespace Ostmann.Construction

theorem unit_fraction_eq_iff {R : Type*} [CommRing R] (v w a b ai bi : R)
    (ha : a*ai=1) (hb : b*bi=1) : v*ai=w*bi ↔ v*b=w*a := by
  have hleft : (v*ai)*(a*b)=v*b := by
    calc
      _ = v*b*(a*ai) := by ring
      _ = _ := by rw [ha,mul_one]
  have hright : (w*bi)*(a*b)=w*a := by
    calc
      _ = w*a*(b*bi) := by ring
      _ = _ := by rw [hb,mul_one]
  have hleft' : (v*b)*(ai*bi)=v*ai := by
    calc
      _ = v*ai*(b*bi) := by ring
      _ = _ := by rw [hb,mul_one]
  have hright' : (w*a)*(ai*bi)=w*bi := by
    calc
      _ = w*bi*(a*ai) := by ring
      _ = _ := by rw [ha,mul_one]
  constructor
  · intro h
    simpa only [hleft,hright] using congrArg (fun z => z*(a*b)) h
  · intro h
    simpa only [hleft',hright'] using congrArg (fun z => z*(ai*bi)) h

theorem modFraction_eq_iff_reversal_dvd (P Hp Hm : ℕ) (v w : ℤ)
    (hHp : Hp.Coprime P) (hHm : Hm.Coprime P) :
    modFraction P v Hp=modFraction P w Hm ↔
      (P:ℤ)∣Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Arithmetic.reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,
    sub_eq_zero,modFraction]
  exact unit_fraction_eq_iff _ _ _ _ _ _
    (ZMod.coe_mul_inv_eq_one Hp hHp) (ZMod.coe_mul_inv_eq_one Hm hHm)

theorem modFraction_eq_iff_exists_unique_frequency (p u Hp Hm : ℕ) (v w : ℤ)
    (hp : 0<p) (hu : 0<u) (hHp : Hp.Coprime (p*u)) (hHm : Hm.Coprime (p*u)) :
    modFraction (p*u) v Hp=modFraction (p*u) w Hm ↔
      ∃! s : ℤ,Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=s*(u:ℤ)*(p:ℤ) := by
  rw [modFraction_eq_iff_reversal_dvd _ _ _ _ _ hHp hHm]
  constructor
  · rintro ⟨s,hs⟩
    have heq : Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=s*(u:ℤ)*(p:ℤ) := by
      rw [hs,Nat.cast_mul]
      ring
    refine ⟨s,heq,?_⟩
    intro t ht
    exact reversal_frequency_unique (by exact_mod_cast hp.ne') (by exact_mod_cast hu.ne') ht heq
  · rintro ⟨s,hs,_⟩
    refine ⟨s,?_⟩
    rw [hs,Nat.cast_mul]
    ring

theorem reversal_frequency_ne_zero {p u Hp Hm : ℕ} {v w s : ℤ}
    (hN : Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)≠0)
    (hs : Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=s*(u:ℤ)*(p:ℤ)) : s≠0 := by
  intro hs0
  apply hN
  simp only [hs,hs0,zero_mul]

end Ostmann.Construction

end OAI
