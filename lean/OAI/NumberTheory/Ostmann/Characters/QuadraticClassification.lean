import OAI.NumberTheory.Ostmann.Characters.MixedMaximum

namespace OAI

noncomputable section
namespace Ostmann.Characters

def quadraticCharacter (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacter_isQuadratic (p : ℕ) [Fact p.Prime] :
    (quadraticCharacter p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

theorem quadraticCharacter_ne_one (p : ℕ) [Fact p.Prime] (hp : p≠2) :
    quadraticCharacter p≠1 := by
  apply (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr
  apply quadraticChar_ne_one
  simpa only [ZMod.ringChar_zmod_n] using hp

theorem quadratic_at_generator {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ≠1) (hsq : χ^2=1)
    (g : Fˣ) (hg : ∀x, x∈Subgroup.zpowers g) : χ g= -1 := by
  have hne : χ g≠1 := by
    intro he
    apply hχ
    apply (MulChar.eq_iff hg χ 1).mpr
    simpa only [MulChar.one_apply_coe] using he
  apply (sq_eq_one_iff.mp ?_).resolve_left hne
  rw [← χ.pow_apply_coe 2 g, hsq, MulChar.one_apply_coe]

theorem eq_quadraticCharacter (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (hsq : χ^2=1) :
    χ=quadraticCharacter p := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  apply (MulChar.eq_iff hg χ (quadraticCharacter p)).mpr
  rw [quadratic_at_generator χ hχ hsq g hg,
    quadratic_at_generator (quadraticCharacter p) (quadraticCharacter_ne_one p hp)
      (quadraticCharacter_isQuadratic p).sq_eq_one g hg]

theorem quadraticCharacter_intCast (p : ℕ) [Fact p.Prime] (a : ℤ) :
    quadraticCharacter p (a:ZMod p) = (legendreSym p a : ℂ) := by
  rfl
end Ostmann.Characters

end

end OAI
