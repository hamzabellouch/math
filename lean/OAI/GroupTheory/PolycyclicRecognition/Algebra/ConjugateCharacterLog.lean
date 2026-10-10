import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteGeneratedCharacterLog

namespace OAI

/-! # Conjugation-compatible logarithms after a finite power

Symmetrizing a compatible logarithm doubles its power and makes it respect
the involution. This will preserve real forms in the spectral construction.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [CommGroup G]

def conjugateCharacterLog (L : G →* Multiplicative ℂ) (c : G →* G) :
    G →* Multiplicative ℂ where
  toFun g := Multiplicative.ofAdd (star (L (c g)).toAdd)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.ext
    simp [map_mul, star_add]

theorem conjugateCharacterLog_exp (L : G →* Multiplicative ℂ) (c : G →* G) (g : G) :
    complexUnitExp (conjugateCharacterLog L c g) = star (complexUnitExp (L (c g))) := by
  apply Units.ext
  exact Complex.exp_conj _

theorem symmetrizedCharacterLog_conjugation (L : G →* Multiplicative ℂ)
    (c : G →* G) (hc : ∀ g, c (c g) = g) (g : G) :
    ((L * conjugateCharacterLog L c) (c g)).toAdd =
      star (((L * conjugateCharacterLog L c) g).toAdd) := by
  change (L (c g)).toAdd + star (L (c (c g))).toAdd =
    star ((L g).toAdd + star (L (c g)).toAdd)
  rw [hc, star_add, star_star, add_comm]

theorem finitelyGenerated_real_character_power_log [Group.FG G]
    (ρ : G →* ℂˣ) (c : G →* G) (hc : ∀ g, c (c g) = g)
    (hρ : ∀ g, ρ (c g) = star (ρ g)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : G →* Multiplicative ℂ,
      (∀ g, complexUnitExp (L g) = ρ g ^ m) ∧
      (∀ g, (L (c g)).toAdd = star (L g).toAdd) := by
  obtain ⟨m, hm, L, hL⟩ := finitelyGenerated_character_power_log ρ
  refine ⟨2 * m, Nat.mul_pos (by decide) hm, L * conjugateCharacterLog L c, ?_,
    symmetrizedCharacterLog_conjugation L c hc⟩
  intro g
  rw [MonoidHom.mul_apply, map_mul, hL, conjugateCharacterLog_exp, hL, hρ,
    star_pow, star_star, two_mul, pow_add]

end PolycyclicRecognition

end

end OAI
