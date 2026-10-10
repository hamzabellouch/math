import OAI.NumberTheory.Ostmann.Tree.Autocorrelation
import OAI.NumberTheory.Ostmann.Tree.Mellin
import OAI.NumberTheory.Ostmann.Tree.PairMobius
import OAI.NumberTheory.Ostmann.Tree.UnitSums

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def bottomPair (g : ZMod p → ℂ) (c : (ZMod p)ˣ) (t : ZMod p) : ℂ :=
  g (pairMobiusValue c t) * conj (g ((c:ZMod p)/(t-1)))

def characterTwist (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (x : ZMod p) : ℂ :=
  g x*conj (χ x)

theorem conjugate_character_cancel (χ : MulChar (ZMod p) ℂ) (x : ZMod p) (hx : x≠0) :
    conj (χ x)*χ x=1 := by
  change star (χ x)*χ x=1
  rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
  exact MulChar.one_apply_coe (Units.mk0 x hx)

theorem bottomPair_twisted_value (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (c : (ZMod p)ˣ) (t : ZMod p) (hg0 : g 0=0) :
    bottomPair g c t*conj (χ t) =
      characterTwist g χ (pairMobiusValue c t) *
        conj (characterTwist g χ (pairMobiusValue c t-c)) := by
  by_cases ht0 : t=0
  · subst t
    simp [bottomPair, pairMobiusValue, characterTwist, hg0]
  by_cases ht1 : t=1
  · subst t
    simp [bottomPair, pairMobiusValue, characterTwist, hg0]
  let z : ZMod p := (c:ZMod p)/(t-1)
  have hz : z≠0 := div_ne_zero (Units.ne_zero c) (sub_ne_zero.mpr ht1)
  have hx : pairMobiusValue c t=t*z := by dsimp [pairMobiusValue,z]; ring
  have hc := conjugate_character_cancel χ z hz
  rw [pairMobiusValue_sub c t ht1]
  change (g (pairMobiusValue c t)*conj (g z))*conj (χ t) =
    (g (pairMobiusValue c t)*conj (χ (pairMobiusValue c t))) * conj (g z*conj (χ z))
  rw [hx, map_mul χ, map_mul, map_mul, starRingEnd_self_apply]
  calc
    _ = (g (t*z)*conj (g z)*conj (χ t))*(conj (χ z)*χ z) := by rw [hc]; ring
    _ = _ := by ring

theorem bottomPair_mellin (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (c : (ZMod p)ˣ) (hg0 : g 0=0) :
    mellin (fun t : (ZMod p)ˣ => bottomPair g c t) χ =
      ((p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)) * autocorrelation (characterTwist g χ) c := by
  have hzero : characterTwist g χ 0=0 := by simp [characterTwist,hg0]
  let A : ZMod p → ℂ := fun x => characterTwist g χ x*conj (characterTwist g χ (x-c))
  have hA0 : A 0=0 := by simp [A,hzero]
  have hAc : A c=0 := by simp [A,hzero]
  have hT0 : bottomPair g c 0*conj (χ 0)=0 := by
    simp [bottomPair, pairMobiusValue,hg0]
  unfold mellin
  rw [sum_units_of_zero (fun t => bottomPair g c t*conj (χ t)) hT0]
  simp_rw [bottomPair_twisted_value g χ c _ hg0]
  change (Fintype.card (ZMod p)ˣ:ℂ)⁻¹ * (∑ t, A (pairMobiusValue c t)) = _
  rw [pairMobius_sum c A hA0 hAc]
  dsimp [A, autocorrelation, mean]
  have hp : (p:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

end
end Ostmann.FiniteField

end OAI
