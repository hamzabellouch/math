import OAI.NumberTheory.CubicMoment.Estimates.PrimaryHeckeCharacter

namespace OAI

/-! Elementary conductor reduction for the finite residue characters.
Minimality is measured by the positive ideal norm; the inducing character
and exact deleted Euler factors are not supplied as extra assumptions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Agreement of characters on ideals prime to the original modulus. -/
def ResidueCharacterInduces (q d : Eisenstein)
    (χ : MulChar (Residues q) ℂ) (ψ : MulChar (Residues d) ℂ) : Prop :=
  d ∣ q ∧ ∀ x : Eisenstein, IsCoprime q x →
    ψ (Ideal.Quotient.mk (modulus d) x) = χ (Ideal.Quotient.mk (modulus q) x)

/-- No inducing modulus has smaller norm. This is the usual primitivity
criterion for a finite ray character over a principal ideal domain. -/
def PrimitiveResidueCharacter (q : Eisenstein) (χ : MulChar (Residues q) ℂ) : Prop :=
  ∀ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
    ResidueCharacterInduces q d χ ψ → normNat q ≤ normNat d

lemma ResidueCharacterInduces.refl (q : Eisenstein) (χ : MulChar (Residues q) ℂ) :
    ResidueCharacterInduces q q χ χ := ⟨dvd_refl q,fun _ _ => rfl⟩

lemma ResidueCharacterInduces.trans {q d e : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    {ω : MulChar (Residues e) ℂ}
    (hqd : ResidueCharacterInduces q d χ ψ) (hde : ResidueCharacterInduces d e ψ ω) :
    ResidueCharacterInduces q e χ ω := by
  refine ⟨hde.1.trans hqd.1,?_⟩
  intro x hx
  exact (hde.2 x (hx.of_isCoprime_of_dvd_left hqd.1)).trans (hqd.2 x hx)

/-- Every finite character has an actual primitive inducing character,
of modulus dividing the original one and of no larger norm. -/
theorem primitive_residue_conductor_exists {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ ResidueCharacterInduces q d χ ψ ∧
      normNat d ≤ normNat q ∧ PrimitiveResidueCharacter d ψ := by
  let E : ℕ → Prop := fun n => ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
    normNat d = n ∧ ResidueCharacterInduces q d χ ψ
  have hex : ∃ n, E n := ⟨normNat q,q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  obtain ⟨d,ψ,hdn,hd⟩ := Nat.find_spec hex
  refine ⟨d,ψ,ne_zero_of_dvd_ne_zero hq hd.1,hd,?_,?_⟩
  · rw [hdn]
    exact Nat.find_min' hex ⟨q,χ,rfl,ResidueCharacterInduces.refl q χ⟩
  · intro e ω he
    rw [hdn]
    exact Nat.find_min' hex ⟨e,ω,rfl,hd.trans he⟩

lemma ResidueCharacterInduces.global_units {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1) :
    ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1 := by
  intro u
  have hc : IsCoprime q (u:Eisenstein) := ⟨0,(u⁻¹:Eisensteinˣ),by simp⟩
  exact (h.2 u hc).trans (hu u)

lemma ResidueCharacterInduces.restriction {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (x : Eisenstein) :
    χ (Ideal.Quotient.mk (modulus q) x) =
      if IsCoprime q x then ψ (Ideal.Quotient.mk (modulus d) x) else 0 := by
  by_cases hx : IsCoprime q x
  · rw [ite_eq_left hx,h.2 x hx]
  · rw [ite_eq_right hx]
    exact MulChar.map_nonunit χ (fun hu => hx (isCoprime_of_residue_isUnit hu))

lemma ResidueCharacterInduces.nonprincipal {q d : Eisenstein}
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ)
    (hw : ∃ x : Eisenstein, IsCoprime q x ∧ χ (Ideal.Quotient.mk (modulus q) x) ≠ 1) :
    ψ ≠ 1 := by
  intro he
  obtain ⟨x,hx,hχx⟩ := hw
  have hdx := residue_isUnit_of_isCoprime (hx.of_isCoprime_of_dvd_left h.1)
  have hval := h.2 x hx
  rw [he,MulChar.one_apply hdx] at hval
  exact hχx hval.symm

end CubicFirstMoment

end

end OAI
