import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorNoncube

namespace OAI

/-! The exact nonreal primitive cubic character for the Kummer prime input.
All arithmetic hypotheses of that input are derived here. -/
noncomputable section
namespace CubicFirstMoment

theorem noncube_primitive_conductor (hpub : CubicSupplementaryPeriodicity)
    {v : Eisenstein} (hv : v ≠ 0) (hn : ¬∃ j : Eisenstein, j^3=v) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧ star ψ ≠ ψ ∧
      d ∣ 9*v ∧ normNat d ≤ normNat (9*v) ∧ ψ^3=1 ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u)=1) ∧
      (∀ x : Eisenstein, primary x → IsCoprime v x →
        ψ (Ideal.Quotient.mk (modulus d) x)=cubicSymbol x v) := by
  obtain ⟨d,ψ,hd,hp,hdiv,hN,h3,hu,hi,hval⟩ := cubicNumerator_primitive_conductor hpub hv
  obtain ⟨x,hx,hcop,hne⟩ := (cubicNumeratorChar_ne_one_iff hpub v hv).mp
    (cubicNumeratorChar_noncube hpub hv hn)
  have hψ : ψ ≠ 1 := hi.nonprincipal ⟨x,hcop,by
    rwa [cubicNumeratorChar_primary hpub v hv hx]⟩
  let : Finite (Residues d) := finite_residues hd
  exact ⟨d,ψ,hd,hp,hψ,odd_cubic_character_not_self_conjugate ψ h3 hψ,
    hdiv,hN,h3,hu,hval⟩

end CubicFirstMoment

end

end OAI
