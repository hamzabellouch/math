import OAI.NumberTheory.CubicMoment.Estimates.MixedPrimitiveData
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Uniformly selecting the primitive character attached to each actual
mixed pair in a finite family, with no character-existence hypothesis. -/
noncomputable section
namespace CubicFirstMoment

def PrimitiveMixedSpecification (a b d : Eisenstein) (ψ : MulChar (Residues d) ℂ) : Prop :=
  d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
  (∀ v : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) v) = 1) ∧
  (∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x) ∧
  (residueHeckeScale d)^2 ≤ 27*norm a*norm b/(2*Real.pi)^2

theorem actual_primitive_mixed_family (P : Finset Eisenstein) {b : Eisenstein}
    (hb : primary b) (hsb : Squarefree b)
    (hP : ∀ a ∈ P, primary a ∧ Squarefree a ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) :
    ∃ (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ),
      ∀ a ∈ P, PrimitiveMixedSpecification a b (d a) (ψ a) := by
  have hex (a : Eisenstein) : ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      a ∈ P → PrimitiveMixedSpecification a b d ψ := by
    by_cases ha : a ∈ P
    · let D := mixedPrimitiveData (hP a ha).1 hb (hP a ha).2.1 hsb
        (hP a ha).2.2.1 (hP a ha).2.2.2
      exact ⟨D.modulus,D.character,fun _ => ⟨D.modulus_ne_zero,D.primitive,D.nonprincipal,
        D.unit_invariant,D.agrees,D.scale_sq_le⟩⟩
    · exact ⟨1,1,fun h => False.elim (ha h)⟩
  choose d ψ hspec using hex
  exact ⟨d,ψ,hspec⟩

lemma ramifiedEulerNorm_le {T : Finset EisensteinIdealPrime}
    (hT : T ∈ ramifiedIdealPrimes.powerset) :
    idealExponentNorm (primeSetExponent T) ≤ 9 := by
  have hle : primeSetExponent T ≤ idealExponentOf (3:Eisenstein) := by
    apply (primeSetExponent_le_iff T (idealExponentOf (3:Eisenstein))).mpr
    intro p hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ((Finset.mem_powerset.mp hT) hp))
  have hnorm := norm_le_of_dvd
    (idealExponentGenerator_ne_zero (idealExponentOf (3:Eisenstein)))
    (idealExponentGenerator_dvd_of_le hle)
  have h3 : idealExponentNorm (idealExponentOf (3:Eisenstein)) = 9 := by
    rw [idealExponentOf_norm (by norm_num)]
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  have hn : idealExponentNorm (primeSetExponent T) ≤ idealExponentNorm (idealExponentOf (3:Eisenstein)) := by
    simpa only [idealExponentNorm,normNat_cast] using hnorm
  exact hn.trans_eq h3

end CubicFirstMoment

end

end OAI
