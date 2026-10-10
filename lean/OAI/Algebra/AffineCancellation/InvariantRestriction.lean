import OAI.Algebra.AffineCancellation.PositiveInvariant
import OAI.Algebra.AffineCancellation.RelativeClearing

namespace OAI

noncomputable section

namespace ComplexCancellation.InvariantRestriction
variable {k A B R : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
  [CommRing B] [CommRing R] [IsDomain R] [Algebra k A] [Algebra k B] [Algebra k R]
lemma stable_restrict (f : B →ₐ[k] R) (hf : Function.Injective f) (E : Derivation k R R)
    (hE : LND.LocallyNilpotent E) (hs : ∀ b, ∃ t, E (f b)=f t) :
    ∃ D : Derivation k B B, LND.LocallyNilpotent D ∧ ∀ b, E (f b)=f (D b) := by
  have he : ∀ b, ∃ t, E (f b)=1*f t := by simpa only [one_mul] using hs
  let D := FactorDerivation.derivation f hf E 1 one_ne_zero he
  have hspec (b : B) : E (f b)=f (D b) := by
    simpa only [one_mul] using FactorDerivation.apply_spec f hf E 1 one_ne_zero he b
  exact ⟨D,LND.cancel_factor_locallyNilpotent f hf E hE D one_ne_zero (by simpa only [one_mul] using hspec),hspec⟩
lemma exists_restriction [Algebra.FiniteType k B]
    (h : A →ₐ[k] B) (f : B →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k A A) (E : Derivation k R R) (hE : LND.LocallyNilpotent E)
    (he : ∀ a, E (f (h a))=f (h (D a)))
    (hc : ∀ r, r ∈ RelativeClearing.subalgebra h f D) :
    ∃ c : A, ∃ E' : Derivation k B B, D c=0 ∧ c≠0 ∧ LND.LocallyNilpotent E' ∧
      ∀ b, f (E' b)=f (h c)*E (f b) := by
  obtain ⟨s,hs⟩ := Algebra.FiniteType.out (R := k) (A := B)
  obtain ⟨c,hDc,hcn,hgen⟩ := RelativeClearing.uniform h f D s E (fun _ => hc _)
  let E₀ := f (h c) • E
  have hE₀ : LND.LocallyNilpotent E₀ := LND.replica E hE _ (by rw [he,hDc,map_zero,map_zero])
  have hstable : ∀ b, ∃ t, E₀ (f b)=f t :=
    DerivationRange.stable_of_generators f E₀ (s : Set B) hs hgen
  obtain ⟨E',hE',hspec⟩ := stable_restrict f hf E₀ hE₀ hstable
  exact ⟨c,E',hDc,hcn,hE',fun b => (hspec b).symm⟩
end ComplexCancellation.InvariantRestriction

end

end OAI
