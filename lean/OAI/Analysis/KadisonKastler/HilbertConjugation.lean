import OAI.Analysis.KadisonKastler.TomitaCentralizerConjugation
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! # An auxiliary conjugate copy of an arbitrary Hilbert space

Coordinate conjugation supplies the fixed antiunitary used to write the Tomita
graph as a complex-linear graph. The polar conjugation is then constructed
from that graph; no modular theorem is invoked here.
-/

namespace KadisonKastler

noncomputable section

private def coordinateConjugation (ι : Type*) : lp (fun _ : ι => ℂ) 2 ≃ₗᵢ⋆[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_smul' := star_smul
  norm_map' := norm_star

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_hilbert_conjugation : ∃ J : H ≃ₗᵢ⋆[ℂ] H, Function.Involutive J := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  let J := (b.repr.trans (coordinateConjugation ι)).trans b.repr.symm
  refine ⟨J, ?_⟩
  intro x
  change b.repr.symm (star (b.repr (b.repr.symm (star (b.repr x))))) = x
  rw [b.repr.apply_symm_apply, star_star, b.repr.symm_apply_apply]

/-- The graph construction gives an involutive conjugation fixing the state
vector and satisfying the full centralizer-vector clause. The commutant clause
of modular conjugation is not asserted by this theorem. -/
theorem exists_polar_conjugation {M : VonNeumannAlgebra H} (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    ∃ J : H ≃ₗᵢ⋆[ℂ] H, Function.Involutive J ∧ J Ω = Ω ∧
      ∀ r : Algebra M,
        (∀ a : Algebra M,
          inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) →
        J (star r.val Ω) = r.val Ω := by
  obtain ⟨J, _⟩ := exists_hilbert_conjugation (H := H)
  exact ⟨tomitaPolarConjugation J Ω hsep hcyc,
    tomitaPolarConjugation_involutive J Ω hsep hcyc,
    tomitaPolarConjugation_fixes_vector J Ω hsep hcyc,
    tomitaPolarConjugation_star_centralizer J Ω hsep hcyc⟩

end

end KadisonKastler

end OAI
