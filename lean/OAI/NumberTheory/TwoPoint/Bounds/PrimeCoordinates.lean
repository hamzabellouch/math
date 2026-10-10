import OAI.NumberTheory.TwoPoint.Bounds.PrimeLiteralEncoding
import OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
import OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform

namespace OAI

/-! The common padded prime law in the canonical finite coordinate order. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

local instance canonicalPrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (i : Fin (Fintype.card ↥(data.P ∪ data.Q))) :
    NeZero (primeResidueModuli (data.P ∪ data.Q) i) :=
  ⟨(primeResidueModuli_prime _ (fun p hp => data.prime ⟨p, hp⟩) i).ne_zero⟩

lemma ProhibitedPrimeFamily.residue_average_canonical {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (F : (∀ i, ZMod (primeResidueModuli (data.P ∪ data.Q) i)) → ℝ) :
    (data.residueLaw B hB).average
      (fun x => F (fun i => (x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)).val)) =
      uniformAverage F := by
  unfold ProhibitedPrimeFamily.residueLaw
  rw [FiniteLaw.independent_average_reindex (Fintype.equivFin ↥(data.P ∪ data.Q)).symm]
  simp only [Equiv.symm_symm, Equiv.apply_symm_apply]
  exact uniformResidue_product_average B (primeResidueModuli (data.P ∪ data.Q))
    (fun i => (data.prime _).pos) (fun i => hB _ ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i).property) F

lemma ProhibitedPrimeFamily.canonical_origin {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (x : ↥(data.P ∪ data.Q) → Fin B) :
    (fun i => (data.residueOrigin x : ZMod (primeResidueModuli (data.P ∪ data.Q) i))) =
      (fun i => ((x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)).val :
        ZMod (primeResidueModuli (data.P ∪ data.Q) i))) := by
  funext i
  exact data.residueOrigin_spec x ((Fintype.equivFin ↥(data.P ∪ data.Q)).symm i)

end TwoPointCorrelations

end OAI
