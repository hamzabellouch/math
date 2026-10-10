import OAI.NumberTheory.Ostmann.Construction.CanonicalRecurrence

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Ostmann.Construction

theorem guardedCanonicalCoefficient_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (parent a : State)
    (hp : Nat.Prime parent.giantPlus) (hm : Nat.Prime parent.giantMinus)
    (hV : ∀ j≤l,V j<parent.giantPlus ∧ V j<parent.giantMinus) :
    guardedCanonicalCoefficient sources seed V outside base φ G l parent a =
      canonicalCoefficient sources seed V outside base φ G l a := by
  unfold guardedCanonicalCoefficient canonicalCoefficient
  apply Finset.sum_congr rfl
  intro c hc
  rw [History.guardedWeight_eq_supportedWeight V outside base φ G _ parent hp hm hV]

theorem canonicalCoefficient_prime_node (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (a : State)
    (hp : Nat.Prime a.giantPlus) (hm : Nat.Prime a.giantMinus)
    (hV : ∀ j≤l,V j<a.giantPlus ∧ V j<a.giantMinus) :
    canonicalCoefficient sources seed V outside base φ G (l+1) a =
      ∑ v : AllowedFrequency V l, ∑ w : AllowedFrequency V l,
      ∑ u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)),
        let f := canonicalFrame sources seed V l a v w u
        ((assignmentPrior sources (Template.extracted (l+1) (Template.current seed l))).mass u:ℂ)*
          (if f.Valid V outside l then f.scalar φ G*
            canonicalCoefficient sources seed V outside base φ G l f.plusState*
            conj (canonicalCoefficient sources seed V outside base φ G l f.minusState)
           else 0) := by
  rw [canonicalCoefficient_node]
  simp_rw [guardedCanonicalCoefficient_eq sources seed V outside base φ G l a _ hp hm hV]

end Ostmann.Construction

end

end OAI
