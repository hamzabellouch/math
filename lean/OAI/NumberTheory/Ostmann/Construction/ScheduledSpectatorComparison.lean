import OAI.NumberTheory.Ostmann.Construction.ScheduledTreeBulkCoordinates
import OAI.NumberTheory.Ostmann.Construction.TransferConjugations
import OAI.NumberTheory.Ostmann.Construction.NormalizedSpectatorComparison

namespace OAI

/-! # The normalized quartet estimate for actual scheduled good matchings -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def SpectatorDiagram.withTransferConjugations {p n : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (b : Bool) : SpectatorDiagram p n :=
  { d with conjugations := transferConjugations n b }

theorem normalized_scheduled_spectator_comparison {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (hm : 0 < m)
    (e : PartitionMatching (scheduledBulkLabel role (n + 2)) (scheduledBulkLabel role (n + 2)))
    (he : ¬ BadScheduledMatching role (n + 2) m word e)
    {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (b : Bool) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        (d₁.withTransferConjugations b).bulkValue (normalizedResidueTransform S) x *
          conj (d₂.bulkValue (normalizedResidueTransform S)
            (x ∘ (scheduledTreeBulkMatching role (n + 2) m word e).symm)))‖ ^ 2 ≤
      quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  let c : TreeLeafIndex n → Bool := treeLeafTupleEquiv Bool n (transferConjugations n b)
  apply normalized_spectator_bulk_comparison hp n m hm
    (scheduledTreeBulkMatching role (n + 2) m word e)
    (scheduledTreeBulkMatching_good role (n + 2) m word e he)
    S hlo hhi hS hSp β ε hε hε1 hprincipal hβ hbias
    (d₁.withTransferConjugations b) d₂ c (fun q => !(c q))
  intro q
  simpa only [SpectatorDiagram.withTransferConjugations, Bool.not_not] using
    transferConjugations_quartet n b q

end Ostmann

end OAI
