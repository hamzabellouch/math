import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RankBot

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]

theorem source_cylinder_truncation
    (_hΩ : ∀ p, 2 ≤ Fintype.card (Ω p))
    (E : Finset (Cylinder Ω)) (hproper : ∀ e ∈ E, e ≠ ⊥)
    (w t : ℕ) (_hw : 1 ≤ w) (ht : 1 ≤ t)
    (hwidth : ∀ e ∈ E, e.support.card ≤ w) :
    Monotone (fun I : Intersection E => Cylinder.rank E I.val) ∧
    (∀ I : Intersection E, ∃ A ⊆ E,
      A.card ≤ Cylinder.rank E I.val ∧ Cylinder.Generates A I.val) ∧
    (∀ I : Intersection E, I.val.support.card ≤ w * Cylinder.rank E I.val) ∧
    (∀ x : ∀ p, Ω p,
      (avoidance E x - truncated E t x).natAbs ≤
        2 ^ (t * w) * max 1 ((t * w) ^ (t * w + 1)) * witnessCount E t x) ∧
    (∀ I ∈ retained E t,
      (coefficient E I).natAbs ≤ max 1 ((t * w) ^ (t * w + 1))) ∧
    (∀ I ∈ witnesses E t, I.val.support.card ≤ t * w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I J hIJ
    exact Cylinder.rank_mono E hIJ
  · intro I
    exact Cylinder.minimal_generators E I.val I.property
  · intro I
    exact Cylinder.rank_width I.property hwidth
  · intro x
    exact truncation_bound E hproper t w ht hwidth x
  · intro I hI
    exact retained_coefficient_bound E t w hwidth I hI
  · intro I hI
    exact witnesses_width E t w hwidth I hI

end OrdinaryCorrelations.SourceCylinder

end

end OAI
