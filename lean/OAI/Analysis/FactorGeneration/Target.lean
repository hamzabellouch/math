import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weak operator closedness, not operator norm closedness. -/
def WOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S}

/-- The manuscript's W*(s), as the intersection of all weakly closed unital
star subalgebras containing s. This does not invoke a double-commutant theorem. -/
def wstar (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  sInf {S | WOTClosed S ∧ s ⊆ S}

theorem subset_wstar (s : Set (H →L[ℂ] H)) : s ⊆ wstar s := by
  intro x hx
  exact StarSubalgebra.mem_sInf.mpr fun S hS => hS.2 hx

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

theorem wstar_mono {s t : Set (H →L[ℂ] H)} (h : s ⊆ t) : wstar s ≤ wstar t := by
  intro x hx
  apply StarSubalgebra.mem_sInf.mpr
  intro S hS
  exact StarSubalgebra.mem_sInf.mp hx S ⟨hS.1, h.trans hS.2⟩

theorem wstar_closed (s : Set (H →L[ℂ] H)) : WOTClosed (wstar s) := by
  unfold WOTClosed
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ wstar s} =
      ⋂ (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_ : WOTClosed S ∧ s ⊆ S),
        {T : H →WOT[ℂ] H | T.toCLM ∈ S} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, wstar, StarSubalgebra.mem_sInf]
  rw [heq]
  exact isClosed_iInter fun S => isClosed_iInter fun h => h.1

theorem wstar_eq (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    wstar (S : Set (H →L[ℂ] H)) = S :=
  le_antisymm (wstar_le hS (fun _ h => h)) (subset_wstar _)

theorem wstar_idempotent (s : Set (H →L[ℂ] H)) :
    wstar (wstar s : Set (H →L[ℂ] H)) = wstar s :=
  wstar_eq _ (wstar_closed _)

/-- A nonzero finite diffuse factor, stated by its center, isometries, and
projections. These hypotheses do not include any generation conclusion. -/
structure IsII1Factor (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop where
  nonzero : (0 : H →L[ℂ] H) ≠ 1
  weaklyClosed : WOTClosed S
  factor : ∀ x : S, (∀ y : S, y * x = x * y) → ∃ c : ℂ, x = algebraMap ℂ S c
  finite : ∀ v : S, star v * v = 1 → v * star v = 1
  diffuse : ∀ p : S, IsStarProjection p → p ≠ 0 →
    ∃ q : S, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

/-- Separable Banach predual, matching the existential predual convention of
mathlib's WStarAlgebra. This is not norm separability of S. -/
def HasSeparablePredual (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X)
    (_ : CompleteSpace X) (_ : TopologicalSpace.SeparableSpace X),
    Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Generation of the same algebra by one of its bounded operators. -/
def SinglyGenerated (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∃ x ∈ S, wstar {x} = S

/-- The single-generation proposition for nonzero finite diffuse factors with separable Banach preduals. -/
def MainTarget : Prop :=
  ∀ (S : StarSubalgebra ℂ (H →L[ℂ] H)),
    IsII1Factor S → HasSeparablePredual S → SinglyGenerated S

end

end Generator

end OAI
