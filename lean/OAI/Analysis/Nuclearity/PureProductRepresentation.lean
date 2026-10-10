import OAI.Analysis.Nuclearity.PureStateRepresentation
import OAI.Analysis.Nuclearity.SpatialEvaluation
import OAI.Analysis.OperatorAlgebra.TotalTensorVectors

namespace OAI

/-! The product of the faithful pure-GNS sums and its total cyclic vectors. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder ENNReal
open UniformSpace

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

local instance : DecidableEq (PureStateData A) := Classical.decEq _
local instance : DecidableEq (PureStateData B) := Classical.decEq _

abbrev pureProductRepresentation : SpatialRepresentation A B where
  left := pureGNSHilbert A
  right := pureGNSHilbert B
  leftRep := pureGNSRepresentation A
  rightRep := pureGNSRepresentation B

theorem pureProductEvaluation_isometry : Isometry
    (minimalSpatialEvaluation (pureProductRepresentation (A := A) (B := B))) :=
  minimalSpatialEvaluation_isometry _ (pureGNSRepresentation_injective A)
    (pureGNSRepresentation_injective B)

theorem gns_unital_apply (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a = f.gnsNonUnitalStarAlgHom a := rfl

def pureCyclicVector (f : PureStateData A) : pureGNSHilbert A :=
  lp.single 2 f (Pureness.stateGNSVector f.state)

theorem pureGNS_inner_single (f : PureStateData A) (ξ η : f.state.GNS) :
    inner ℂ (lp.single 2 f ξ : pureGNSHilbert A) (lp.single 2 f η) = inner ℂ ξ η := by
  exact (lp.inner_single_left (𝕜 := ℂ) (G := fun g : PureStateData A => g.state.GNS)
    f ξ (lp.single 2 f η)).trans
    (by rw [lp.single_apply_self])

@[simp] theorem norm_pureCyclicVector (f : PureStateData A) : ‖pureCyclicVector f‖ = 1 := by
  exact (lp.norm_single (E := fun g : PureStateData A => g.state.GNS)
    (by norm_num : (0 : ℝ≥0∞) < 2) f (Pureness.stateGNSVector f.state)).trans
    (Pureness.stateGNSVector_norm f.state f.unital)

theorem pureProduct_cyclic_total {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : (pureProductRepresentation (A := A) (B := B)).space →L[ℂ] E)
    (hT : ∀ (f : PureStateData A) (g : PureStateData B) (a : A) (b : B),
      T ((pureGNSRepresentation A a (pureCyclicVector f) ⊗ₜ[ℂ]
        pureGNSRepresentation B b (pureCyclicVector g) :
        pureGNSHilbert A ⊗[ℂ] pureGNSHilbert B) :
        (pureProductRepresentation (A := A) (B := B)).space) = 0) : T = 0 := by
  let ξ (i : PureStateData A × A) := pureGNSRepresentation A i.2 (pureCyclicVector i.1)
  let η (j : PureStateData B × B) := pureGNSRepresentation B j.2 (pureCyclicVector j.1)
  have hA : ∀ L : pureGNSHilbert A →L[ℂ] E, (∀ i, L (ξ i) = 0) → L = 0 := by
    intro L hL
    apply pureGNS_operator_eq_zero A L
    intro f a
    simpa only [ξ, pureCyclicVector, pureGNSRepresentation_single, gns_unital_apply] using hL (f, a)
  have hB : ∀ L : pureGNSHilbert B →L[ℂ] E, (∀ j, L (η j) = 0) → L = 0 := by
    intro L hL
    apply pureGNS_operator_eq_zero B L
    intro g b
    simpa only [η, pureCyclicVector, pureGNSRepresentation_single, gns_unital_apply] using hL (g, b)
  exact completed_tensor_operator_eq_zero ξ η hA hB T (fun i j => hT i.1 j.1 i.2 j.2)

end WeakPureInfiniteness

end

end OAI
