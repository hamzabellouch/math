import OAI.Analysis.KadisonKastler.SimpleAlgebraIdealSeparation
import OAI.Analysis.Naimark.States

namespace OAI

/-! # A faithful irreducible representation for Sakai's construction

Compactness of the state space gives a pure state. Its GNS representation
is irreducible, and simplicity makes the representation faithful. These
steps use the existing state-space and GNS proofs, with no representation
existence hypothesis.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

theorem exists_pure_state :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ IsPureState f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : IsScalarTower ℝ ℂ (WeakDual ℂ A) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (A →L[ℂ] ℂ))
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    (WeakDual.withSeminorms ℂ A).toLocallyConvexSpace
  obtain ⟨f, hf, _⟩ := exists_norming_state (1 : A)
  have hne : (weakStates A).Nonempty := ⟨StrongDual.toWeakDual f, hf⟩
  obtain ⟨g, hg⟩ := isCompact_weakStates.extremePoints_nonempty hne
  exact ⟨g.toStrongDual, hg.1, hg⟩

theorem exists_simple_irreducible_representation (hA : CStarSimple A) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ ξ : H, ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨f, hf, hpure⟩ := exists_pure_state (A := A)
  let g := positiveOfSquares f hf.2
  have h1 : g 1 = 1 := ((isState_iff f).mp hf).1
  have hn : ‖gnsVector g‖ = 1 := gnsVector_norm_eq_one g h1
  let : Nontrivial g.GNS := ⟨⟨gnsVector g, 0, by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn⟩⟩
  refine ⟨g.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    g.gnsStarAlgHom, ?_, pure_gns_irreducible f hf hpure,
    gnsVector g, hn, gnsVector_cyclic g⟩
  exact CurrentMain.simple_starAlgHom_injective hA g.gnsStarAlgHom

end

end KadisonKastler

end OAI
