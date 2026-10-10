import OAI.Analysis.KadisonKastler.PureStateExtension
import OAI.Analysis.KadisonKastler.MaximalClosedStarIdeal

namespace OAI

/-! # Irreducible representations extending a prescribed pure state -/

namespace KadisonKastler

noncomputable section

open NaimarkZFC
open scoped ComplexOrder InnerProductSpace

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

theorem exists_irreducible_extension_representation (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)),
      IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ ξ : H, ‖ξ‖ = 1 ∧ DenseRange (fun b : B => π b ξ) ∧
        ∀ a, inner ℂ ξ (π (φ a) ξ) = f a := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  obtain ⟨g, hgpure, hrest⟩ := exists_pure_state_extension φ hφ f hf
  have hg : IsState g := (mem_extremePoints.mp hgpure).1
  let P := positiveOfSquares g hg.2
  have hP1 : P 1 = 1 := ((isState_iff g).mp hg).1
  have hn : ‖gnsVector P‖ = 1 := gnsVector_norm_eq_one P hP1
  let : Nontrivial P.GNS := ⟨⟨gnsVector P, 0, by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn⟩⟩
  refine ⟨P.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    P.gnsStarAlgHom, pure_gns_irreducible g hg hgpure,
    gnsVector P, hn, gnsVector_cyclic P, ?_⟩
  intro a
  calc
    inner ℂ (gnsVector P) (P.gnsStarAlgHom (φ a) (gnsVector P)) = P (φ a) :=
      gnsVector_coefficient P (φ a)
    _ = g (φ a) := positiveOfSquares_apply g hg.2 (φ a)
    _ = f a := congrArg (fun F : A →L[ℂ] ℂ => F a) hrest

local instance pureExtensionRepresentationInstance1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance pureExtensionRepresentationInstance2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

theorem exists_faithful_maximal_quotient_extension
    (J : CuntzPureness.ClosedStarIdeal B)
    (hmax : ∀ K : CuntzPureness.ClosedStarIdeal B, K.ideal ≠ ⊤ →
      J.ideal ≤ K.ideal → K.ideal = J.ideal)
    (φ : A →⋆ₐ[ℂ] J.Quotient) (hφ : Function.Injective φ)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : Nontrivial H)
      (π : J.Quotient →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ IsIrreducible π.toNonUnitalStarAlgHom ∧
      ∃ ξ : H, ‖ξ‖ = 1 ∧ DenseRange (fun b : J.Quotient => π b ξ) ∧
        ∀ a, inner ℂ ξ (π (φ a) ξ) = f a := by
  obtain ⟨H, _, _, _, _, π, hπ, ξ, hξ, hcyc, hcoeff⟩ :=
    exists_irreducible_extension_representation φ hφ f hf
  exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, π,
    maximal_closedStarIdeal_quotient_injective J hmax π, hπ, ξ, hξ, hcyc, hcoeff⟩

end

end KadisonKastler

end OAI
