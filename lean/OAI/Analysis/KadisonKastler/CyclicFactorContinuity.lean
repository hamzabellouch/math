import OAI.Analysis.KadisonKastler.CyclicRowFactorization

namespace OAI

/-! The uniquely determined cyclic right factor varies continuously in the
weak operator topology on every uniformly bounded family. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem continuous_cyclic_right_factor
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (C : Set (BoundedWeakAlgebraMap M c)) (d : ℝ) (hd : 0 ≤ d)
    (R : C → H →L[ℂ] factorizationCyclicSpace π L)
    (hR : ∀ F, ‖R F‖ ≤ d)
    (hF : ∀ F a, (F.val.map a : H →L[ℂ] H) =
      (cyclicFactorLeft π L).adjoint.comp ((cyclicFactorRepresentation π L a).comp (R F))) :
    Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)) := by
  let B := ↥(weakRectangularBall H (factorizationCyclicSpace π L) d)
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_weakRectangularBall (H := H) (K := factorizationCyclicSpace π L) hd)
  let T : C → B := fun F => ⟨ContinuousLinearMapWOT.ofCLM (R F), hR F⟩
  have hgraph : T.graph = {p : C × B | ∀ a ξ η,
      boundedWeakAlgebraCoefficients p.1.val (a, ξ, η) =
        inner ℂ ((cyclicFactorRepresentation π L a).adjoint (cyclicFactorLeft π L η))
          (p.2.val.toCLM ξ)} := by
    ext p
    change T p.1 = p.2 ↔ _
    constructor
    · intro he a ξ η
      rw [← he]
      change inner ℂ η ((p.1.val.map a : H →L[ℂ] H) ξ) = _
      rw [hF]
      simp only [ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
    · intro he
      have hf (a : Algebra M) : (p.1.val.map a : H →L[ℂ] H) =
          (cyclicFactorLeft π L).adjoint.comp
            ((cyclicFactorRepresentation π L a).comp p.2.val.toCLM) := by
        apply ContinuousLinearMap.ext
        intro ξ
        apply ext_inner_left ℂ
        intro η
        simp only [ContinuousLinearMap.comp_apply]
        calc
          _ = inner ℂ ((cyclicFactorRepresentation π L a).adjoint
              (cyclicFactorLeft π L η)) (p.2.val.toCLM ξ) := he a ξ η
          _ = inner ℂ (cyclicFactorLeft π L η)
              (cyclicFactorRepresentation π L a (p.2.val.toCLM ξ)) :=
            ContinuousLinearMap.adjoint_inner_left _ _ _
          _ = _ := (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      have huniq : R p.1 = p.2.val.toCLM :=
        cyclicFactorRight_unique π L _ _ (fun a => (hF p.1 a).symm.trans (hf a))
      apply Subtype.ext
      change ContinuousLinearMapWOT.ofCLM (R p.1) = p.2.val
      rw [huniq, ContinuousLinearMapWOT.ofCLM_toCLM]
  have hclosed : IsClosed T.graph := by
    rw [hgraph]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro ξ
    apply isClosed_iInter
    intro η
    have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
      continuous_induced_dom
    exact isClosed_eq
      (((continuous_apply (a, ξ, η)).comp hcoeff).comp
        (continuous_subtype_val.comp continuous_fst))
      (ContinuousLinearMapWOT.continuous_inner_apply
        (continuous_subtype_val.comp continuous_snd) ξ
        ((cyclicFactorRepresentation π L a).adjoint (cyclicFactorLeft π L η)))
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph hclosed)

end

end KadisonKastler

end OAI
