import OAI.Analysis.KadisonKastler.RowRepresentationContraction
import OAI.Analysis.KadisonKastler.RectangularWeakCompact
import OAI.Analysis.KadisonKastler.WeakRowOrbit
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-! A single operator representation factors the entire weak row-orbit closure.
Only its bounded right-hand operator varies at cluster points. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def HasFixedRowFactorization {M : VonNeumannAlgebra H} {c : ℝ}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (d : ℝ)
    (F : BoundedWeakAlgebraMap M c) : Prop :=
  ∃ R : H →L[ℂ] K, ‖R‖ ≤ d ∧ ∀ a,
    (F.map a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R)

private theorem factorization_inner {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (a : Algebra M) (ξ η : H) :
    inner ℂ η (L.adjoint ((π a) (R ξ))) =
      inner ℂ ((π a).adjoint (L η)) (R ξ) := by
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]

theorem isClosed_hasFixedRowFactorization {M : VonNeumannAlgebra H} {c d : ℝ}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (hd : 0 ≤ d) :
    IsClosed {F : BoundedWeakAlgebraMap M c | HasFixedRowFactorization π L d F} := by
  let B := ↥(weakRectangularBall H K d)
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_weakRectangularBall (H := H) (K := K) hd)
  let S : Set (BoundedWeakAlgebraMap M c × B) := {p | ∀ a ξ η,
    boundedWeakAlgebraCoefficients p.1 (a, ξ, η) =
      inner ℂ ((π a).adjoint (L η)) (p.2.val.toCLM ξ)}
  have hS : IsClosed S := by
    dsimp only [S]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro ξ
    apply isClosed_iInter
    intro η
    have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
      continuous_induced_dom
    exact isClosed_eq (((continuous_apply (a, ξ, η)).comp hcoeff).comp continuous_fst)
      (ContinuousLinearMapWOT.continuous_inner_apply
        (continuous_subtype_val.comp continuous_snd) ξ ((π a).adjoint (L η)))
  have he : Prod.fst '' S =
      {F : BoundedWeakAlgebraMap M c | HasFixedRowFactorization π L d F} := by
    ext F
    constructor
    · rintro ⟨⟨G, R⟩, h, rfl⟩
      refine ⟨R.val.toCLM, R.property, ?_⟩
      intro a
      apply ContinuousLinearMap.ext
      intro ξ
      apply ext_inner_left ℂ
      intro η
      exact (h a ξ η).trans (factorization_inner π L R.val.toCLM a ξ η).symm
    · rintro ⟨R, hR, h⟩
      refine ⟨(F, ⟨ContinuousLinearMapWOT.ofCLM R, hR⟩), ?_, rfl⟩
      intro a ξ η
      change inner ℂ η ((F.map a : H →L[ℂ] H) ξ) = _
      rw [h a]
      exact factorization_inner π L R a ξ η
  rw [← he]
  exact isClosedMap_fst_of_compactSpace S hS

theorem hasFixedRowFactorization_of_mem_orbitClosure {M : VonNeumannAlgebra H}
    {c d : ℝ} (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (hd : 0 ≤ d) {F G : BoundedWeakAlgebraMap M c}
    (hF : HasFixedRowFactorization π L d F) (hG : G ∈ closure (boundedWeakRowOrbit F)) :
    HasFixedRowFactorization π L d G := by
  apply closure_minimal (t := {T | HasFixedRowFactorization π L d T}) ?_
    (isClosed_hasFixedRowFactorization π L hd) hG
  rintro T ⟨n, r, hr, he⟩
  obtain ⟨R, hR, hf⟩ := hF
  refine ⟨representationRowAverage π r R, (representationRowAverage_norm_le π r hr R).trans hR, ?_⟩
  intro a
  rw [he]
  exact finiteRightAverage_operator_factorization F.map π L R hf r a

end

end KadisonKastler

end OAI
