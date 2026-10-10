import OAI.Analysis.KadisonKastler.WOTDistanceSeparation
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! # Weak compactness of self-adjoint vector balls

The bounded real vector images used in the modular Radon--Nikodym argument
are closed and convex in the Hilbert norm, by weak operator compactness.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance selfAdjointCompactReal : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Self-adjoint contractions of the given algebra, with the weak operator topology. -/
def wotSelfAdjointBall (M : VonNeumannAlgebra H) : Set (H →WOT[ℂ] H) :=
  Generator.Tracial.weakOperatorBall M 1 ∩ {T | IsSelfAdjoint T.toCLM}

theorem wotSelfAdjointBall_compact (M : VonNeumannAlgebra H) :
    IsCompact (wotSelfAdjointBall M) := by
  apply (Generator.Tracial.weakOperatorBall_isCompact M 1).inter_right
  have he : {T : H →WOT[ℂ] H | IsSelfAdjoint T.toCLM} = {T | star T = T} := by
    ext T
    constructor
    · intro h
      exact DFunLike.ext _ _ (fun x => congrArg (fun A : H →L[ℂ] H => A x) h.star_eq)
    · intro h
      exact ContinuousLinearMap.ext (fun x => congrArg (fun A : H →WOT[ℂ] H => A x) h)
  rw [he]
  exact isClosed_eq continuous_star continuous_id

theorem wotSelfAdjointBall_convex (M : VonNeumannAlgebra H) :
    Convex ℝ (wotSelfAdjointBall M) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨⟨M.toStarSubalgebra.add_mem
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hX.1.1 a)
    ((M.toStarSubalgebra.restrictScalars ℝ).smul_mem hY.1.1 b), ?_⟩, ?_⟩
  · have h := (convex_closedBall (0 : H →L[ℂ] H) 1)
      (show X.toCLM ∈ Metric.closedBall 0 1 by simpa using hX.1.2)
      (show Y.toCLM ∈ Metric.closedBall 0 1 by simpa using hY.1.2)
      ha hb hab
    simpa using h
  · change star (a • X.toCLM + b • Y.toCLM) = a • X.toCLM + b • Y.toCLM
    simp only [star_add, star_smul, star_trivial, hX.2.star_eq, hY.2.star_eq]

/-- A fixed real-linear transform of the vector ball. -/
def selfAdjointVectorImage (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) : Set H :=
  (fun T : H →WOT[ℂ] H => P (T Ω)) '' wotSelfAdjointBall M

private theorem wotVector_realMap_weak_continuous (Ω : H) (P : H →L[ℝ] H) :
    Continuous (fun T : H →WOT[ℂ] H => toWeakSpace ℝ H (P (T Ω))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  let g := f.comp P
  let η := (InnerProductSpace.toDual ℝ H).symm g
  have hg (v : H) : g v = inner ℝ η v :=
    (InnerProductSpace.toDual_symm_apply (x := v) (y := g)).symm
  change Continuous (fun T : H →WOT[ℂ] H => g (T Ω))
  simp_rw [hg, real_inner_eq_re_inner]
  exact Complex.continuous_re.comp
    (ContinuousLinearMapWOT.continuous_inner_apply continuous_id Ω η)

theorem selfAdjointVectorImage_closed (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) :
    IsClosed (selfAdjointVectorImage M Ω P) := by
  have hcompact := (wotSelfAdjointBall_compact M).image
    (wotVector_realMap_weak_continuous Ω P)
  have he : selfAdjointVectorImage M Ω P =
      (toWeakSpace ℝ H) ⁻¹' ((fun T : H →WOT[ℂ] H => toWeakSpace ℝ H (P (T Ω))) ''
        wotSelfAdjointBall M) := by
    ext v
    simp only [selfAdjointVectorImage, Set.mem_image, Set.mem_preimage]
    exact exists_congr fun T => and_congr_right fun _ => (toWeakSpace ℝ H).injective.eq_iff.symm
  rw [he]
  exact hcompact.isClosed.preimage (toWeakSpaceCLM ℝ H).continuous

theorem selfAdjointVectorImage_convex (M : VonNeumannAlgebra H) (Ω : H) (P : H →L[ℝ] H) :
    Convex ℝ (selfAdjointVectorImage M Ω P) := by
  let F : (H →WOT[ℂ] H) →ₗ[ℝ] H :=
    { toFun := fun T => P (T Ω)
      map_add' := fun _ _ => P.map_add _ _
      map_smul' := fun _ _ => P.map_smul _ _ }
  exact (wotSelfAdjointBall_convex M).linear_image F

end

end KadisonKastler

end OAI
