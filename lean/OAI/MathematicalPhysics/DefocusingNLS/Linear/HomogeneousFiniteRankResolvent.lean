import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-! # The finite-rank resolvent formula

The time-step decomposition reduces invertibility to the finite-dimensional
factor. This algebraic identity is used with the actual finite-rank factor;
it makes no spectral or evolution assumption.
-/

namespace DefocusingNLS

section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def finiteRankResolvent (R : E →L[𝕜] E) (U : F →L[𝕜] E)
    (V : E →L[𝕜] F) (W : F →L[𝕜] F) : E →L[𝕜] E :=
  R + R.comp (U.comp (W.comp (V.comp R)))

theorem finiteRankResolvent_left (A R : E →L[𝕜] E) (U : F →L[𝕜] E)
    (V : E →L[𝕜] F) (W : F →L[𝕜] F)
    (hAR : A.comp R = ContinuousLinearMap.id 𝕜 E)
    (hDW : (ContinuousLinearMap.id 𝕜 F - V.comp (R.comp U)).comp W =
      ContinuousLinearMap.id 𝕜 F) :
    (A - U.comp V).comp (finiteRankResolvent R U V W) =
      ContinuousLinearMap.id 𝕜 E := by
  have hARx (x : E) : A (R x) = x :=
    congrArg (fun L : E →L[𝕜] E => L x) hAR
  ext x
  have hDx : W (V (R x)) - V (R (U (W (V (R x))))) = V (R x) :=
    congrArg (fun L : F →L[𝕜] F => L (V (R x))) hDW
  have hU := congrArg U hDx
  rw [map_sub, sub_eq_iff_eq_add] at hU
  change A (R x + R (U (W (V (R x))))) -
    U (V (R x + R (U (W (V (R x)))))) = x
  simp only [map_add, hARx]
  rw [← hU]
  abel

theorem finiteRankResolvent_right (A R : E →L[𝕜] E) (U : F →L[𝕜] E)
    (V : E →L[𝕜] F) (W : F →L[𝕜] F)
    (hRA : R.comp A = ContinuousLinearMap.id 𝕜 E)
    (hWD : W.comp (ContinuousLinearMap.id 𝕜 F - V.comp (R.comp U)) =
      ContinuousLinearMap.id 𝕜 F) :
    (finiteRankResolvent R U V W).comp (A - U.comp V) =
      ContinuousLinearMap.id 𝕜 E := by
  have hRAx (x : E) : R (A x) = x :=
    congrArg (fun L : E →L[𝕜] E => L x) hRA
  ext x
  have hWx : W (V x - V (R (U (V x)))) = V x :=
    congrArg (fun L : F →L[𝕜] F => L (V x)) hWD
  change R (A x - U (V x)) + R (U (W (V (R (A x - U (V x)))))) = x
  simp only [map_sub R, hRAx, map_sub V]
  rw [hWx]
  abel

end

end DefocusingNLS

end OAI
