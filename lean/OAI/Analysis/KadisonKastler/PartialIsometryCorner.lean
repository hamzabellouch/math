import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # A partial isometry between two isometrically embedded Hilbert spaces -/

namespace KadisonKastler

noncomputable section

variable {H K E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private theorem corner_adjoint_comp (U : H →ₗᵢ[ℂ] E) (V : K →ₗᵢ[ℂ] E) (W : E →L[ℂ] E)
    (hU : W.adjoint.comp W = U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint)
    (hV : W.comp W.adjoint = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint) :
    (V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)).adjoint.comp
      (V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)) = 1 := by
  let u := U.toContinuousLinearMap
  let v := V.toContinuousLinearMap
  have hu : u.adjoint.comp u = 1 := U.adjoint_comp_self
  change (v.adjoint.comp (W.comp u)).adjoint.comp (v.adjoint.comp (W.comp u)) = 1
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  calc
    _ = u.adjoint.comp (W.adjoint.comp ((v.comp v.adjoint).comp (W.comp u))) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = u.adjoint.comp (W.adjoint.comp ((W.comp W.adjoint).comp (W.comp u))) := by rw [hV]
    _ = u.adjoint.comp ((W.adjoint.comp W).comp ((W.adjoint.comp W).comp u)) := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = u.adjoint.comp ((u.comp u.adjoint).comp ((u.comp u.adjoint).comp u)) := by rw [hU]
    _ = 1 := by
      simp only [← ContinuousLinearMap.comp_assoc, hu, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp]

/-- Compress a partial isometry whose initial and final projections are the two range projections. -/
def partialIsometryCornerEquiv (U : H →ₗᵢ[ℂ] E) (V : K →ₗᵢ[ℂ] E) (W : E →L[ℂ] E)
    (hU : W.adjoint.comp W = U.toContinuousLinearMap.comp U.toContinuousLinearMap.adjoint)
    (hV : W.comp W.adjoint = V.toContinuousLinearMap.comp V.toContinuousLinearMap.adjoint) :
    H ≃ₗᵢ[ℂ] K := by
  let T := V.toContinuousLinearMap.adjoint.comp (W.comp U.toContinuousLinearMap)
  have hT : T.adjoint.comp T = 1 := corner_adjoint_comp U V W hU hV
  have hT' : T.comp T.adjoint = 1 := by
    have h := corner_adjoint_comp V U W.adjoint (by simpa using hV) (by simpa using hU)
    simpa only [T, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc] using h
  exact LinearIsometryEquiv.ofSurjective
    { T.toLinearMap with norm_map' := T.norm_map_iff_adjoint_comp_self.mpr hT }
    (fun y => ⟨T.adjoint y, by
      have h := congrArg (fun S : K →L[ℂ] K => S y) hT'
      simpa using h⟩)

theorem partialIsometryCornerEquiv_apply (U : H →ₗᵢ[ℂ] E) (V : K →ₗᵢ[ℂ] E)
    (W : E →L[ℂ] E) (hU hV) (x : H) :
    partialIsometryCornerEquiv U V W hU hV x = V.toContinuousLinearMap.adjoint (W (U x)) := rfl

end

end KadisonKastler

end OAI
