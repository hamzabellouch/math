import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderOperator

namespace OAI

/-! Holomorphic dependence of the weak lower-order operator on the spectral
parameter and on the outgoing boundary matrix. -/

namespace DefocusingNLS

theorem spectralSandwich_analyticAt {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F)
    (Q : ℂ → F →L[ℂ] F) (z : ℂ) (hQ : AnalyticAt ℂ Q z) :
    AnalyticAt ℂ (fun w => (A.comp (Q w)).comp B) z := by
  let L : (F →L[ℂ] F) →L[ℂ] E →L[ℂ] G :=
    ((ContinuousLinearMap.compL ℂ E F G).flip B).comp
      (ContinuousLinearMap.compL ℂ F F G A)
  exact (L.analyticAt (Q z)).comp hQ

theorem spectralWeakOperator_analyticAt {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : F →L[ℂ] F) (c : ℂ) (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (z : ℂ) (hB : AnalyticAt ℂ B z) :
    AnalyticAt ℂ (fun w => spectralWeakOperator V D T Q A c w (B w)) z := by
  let : NormedAddCommGroup ((F × F) × (ℂ × ℂ) →L[ℂ] E) := inferInstance
  let : NormedSpace ℂ ((F × F) × (ℂ × ℂ) →L[ℂ] E) := inferInstance
  let P := ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)
  let H := ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ)
  have hboundary := spectralSandwich_analyticAt (spectralPairRiesz T) H B z hB
  have hrotation : AnalyticAt ℂ
      (fun w : ℂ => (c-w) • (((spectralPairRiesz V).comp (Q.prodMap Q)).comp
        ((spectralPairSkew F).comp P))) z :=
    (analyticAt_const.sub analyticAt_id).smul analyticAt_const
  exact ((analyticAt_const.add hrotation).add analyticAt_const).add hboundary

noncomputable local instance lowerOrderSpaceNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem spectralLowerOrderOperator_analyticAt (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c : ℂ)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ) (hB : AnalyticAt ℂ B z) :
    AnalyticAt ℂ (fun w => spectralLowerOrderOperator ell R hR Q A c w (B w)) z := by
  unfold spectralLowerOrderOperator
  exact spectralWeakOperator_analyticAt _ _ _ _ _ _ _ _ hB

end DefocusingNLS

end OAI
