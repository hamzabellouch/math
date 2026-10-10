import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderAnalytic

namespace OAI

/-! The actual lower-order spectral derivative contains the volume rotation
and the derivative of the outgoing boundary operator. -/

namespace DefocusingNLS

local instance {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    IsBoundedSMul ℂ ((F × F) × (ℂ × ℂ) →L[ℂ] E) := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℂ)
    (E := (F × F) × (ℂ × ℂ) →L[ℂ] E))

theorem spectralSandwich_hasDerivAt {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F)
    (Q : ℂ → F →L[ℂ] F) (D : F →L[ℂ] F) (z : ℂ) (hQ : HasDerivAt Q D z) :
    HasDerivAt (fun w => (A.comp (Q w)).comp B) ((A.comp D).comp B) z := by
  let L : (F →L[ℂ] F) →L[ℂ] E →L[ℂ] G :=
    ((ContinuousLinearMap.compL ℂ E F G).flip B).comp
      (ContinuousLinearMap.compL ℂ F F G A)
  exact L.hasFDerivAt.comp_hasDerivAt z hQ

noncomputable def spectralWeakOperatorSlope {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q : F →L[ℂ] F) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    (F × F) × (ℂ × ℂ) →L[ℂ] E :=
  -(((spectralPairRiesz V).comp (Q.prodMap Q)).comp
    ((spectralPairSkew F).comp (ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)))) +
    ((spectralPairRiesz T).comp B).comp (ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ))

theorem spectralWeakOperator_hasDerivAt {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : F →L[ℂ] F) (c : ℂ) (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (B' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ) (hB : HasDerivAt B B' z) :
    HasDerivAt (fun w => spectralWeakOperator V D T Q A c w (B w))
      (spectralWeakOperatorSlope V T Q B') z := by
  let P := ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)
  let H := ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ)
  let J := spectralPairSkew F
  let V₀ := ((spectralPairRiesz V).comp (Q.prodMap Q)).comp P
  let V₁ := ((spectralPairRiesz V).comp (Q.prodMap Q)).comp (J.comp P)
  let V₂ := ((spectralPairRiesz D).comp (A.prodMap A)).comp (J.comp P)
  have hb := spectralSandwich_hasDerivAt (spectralPairRiesz T) H B B' z hB
  have hr := ((hasDerivAt_id z).const_sub c).smul_const V₁
  have hd := (((hasDerivAt_const z V₀).add hr).add (hasDerivAt_const z V₂)).add hb
  simp only [zero_add, neg_smul, one_smul, add_zero] at hd
  convert! hd using 1

noncomputable def spectralLowerOrderSlope (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R :=
  spectralWeakOperatorSlope (E := SpectralHarmonicPair ell R) (F := SpectralRadialL2 R)
    (spectralHarmonicPairValues ell R)
    (spectralHarmonicPairTraces ell R hR) Q B

noncomputable local instance lowerOrderDerivativeNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem spectralLowerOrderOperator_hasDerivAt (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c : ℂ)
    (B : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (z : ℂ) (hB : HasDerivAt B B' z) :
    HasDerivAt (fun w => spectralLowerOrderOperator ell R hR Q A c w (B w))
      (spectralLowerOrderSlope ell R hR Q B') z := by
  exact spectralWeakOperator_hasDerivAt _ _ _ _ _ _ _ _ _ hB

end DefocusingNLS

end OAI
