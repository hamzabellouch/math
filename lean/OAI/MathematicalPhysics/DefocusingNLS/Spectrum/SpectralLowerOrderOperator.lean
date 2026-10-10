import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactPencil
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexMultiplierLimit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Prod

namespace OAI

/-! The lower-order weak operator from volume and boundary observations.
The two real multipliers are the mass and weighted radial flux. The boundary
operator contains the outgoing Robin matrix and its transport correction. -/

open InnerProductSpace
namespace DefocusingNLS

noncomputable def spectralPairSkew (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    F × F →L[ℂ] F × F :=
  (ContinuousLinearMap.snd ℂ F F).prod (-ContinuousLinearMap.fst ℂ F F)

noncomputable def spectralPairRiesz {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F × F) : F × F →L[ℂ] E :=
  (((ContinuousLinearMap.fst ℂ F F).comp A).adjoint).comp
    (ContinuousLinearMap.fst ℂ F F) +
  (((ContinuousLinearMap.snd ℂ F F).comp A).adjoint).comp
    (ContinuousLinearMap.snd ℂ F F)

theorem spectralPairRiesz_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F × F) (x : E) (y : F × F) :
    inner ℂ x (spectralPairRiesz A y)=
      inner ℂ (A x).1 y.1+inner ℂ (A x).2 y.2 := by
  simp only [spectralPairRiesz,add_apply,
    ContinuousLinearMap.comp_apply,inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

noncomputable def spectralHarmonicPairValues (ell : ℕ) (R : ℝ) :
    SpectralHarmonicPair ell R →L[ℂ] SpectralRadialL2 R × SpectralRadialL2 R :=
  (spectralRadialPairValue R).comp (spectralHarmonicPairForget ell R)

noncomputable def spectralHarmonicPairDerivatives (ell : ℕ) (R : ℝ) :
    SpectralHarmonicPair ell R →L[ℂ] SpectralRadialL2 R × SpectralRadialL2 R :=
  (((spectralRadialDerivative R).comp
    (WithLp.fstL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R))).prod
  ((spectralRadialDerivative R).comp
    (WithLp.sndL 2 ℂ (SpectralRadialEnergy R) (SpectralRadialEnergy R)))).comp
      (spectralHarmonicPairForget ell R)

noncomputable def spectralHarmonicPairTraces (ell : ℕ) (R : ℝ) (hR : 0 < R) :
    SpectralHarmonicPair ell R →L[ℂ] ℂ × ℂ :=
  (spectralRadialPairTrace R hR).comp (spectralHarmonicPairForget ell R)

noncomputable def spectralWeakOperator {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : F →L[ℂ] F) (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    (F × F) × (ℂ × ℂ) →L[ℂ] E :=
  let P := ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)
  let H := ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ)
  let J := spectralPairSkew F
  ((spectralPairRiesz V).comp (Q.prodMap Q)).comp P +
    (c-ζ) • (((spectralPairRiesz V).comp (Q.prodMap Q)).comp (J.comp P)) +
    ((spectralPairRiesz D).comp (A.prodMap A)).comp (J.comp P) +
    ((spectralPairRiesz T).comp B).comp H

noncomputable def spectralWeakPairing {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : F →L[ℂ] F) (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (θ : E) (z : (F × F) × (ℂ × ℂ)) : ℂ :=
      (inner ℂ (V θ).1 (Q z.1.1)+inner ℂ (V θ).2 (Q z.1.2))+
      (c-ζ)*(inner ℂ (V θ).1 (Q z.1.2)-inner ℂ (V θ).2 (Q z.1.1))+
      (inner ℂ (D θ).1 (A z.1.2)-inner ℂ (D θ).2 (A z.1.1))+
      (inner ℂ (T θ).1 (B z.2).1+inner ℂ (T θ).2 (B z.2).2)

theorem spectralWeakOperator_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : F →L[ℂ] F) (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (θ : E) (z : (F × F) × (ℂ × ℂ)) :
    inner ℂ θ (spectralWeakOperator V D T Q A c ζ B z)=
      spectralWeakPairing V D T Q A c ζ B θ z := by
  change inner ℂ θ
    (spectralPairRiesz V (Q z.1.1,Q z.1.2)+
      (c-ζ) • spectralPairRiesz V (Q z.1.2,Q (-z.1.1))+
      spectralPairRiesz D (A z.1.2,A (-z.1.1))+
      spectralPairRiesz T (B z.2))=_
  simp only [inner_add_right,inner_smul_right,spectralPairRiesz_inner,
    map_neg,inner_neg_right,sub_eq_add_neg,spectralWeakPairing]

noncomputable def spectralLowerOrderOperator (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R :=
  spectralWeakOperator (E := SpectralHarmonicPair ell R) (F := SpectralRadialL2 R)
    (spectralHarmonicPairValues ell R) (spectralHarmonicPairDerivatives ell R)
    (spectralHarmonicPairTraces ell R hR) Q A c ζ B

theorem spectralLowerOrderOperator_inner (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (c ζ : ℂ) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (θ : SpectralHarmonicPair ell R) (z : SpectralRadialObservationSpace R) :
    inner ℂ θ (spectralLowerOrderOperator ell R hR Q A c ζ B z)=
      spectralWeakPairing (spectralHarmonicPairValues ell R)
        (spectralHarmonicPairDerivatives ell R) (spectralHarmonicPairTraces ell R hR)
        Q A c ζ B θ z := by
  unfold spectralLowerOrderOperator
  exact spectralWeakOperator_inner _ _ _ _ _ _ _ _ _ _

end DefocusingNLS

end OAI
