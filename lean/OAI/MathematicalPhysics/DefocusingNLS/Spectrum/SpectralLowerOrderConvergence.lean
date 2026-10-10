import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderOperator

namespace OAI

/-! Operator-norm continuity of the lower-order weak equation. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralSandwich_tendsto {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F)
    (Q : ℕ → F →L[ℂ] F) (Q₀ : F →L[ℂ] F)
    (hQ : Tendsto Q atTop (𝓝 Q₀)) :
    Tendsto (fun n => (A.comp (Q n)).comp B) atTop (𝓝 ((A.comp Q₀).comp B)) := by
  exact spectralComposition_tendsto _ _ _ _
    (spectralComposition_tendsto (fun _ => A) A Q Q₀ tendsto_const_nhds hQ)
    tendsto_const_nhds

theorem spectralWeakOperator_tendsto {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : ℕ → F →L[ℂ] F)
    (Q₀ A₀ : F →L[ℂ] F)
    (hQ : Tendsto Q atTop (𝓝 Q₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (c ζ : ℕ → ℂ) (c₀ ζ₀ : ℂ)
    (hc : Tendsto c atTop (𝓝 c₀)) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (B : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun n => spectralWeakOperator V D T (Q n) (A n) (c n) (ζ n) (B n))
      atTop (𝓝 (spectralWeakOperator V D T Q₀ A₀ c₀ ζ₀ B₀)) := by
  let RV := spectralPairRiesz V
  let RD := spectralPairRiesz D
  let RT := spectralPairRiesz T
  let P := ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)
  let H := ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ)
  let J := spectralPairSkew (F)
  have hQQ : Tendsto (fun n => (Q n).prodMap (Q n)) atTop (𝓝 (Q₀.prodMap Q₀)) :=
    ((ContinuousLinearMap.prodMapL ℂ (F) (F)
      (F) (F)).continuous.continuousAt.tendsto).comp
        (hQ.prodMk_nhds hQ)
  have hAA : Tendsto (fun n => (A n).prodMap (A n)) atTop (𝓝 (A₀.prodMap A₀)) :=
    ((ContinuousLinearMap.prodMapL ℂ (F) (F)
      (F) (F)).continuous.continuousAt.tendsto).comp
        (hA.prodMk_nhds hA)
  have hmass := spectralSandwich_tendsto RV P _ _ hQQ
  have hskew := spectralSandwich_tendsto RV (J.comp P) _ _ hQQ
  have htransport := spectralSandwich_tendsto RD (J.comp P) _ _ hAA
  have hboundary := spectralSandwich_tendsto RT H B B₀ hB
  exact ((hmass.add ((hc.sub hζ).smul hskew)).add htransport).add hboundary

theorem spectralLowerOrderOperator_tendsto (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : ℕ → SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (Q₀ A₀ : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (hQ : Tendsto Q atTop (𝓝 Q₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (c ζ : ℕ → ℂ) (c₀ ζ₀ : ℂ)
    (hc : Tendsto c atTop (𝓝 c₀)) (hζ : Tendsto ζ atTop (𝓝 ζ₀))
    (B : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun n => spectralLowerOrderOperator ell R hR (Q n) (A n) (c n) (ζ n) (B n))
      atTop (𝓝 (spectralLowerOrderOperator ell R hR Q₀ A₀ c₀ ζ₀ B₀)) := by
  unfold spectralLowerOrderOperator
  exact spectralWeakOperator_tendsto _ _ _ _ _ _ _ hQ hA _ _ _ _ hc hζ _ _ hB

end DefocusingNLS

end OAI
