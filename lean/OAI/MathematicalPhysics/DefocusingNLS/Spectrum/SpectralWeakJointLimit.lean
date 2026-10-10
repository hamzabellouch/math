import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderOperator

namespace OAI

/-! Product-filter versions of the weak-operator limit, for joint convergence
in power and spectral parameter. -/

open Filter Topology
namespace DefocusingNLS
theorem spectralComposition_tendsto_filter {ι E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (p : Filter ι) (T : ι → F →L[ℂ] G) (T₀ : F →L[ℂ] G)
    (K : ι → E →L[ℂ] F) (K₀ : E →L[ℂ] F)
    (hT : Tendsto T p (𝓝 T₀)) (hK : Tendsto K p (𝓝 K₀)) :
    Tendsto (fun i => (T i).comp (K i)) p (𝓝 (T₀.comp K₀)) := by
  exact ((ContinuousLinearMap.compL ℂ E F G).continuous₂.continuousAt.tendsto).comp
    (hT.prodMk_nhds hK)


theorem spectralSandwich_tendsto_filter {ι E F G : Type*} (p : Filter ι)
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (B : E →L[ℂ] F)
    (Q : ι → F →L[ℂ] F) (Q₀ : F →L[ℂ] F)
    (hQ : Tendsto Q p (𝓝 Q₀)) :
    Tendsto (fun n => (A.comp (Q n)).comp B) p (𝓝 ((A.comp Q₀).comp B)) := by
  exact spectralComposition_tendsto_filter p _ _ _ _
    (spectralComposition_tendsto_filter p (fun _ => A) A Q Q₀ tendsto_const_nhds hQ)
    tendsto_const_nhds

theorem spectralWeakOperator_tendsto_filter {ι E F : Type*} (p : Filter ι)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V D : E →L[ℂ] F × F) (T : E →L[ℂ] ℂ × ℂ)
    (Q A : ι → F →L[ℂ] F)
    (Q₀ A₀ : F →L[ℂ] F)
    (hQ : Tendsto Q p (𝓝 Q₀)) (hA : Tendsto A p (𝓝 A₀))
    (c ζ : ι → ℂ) (c₀ ζ₀ : ℂ)
    (hc : Tendsto c p (𝓝 c₀)) (hζ : Tendsto ζ p (𝓝 ζ₀))
    (B : ι → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B p (𝓝 B₀)) :
    Tendsto (fun n => spectralWeakOperator V D T (Q n) (A n) (c n) (ζ n) (B n))
      p (𝓝 (spectralWeakOperator V D T Q₀ A₀ c₀ ζ₀ B₀)) := by
  let RV := spectralPairRiesz V
  let RD := spectralPairRiesz D
  let RT := spectralPairRiesz T
  let P := ContinuousLinearMap.fst ℂ (F × F) (ℂ × ℂ)
  let H := ContinuousLinearMap.snd ℂ (F × F) (ℂ × ℂ)
  let J := spectralPairSkew (F)
  have hQQ : Tendsto (fun n => (Q n).prodMap (Q n)) p (𝓝 (Q₀.prodMap Q₀)) :=
    ((ContinuousLinearMap.prodMapL ℂ (F) (F)
      (F) (F)).continuous.continuousAt.tendsto).comp
        (hQ.prodMk_nhds hQ)
  have hAA : Tendsto (fun n => (A n).prodMap (A n)) p (𝓝 (A₀.prodMap A₀)) :=
    ((ContinuousLinearMap.prodMapL ℂ (F) (F)
      (F) (F)).continuous.continuousAt.tendsto).comp
        (hA.prodMk_nhds hA)
  have hmass := spectralSandwich_tendsto_filter p RV P _ _ hQQ
  have hskew := spectralSandwich_tendsto_filter p RV (J.comp P) _ _ hQQ
  have htransport := spectralSandwich_tendsto_filter p RD (J.comp P) _ _ hAA
  have hboundary := spectralSandwich_tendsto_filter p RT H B B₀ hB
  exact ((hmass.add ((hc.sub hζ).smul hskew)).add htransport).add hboundary

theorem spectralLowerOrderOperator_tendsto_filter {ι : Type*} (p : Filter ι) (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (Q A : ι → SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (Q₀ A₀ : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R)
    (hQ : Tendsto Q p (𝓝 Q₀)) (hA : Tendsto A p (𝓝 A₀))
    (c ζ : ι → ℂ) (c₀ ζ₀ : ℂ)
    (hc : Tendsto c p (𝓝 c₀)) (hζ : Tendsto ζ p (𝓝 ζ₀))
    (B : ι → ℂ × ℂ →L[ℂ] ℂ × ℂ) (B₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hB : Tendsto B p (𝓝 B₀)) :
    Tendsto (fun n => spectralLowerOrderOperator ell R hR (Q n) (A n) (c n) (ζ n) (B n))
      p (𝓝 (spectralLowerOrderOperator ell R hR Q₀ A₀ c₀ ζ₀ B₀)) := by
  unfold spectralLowerOrderOperator
  exact spectralWeakOperator_tendsto_filter p _ _ _ _ _ _ _ hQ hA _ _ _ _ hc hζ _ _ hB

end DefocusingNLS

end OAI
