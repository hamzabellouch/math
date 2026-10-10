import Mathlib
import OAI.Analysis.Conductivity.Scalarization.EndingJoinConstitution
import OAI.Analysis.Conductivity.Flux.AEFluxWeak

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real Matrix
open scoped Matrix.Norms.Elementwise

lemma joinedFlux_C1 {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (j : Fin 2) :
    ContDiff ℝ 1 (joinedFlux D u lam k J L K j) := by
  exact axialFluxBlend_C1 (endingJoinCutoff_smooth.of_le (by simp))
    ((symmetricFlux_smooth hD hu j).of_le (by simp)) (delayedPairFlux_C1 hJ hL hK j)

theorem matchedEnding_weak_equation {D : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hD : ContDiff ℝ (↑(⊤:ℕ∞)) D) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {s : Fin 3 → ℝ} {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (hum : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)])
    (hDm : ∀ x : Coord3,x 0∈Icc (6:ℝ) 7 → D x=flatBackgroundTensor s)
    (hPDE : ∀ j x,0<x 0 → symmetricSource D u j x=0)
    (j : Fin 2) (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val ⊆ {x : Coord3 | 0<x 0}) :
    Integrable (fun x => ∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x) ∧
    (∫ x,∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have hF := joinedFlux_C1 (lam:=lam) (k:=k) hD hu hJ hL hK j
  have he : (fun x => ∑ i,(endingJoinTensor D lam k J L K x*gradientColumns
      (fderiv ℝ (matchedEndingPair u lam k J L K) x)).col j i*(smoothDirection (Pi.single i 1) ψ).val x)=ᵐ[volume]
      (fun x => ∑ i,joinedFlux D u lam k J L K j x i*(smoothDirection (Pi.single i 1) ψ).val x) := by
    filter_upwards [endingJoin_constitution_ae (D:=D) hk hJ hL hK hum] with x hx
    rw [hx j]
  constructor
  · apply Integrable.congr _ he.symm
    apply integrable_finsetSum
    intro i _
    exact ((contDiff_pi.mp hF i).continuous.mul
      (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left
  · rw [integral_congr_ae he]
    apply C1_divergence_zero_ae_test volume (fun i => Pi.single i 1)
      (fun i x => joinedFlux D u lam k J L K j x i) (fun i => contDiff_pi.mp hF i) ψ hc
    filter_upwards [endingJoin_normal_ae hk hJ hL hK hum hDm] with x hx
    intro hxs
    have hp := hs (subset_tsupport _ hxs)
    exact axialFluxBlend_divergence_zero (endingJoinCutoff_smooth.differentiable (by simp))
      ((symmetricFlux_smooth hD hu j).differentiable (by simp))
      ((delayedPairFlux_C1 hJ hL hK j).differentiable (by norm_num))
      (hPDE j x hp) (delayedPairFlux_divergence hJ hL hK j x) (hx j)

end ScalarConductivity

end

end OAI
