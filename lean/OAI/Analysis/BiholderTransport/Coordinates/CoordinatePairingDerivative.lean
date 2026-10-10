import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.GaussLemma

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance coordinatePairingDerivativeNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance coordinatePairingDerivativeDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinatePairingDerivativeDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance coordinatePairingDerivativeBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinatePairingDerivativeBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance coordinatePairingDerivativeTrilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance coordinatePairingDerivativeTrilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

lemma coordinate_pairing_hasDerivAt
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {A V : ℝ × ℝ → E} {U : Set (ℝ×ℝ)} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hV : ContDiffOn ℝ ∞ V U)
    (himg : ∀ z ∈ U, A z ∈ S)
    (hode : ∀ z ∈ U,
      HasDerivAt (fun q => A (q,z.2)) (V z) z.1 ∧
      HasDerivAt (fun q => V (q,z.2))
        (-coordinateChristoffel g (A z) (V z) (V z)) z.1)
    {t s e : ℝ} (hz : (t,s) ∈ U)
    (henergy : HasDerivAt (fun r => g (A (t,r)) (V (t,r)) (V (t,r))) e s) :
    HasDerivAt (fun r => g (A (r,s)) (V (r,s))
      (directionalDerivative A (0,1) (r,s))) (e/2) t := by
  have hgd : DifferentiableAt ℝ g (A (t,s)) :=
    (hg.contDiffAt (hS.mem_nhds (himg _ hz))).differentiableAt (by simp)
  have hAr := hasDerivAt_slice_right ((hA.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hVr := hasDerivAt_slice_right ((hV.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hE := ((hgd.hasFDerivAt.comp_hasDerivAt s hAr).clm_apply hVr).clm_apply hVr
  have he := hE.unique henergy
  have hJ := variation_mixed_derivative hU hA (fun z hz => (hode z hz).1) hz
  have hG := metric_geodesic_variation_derivative
    (γ := fun r => A (r,s)) (V := fun r => V (r,s))
    (J := fun r => directionalDerivative A (0,1) (r,s)) hgd
    (hi _ (himg _ hz)) (hode _ hz).1 (hode _ hz).2 hJ
  have hval : (1/2:ℝ)*(fderiv ℝ g (A (t,s)))
      (directionalDerivative A (0,1) (t,s)) (V (t,s)) (V (t,s)) +
      g (A (t,s)) (V (t,s)) (directionalDerivative V (0,1) (t,s)) = e/2 := by
    simp only [Function.comp_apply,add_apply] at he
    rw [hsym _ (himg _ hz) (directionalDerivative V (0,1) (t,s)) (V (t,s))] at he
    linarith
  exact hval ▸ hG

end WeakMTWTransport

end

end OAI
