import Mathlib
import OAI.Analysis.Conductivity.Flux.LinearTensorEllipticity
import OAI.Analysis.Conductivity.Geometry.TorusAffineField

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped Matrix.Norms.Elementwise

lemma WeakFiniteTensorPair.component_flux_C1 {U : Set Coord3} (w : WeakFiniteTensorPair U)
    (j : Fin 2) : ContDiff ℝ 1 (fun y => (w.G y).col j) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp w.flux_C1)

lemma WeakFiniteTensorPair.flux_on_constant_patch {U V : Set Coord3}
    (w : WeakFiniteTensorPair U) (hV : IsOpen V) (K : Mat3)
    (hK : ∀ x∈V,w.E x=K) (f : Coord3 → Fin 2 → ℝ)
    (_ : ContDiffOn ℝ 2 f V) (hw : ∀ x∈V,w.v x=f x) :
    ∀ x∈V,w.G x=K*gradientColumns (fderiv ℝ f x) := by
  have ha : w.G=ᵐ[volume.restrict V] (fun x => K*gradientColumns (fderiv ℝ w.v x)) := by
    filter_upwards [ae_restrict_of_ae w.constitution,ae_restrict_mem hV.measurableSet] with x hx hxV
    rw [←hx,hK x hxV]
  have hd : Continuous (fun x => K*gradientColumns (fderiv ℝ w.v x)) := by
    have hh := w.smooth.continuous_fderiv (by norm_num)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x => ∑ k : Fin 3,K i k*(fderiv ℝ w.v x (Pi.single k 1)) j)
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((continuous_apply j).comp (hh.clm_apply continuous_const))
  have he := Measure.eqOn_open_of_ae_eq ha hV w.flux_C1.continuous.continuousOn hd.continuousOn
  intro x hx
  rw [he hx]
  have hv : w.v=ᶠ[𝓝 x] f := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hw y hy
  dsimp only
  rw [hv.fderiv_eq (𝕜 := ℝ)]

lemma WeakFiniteTensorPair.flux_on_flat_patch {U V : Set Coord3}
    (w : WeakFiniteTensorPair U) (hV : IsOpen V) (s : Fin 3 → ℝ)
    (hE : ∀ x∈V,w.E x=flatBackgroundTensor s) (f : Coord3 → Fin 2 → ℝ)
    (hf : ContDiffOn ℝ 2 f V) (hw : ∀ x∈V,w.v x=f x) (j : Fin 2) :
    ∀ x∈V,(w.G x).col j=flatModeFlux s (fun y => f y j) x := by
  intro x hx
  rw [w.flux_on_constant_patch hV _ hE f hf hw x hx,flatModeFlux_tensor]
  change flatBackgroundTensor s*ᵥ(gradientColumns (fderiv ℝ f x)).col j = _
  congr 1
  ext i
  rw [(hasFDerivAt_pi'.mp ((hf.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt j).fderiv]
  rfl

end ScalarConductivity

end
end

end OAI
