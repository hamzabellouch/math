import OAI.Geometry.RCD.Metric.EuclideanCompactConvolution
import OAI.Geometry.RCD.Metric.EuclideanMollifierSequence
import OAI.Geometry.RCD.Heat.EuclideanRadialKernel

namespace OAI

/-! # A distributional harmonic function satisfies the exact local radial mean identity -/

open Set Metric Filter MeasureTheory InnerProductSpace
open scoped ContDiff Convolution Topology
noncomputable section
namespace RegularPointCoordinates

theorem weak_harmonic_radial_mean {n : ℕ} {f : Euclidean n → ℝ} {S r : ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hw : EuclideanWeakHarmonicOn f S) (hr : 0<r)
    (p : Euclidean n) (hp : ‖p‖+r<S) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r) p =
      (r^n*(∫ x, euclideanRadialWeight n x))*f p := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  let g := fun k => f ⋆[L,volume] euclideanMollifier n k
  let C := r^n*(∫ x, euclideanRadialWeight n x)
  let R := (S-‖p‖+r)/2
  have hR : 0<R := by dsimp only [R]; linarith
  have hrR : r<R := by dsimp only [R]; linarith
  have hgap : 0<S-‖p‖-R := by dsimp only [R]; linarith
  have hmean : ∀ᶠ k in atTop,
      (g k ⋆[L,volume] euclideanRadialKernel n r) p=C*g k p := by
    filter_upwards [euclideanMollifierRadius_tendsto.eventually (Iio_mem_nhds hgap)] with k hk
    have hh : HarmonicOnNhd (g k) (ball p R) := by
      apply (weak_harmonic_mollification hf.locallyIntegrable hw k).mono
      intro y hy
      have htri := dist_triangle y p 0
      have hyp : dist y p<R := hy
      simp only [dist_zero_right] at htri
      rw [mem_ball,dist_zero_right]
      linarith
    exact harmonic_convolution_radialKernel
      ((euclideanMollifier_compact n k).contDiff_convolution_right L hf.locallyIntegrable
        ((euclideanMollifier_smooth n k).of_le (by simp)))
      (hfs.convolution L (euclideanMollifier_compact n k)) p hR hr hrR hh
  have hleft : Tendsto (fun k => (g k ⋆[L,volume] euclideanRadialKernel n r) p)
      atTop (𝓝 ((f ⋆[L,volume] euclideanRadialKernel n r) p)) := by
    have hc : Continuous (f ⋆[L,volume] euclideanRadialKernel n r) := (euclideanRadialKernel_compact n hr).continuous_convolution_right L
      hf.locallyIntegrable (euclideanRadialKernel_smooth n r).continuous
    apply (euclideanMollifier_convolution_tendsto hc p).congr'
    filter_upwards with k
    dsimp only [g]
    rw [scalar_convolution_comm f (euclideanMollifier n k),
      compact_scalar_convolution_assoc (euclideanMollifier_smooth n k).continuous hf
        (euclideanRadialKernel_smooth n r).continuous hfs (euclideanRadialKernel_compact n hr)]
  have hright : Tendsto (fun k => C*g k p) atTop (𝓝 (C*f p)) := by
    apply ((euclideanMollifier_convolution_tendsto hf p).const_mul C).congr'
    filter_upwards with k
    dsimp only [g]
    rw [scalar_convolution_comm f (euclideanMollifier n k)]
  exact tendsto_nhds_unique hleft (hright.congr' (hmean.mono fun _ hk => hk.symm))

end RegularPointCoordinates

end

end OAI
