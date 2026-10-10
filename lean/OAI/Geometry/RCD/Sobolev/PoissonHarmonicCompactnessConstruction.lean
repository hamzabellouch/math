import OAI.Geometry.RCD.Harmonic.RadialMixedLimit
import OAI.Geometry.RCD.Sobolev.MeasuredSmoothTestLimits

namespace OAI

/-! # The actual Poisson/harmonic compactness input

The normalized harmonic sequence determines one classical harmonic model
and one subsequence. Every radial mixed-gradient test then converges along
that same subsequence by the constructed compact recoveries. The original
constant-Laplacian and energy hypotheses are retained in the interface,
though only the stated radial gradient and value bounds are needed here.
-/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poissonHarmonicCompactnessInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] :
    LocalPoissonHarmonicCompactnessInput hX := by
  intro hn S hS p r ε hr hcurv hε hεlim u V w f hV hrep hw hnorm _ hdata hflim
  obtain ⟨A,α,hA,hdata⟩ := hdata
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hεlim.eventually (Iio_mem_nhds zero_lt_one))
  obtain ⟨t,ht,model,hgs,hgL,hconv,hmom,htest⟩ := hX.harmonic_model_compactness_smooth hn hS
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N)) (fun k => (hε (k+N)).le)
    (fun k => (hN (k+N) (Nat.le_add_left N k)).le) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => u (k+N)) (fun k => V (k+N)) (fun k => w (k+N))
    (fun k => hV (k+N)) (fun k i => hrep (k+N) i) (fun k => hw (k+N)) (fun k => hnorm (k+N))
  let j := fun k => t k+N
  have hj : StrictMono j := fun i k hik => Nat.add_lt_add_right (ht hik) N
  refine ⟨j,hj,model,?_⟩
  constructor
  · intro ρ hρ hρS i k
    exact hmom ρ hρ hρS i k
  · intro ψ hψ
    have hmixed := hX.radial_mixed_limit hn hS (p ∘ j) (r ∘ j) (ε ∘ j) (V ∘ j)
      (fun k => hr (j k)) (fun k => hcurv (j k)) (fun k => (hε (j k)).le)
      (fun k => (hN (j k) (Nat.le_add_left N (t k))).le) (hεlim.comp hj.tendsto_atTop)
      (fun k => hV (j k)) (f ∘ j) (w ∘ j) (fun k => hw (j k)) (fun k => hnorm (j k))
      model.value hgs hgL hconv (show 0≤A+1 by linarith)
      (fun k => (hdata (j k)).2.2.2.mono fun x hx => hx.trans (by nlinarith))
      (hflim.comp hj.tendsto_atTop) hψ
    refine ⟨?_,htest ψ hψ,
      measured_smooth_test_tendsto hS (fun k => hV (j k)) (hεlim.comp hj.tendsto_atTop) hψ,
      fun i => measured_smooth_coordinate_test_tendsto hS (fun k => hV (j k))
        (hεlim.comp hj.tendsto_atTop) hψ i⟩
    convert hmixed using 1
    funext k
    dsimp only [Function.comp_apply]
    have he : (fun x => ψ (V (j k) x)*(r (j k)^2*
        localGamma (hausdorff n X) hX.quadratic (f (j k)) (w (j k)) x))=
        fun x => r (j k)^2*(ψ (V (j k) x)*
          localGamma (hausdorff n X) hX.quadratic (f (j k)) (w (j k)) x) := by
      funext x
      ring
    rw [he,integral_const_mul]
    ring

end RegularPointCoordinates

end

end OAI
