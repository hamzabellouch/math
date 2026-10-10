import OAI.Geometry.RCD.Coordinates.HarmonicCoordinatePair
import OAI.Geometry.RCD.Sobolev.HarmonicLinearEnergyL1
import OAI.Geometry.RCD.Harmonic.MixedGramL1

namespace OAI

/-! # The actual finite harmonic coordinate family has the Euclidean Gram limit -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_coordinate_gram {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*r k^2) (hcurv5 : ∀ k, -1≤K*(5*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w i k))
    (hnorm : ∀ i k, harmonicTargetNorm hX (p k) (5*r k) (w i k)≤7)
    (hconv : ∀ i W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V k x i|≤δ) :
    (∀ i β, 0<β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (3*r k)),
        r k^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w i k) x≤1+β) ∧
    (∀ i j, Tendsto (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w j k) x-(if i=j then 1 else 0)|
        ∂hausdorff n X) atTop (𝓝 0)) := by
  have hdiag (i : Fin n) : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w i k) x-1| ∂hausdorff n X)
      atTop (𝓝 0) :=
    hX.harmonic_linear_energy_l1 hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
      (w i) (hw i) (by norm_num : (0:ℝ)<7) (hnorm i) (EuclideanSpace.proj i)
      (coordinate_projection_norm i) (hconv i)
  constructor
  · intro i
    exact hX.harmonic_linear_sharp hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
      (w i) (hw i) (by norm_num : (0:ℝ)<7) (hnorm i) (EuclideanSpace.proj i)
      (coordinate_projection_norm i).le (hconv i)
  · intro i j
    by_cases hij : i=j
    · subst j
      simpa using hdiag i
    · obtain ⟨hh,hm,hv⟩ := hX.harmonic_coordinate_pair_data p r V w hw hnorm hconv i j
      have hp := hX.harmonic_linear_energy_l1 hn p r ε V hr hcurv hcurv5 hε hε1 hεlim hV
        (fun k => (Real.sqrt 2)⁻¹ • (w i k+w j k)) hh (by norm_num : (0:ℝ)<14) hm
        ((Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)+EuclideanSpace.proj j))
        (coordinate_pair_unit_norm i j hij) hv
      simpa only [ite_eq_right hij,sub_zero] using mixed_gram_l1_tendsto (hausdorff n X) hX.quadratic
        (fun k => ball (p k) (2*r k)) (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
        r (fun k => ((hausdorff n X).real (ball (p k) (2*r k)))⁻¹) (fun _ => by positivity)
        (w i) (w j) (hdiag i) (hdiag j) hp

end RegularPointCoordinates

end

end OAI
