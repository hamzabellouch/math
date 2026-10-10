import Mathlib
import OAI.Probability.Ballisticity.Crossings.OffDiagonalCenteredCross
import OAI.Probability.Ballisticity.Estimates.RestartSupportedBound

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_boundary_cross_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0<r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (F : ℕ → BoundaryData d → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀ i j, ‖F i j‖≤C)
    (g : ℝ →ᵇ ℝ) (hg : ∀ z, |g z|≤1) {a t : ℝ} (ha : 0<a) (ht : 0<t)
    (hgzero : ∀ z, |z|≤a → g z=0) (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
    ∀ᶠ i in atTop, |∫ P, F i (D i P)*
      g (signedCoordinate f ((boundaryTerminal (D i P)).1-(boundaryTerminal (D i P)).2)/r i)*
      centeredClipCross ℓ f (θ i) (r i) ⌊t*n i⌋₊ w
        (boundaryTerminal (D i P)).1 (boundaryTerminal (D i P)).2 (Y i P)
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      C*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))+ε) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)
  let D := fun i => boundaryData ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let Y := fun i => boundarySuffix ℓ ((signedHeight e (x i)+H i : ℤ) : ℝ)
  let κ := fun z : BoundaryData d => sharedConditionedPairLaw ν ℓ (boundaryTerminal z).1 (boundaryTerminal z).2
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  let : ∀ j, IsProbabilityMeasure (κ j) := fun j => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_positive ν hue ℓ (signed_direction_unit e) htrans _ _))
  have hu := shared_centered_cross_uniform_bound ν hue e f hef htrans r hrpos hr ha ht w hε
  filter_upwards [hu] with i hi
  apply countable_restart_supported_bound (μ i) (D i) (Y i) κ (measurable_boundaryData _ _)
    (measurable_boundarySuffix _ _)
    (shared_boundaryData_map ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i) (hH i))
    (fun z => signedHeight e (boundaryTerminal z).1=signedHeight e (boundaryTerminal z).2) ?_
    (fun j => F i j*g (signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i))
    (fun j => centeredClipCross ℓ f _ (r i) _ w (boundaryTerminal j).1 (boundaryTerminal j).2)
    (fun j => measurable_centeredClipCross _ _ _ _ _ _ _ _) C ((w:ℝ)^2) _ hC (by positivity) ?_
    (fun j P => centeredClipCross_bound _ _ _ _ _ _ _ _ _) ?_
  · filter_upwards [shared_boundaryTimes_spec ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
      (signedHeight_projection e) (signedHeight_step_le e) (x i) (y i) (hxy i) (H i) (hH i)] with P hP
    simp only [D,boundaryTerminal_data]
    have he := hP.2.2.1.2.2
    rw [signedHeight_projection e,signedHeight_projection e] at he
    exact_mod_cast he
  · intro j
    rw [norm_mul,Real.norm_eq_abs (g _)]
    exact (mul_le_mul (hF i j) (hg _) (abs_nonneg _) hC).trans_eq (mul_one C)
  · intro j hj hnon
    apply hi _ _ hj
    have hgn : g (signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i) ≠ 0 := by
      intro hz
      exact hnon (by rw [hz,mul_zero])
    have hsep : a≤|signedCoordinate f ((boundaryTerminal j).1-(boundaryTerminal j).2)/r i| := by
      exact le_of_lt (lt_of_not_ge fun h => hgn (hgzero _ h))
    rw [abs_div,abs_of_pos (hrpos i)] at hsep
    have hh := (le_div_iff₀ (hrpos i)).mp hsep
    simpa only [signedCoordinate_sub,abs_sub_comm] using hh

end DirectionalTransience

end

end

end OAI
