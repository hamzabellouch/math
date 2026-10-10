import OAI.Analysis.CircleDomains.LengthArea
import OAI.Analysis.CircleDomains.Sobolev.SourceArea
import OAI.Analysis.CircleDomains.Sobolev.TargetArea
import OAI.Analysis.CircleDomains.Rigidity.FluxLimit

namespace OAI

/-!
# Rigidity reduction with geometric source-area control

Source area and square-summability of the source radii follow from the
geometry of disjoint source disks. The target area follows from an exterior-area
bound. Together with the finite-hole flux estimate, these bounds force rigidity
through the length-area argument.
-/

open MeasureTheory Set Metric Filter Bornology Function
open scoped Topology

namespace CircleDomainRigidity

/-- A principal-normalized conformal map is the identity once the target
area and flux estimates are established. Source area and square-summable
source radii follow from disjoint disk geometry. -/
theorem identity_of_disk_geometry_and_target_flux {ι : Type*} [Countable ι]
    {f : ℂ → ℂ} {D : Set ℂ} (centers : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hDinf : IsBounded Dᶜ)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (r j)))
    (hdisj : ∀ j, Disjoint D (ball (centers j) (r j)))
    (hcontain : ∀ j, ball (centers j) (r j) ⊆ ball 0 R)
    (hi : Integrable (fun z => ‖deriv f z‖) (volume.restrict (D ∩ ball 0 R)))
    (hi2 : Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict (D ∩ ball 0 R)))
    (hs : Summable (fun j => s j ^ 2))
    (htarget : (∫ z in D ∩ ball 0 R, ‖deriv f z‖ ^ 2) +
      Real.pi * (∑' j, s j ^ 2) ≤ Real.pi * R ^ 2)
    (hflux : 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  have hrSum : Summable (fun j => r j ^ 2) :=
    summable_radii_sq centers r R hr hpair hcontain
  have hsourceReal : (volume (D ∩ ball 0 R)).toReal +
      Real.pi * (∑' j, r j ^ 2) ≤ Real.pi * R ^ 2 :=
    sourceArea_real_le centers r R hr hR hpair
      (fun j => (hdisj j).mono_left inter_subset_left)
      inter_subset_right hcontain
  have hsource : (∫ _ in D ∩ ball 0 R, (1 : ℝ)) +
      Real.pi * (∑' j, r j ^ 2) ≤ Real.pi * R ^ 2 := by
    simpa [measureReal_def] using hsourceReal
  exact LengthArea.identity_of_length_area_estimates hD hconn hf hDinf hnorm
    (hD.inter isOpen_ball) hWne (isBounded_ball.subset inter_subset_right)
    inter_subset_left hi hi2 hrSum hs hsource htarget hflux

/-- All area and integrability premises follow from geometric disjointness
and the exterior omitted-area bound, under the limiting-flux inequality. -/
theorem identity_of_disk_geometry_exterior_area_and_flux
    {ι : Type*} [Countable ι] {f : ℂ → ℂ} {D : Set ℂ}
    (sourceCenters targetCenters : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hSourcePair : Pairwise (Disjoint on fun j => ball (sourceCenters j) (r j)))
    (hSourceDisj : ∀ j, Disjoint D (ball (sourceCenters j) (r j)))
    (hSourceContain : ∀ j, ball (sourceCenters j) (r j) ⊆ ball 0 R)
    (hTargetPair : Pairwise (Disjoint on fun j => ball (targetCenters j) (s j)))
    (hTargetDisj : ∀ j, Disjoint (f '' D) (ball (targetCenters j) (s j)))
    (harea : ExteriorOmittedAreaBound f R)
    (hflux : 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  obtain ⟨hsSum, hi2, htarget⟩ := targetArea_of_exterior_area_bound
    targetCenters s R hD hf hinj hExterior hs hTargetPair hTargetDisj harea
  have hbounded : IsBounded (D ∩ ball (0 : ℂ) R) :=
    isBounded_ball.subset inter_subset_right
  have hi := integrable_norm_deriv_of_sq hD hf
    (hD.inter isOpen_ball).measurableSet hbounded inter_subset_left hi2
  have hDinf : IsBounded Dᶜ :=
    isBounded_closedBall.subset (compl_subset_comm.mp hExterior)
  exact identity_of_disk_geometry_and_target_flux sourceCenters r s R hD hconn hf
    hDinf hnorm hR hr hWne hSourcePair hSourceDisj hSourceContain
    hi hi2 hsSum htarget hflux

/-- The finite-hole flux estimates suffice for normalized rigidity. Source
and target geometry imply the required square-summability, so the remaining
tail tends to zero without any separate convergence assumption. -/
theorem identity_of_disk_geometry_exterior_area_and_finite_flux
    {ι : Type*} [Countable ι] {f : ℂ → ℂ} {D : Set ℂ}
    (sourceCenters targetCenters : ι → ℂ) (r s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hnorm : Tendsto (fun z : ℂ => f z - z) (cobounded ℂ) (𝓝 0))
    (hR : 0 ≤ R) (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hWne : (D ∩ ball 0 R).Nonempty)
    (hSourcePair : Pairwise (Disjoint on fun j => ball (sourceCenters j) (r j)))
    (hSourceDisj : ∀ j, Disjoint D (ball (sourceCenters j) (r j)))
    (hSourceContain : ∀ j, ball (sourceCenters j) (r j) ⊆ ball 0 R)
    (hTargetPair : Pairwise (Disjoint on fun j => ball (targetCenters j) (s j)))
    (hTargetDisj : ∀ j, Disjoint (f '' D) (ball (targetCenters j) (s j)))
    (harea : ExteriorOmittedAreaBound f R)
    (hfinite : ∀ F : Finset ι, 2 * (Real.pi * R ^ 2) ≤
      2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑ j ∈ F, r j * s j) +
      16 * (∑' j : {j // j ∉ F}, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  have hrSum := summable_radii_sq sourceCenters r R hr hSourcePair hSourceContain
  have hsSum := (targetArea_of_exterior_area_bound
    targetCenters s R hD hf hinj hExterior hs hTargetPair hTargetDisj harea).1
  have hflux := limiting_flux_of_finite_hole_estimates hrSum hsSum hfinite
  exact identity_of_disk_geometry_exterior_area_and_flux
    sourceCenters targetCenters r s R hD hconn hf hinj hExterior hnorm hR hr hs
    hWne hSourcePair hSourceDisj hSourceContain hTargetPair hTargetDisj harea hflux

end CircleDomainRigidity

end OAI
