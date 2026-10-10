import OAI.MeasureTheory.Falconer.Angular.CircleAngularBins
import OAI.MeasureTheory.Falconer.Graphs.GraphDirectionStability
import OAI.MeasureTheory.Falconer.Angular.InverseCircleArcLength
import OAI.MeasureTheory.Falconer.Geometry.SelectedBinAmplitude

namespace OAI

namespace PlanarFalconer
attribute [local instance] Classical.propDecidable
open Set Metric
open scoped ContDiff Topology

def AngularBinActive (n j : ℕ) (e : UnitCircle) (radius : ℝ) : Prop :=
  ∃ dir ∈ tsupport (circleAngularBin n j), dist e dir < radius

noncomputable def inactiveAngularLabels (n : ℕ) (e : UnitCircle) (radius : ℝ) : Finset ℕ :=
  (Finset.range n).filter (fun j => ¬ AngularBinActive n j e radius)

theorem inactiveAngularLabels_separation (n : ℕ) (e : UnitCircle) (radius : ℝ)
    {j : ℕ} (hj : j ∈ inactiveAngularLabels n e radius)
    {dir : UnitCircle} (hd : dir ∈ tsupport (circleAngularBin n j)) :
    radius ≤ dist e dir := by
  classical
  exact le_of_not_gt (fun hh => (Finset.mem_filter.mp hj).2 ⟨dir,hd,hh⟩)

theorem inactive_angular_sum_support (n : ℕ) (e : UnitCircle) (radius : ℝ) :
    tsupport (fun θ => ∑ j ∈ inactiveAngularLabels n e radius, periodicAngularBin n j θ) ⊆
      {θ | radius ≤ dist e (sourceUnitDirection θ)} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hh
    apply hθ
    apply Finset.sum_eq_zero
    intro j hj
    by_contra hj0
    have hmem : sourceUnitDirection θ ∈ tsupport (circleAngularBin n j) := by
      apply subset_closure
      simpa only [Function.mem_support, circleAngularBin_comp] using hj0
    exact hh (inactiveAngularLabels_separation n e radius hj hmem)
  · exact isClosed_le continuous_const (continuous_const.dist continuous_sourceUnitDirection)

theorem sourceUnitDirection_dist_sq (θ φ : ℝ) :
    dist (sourceUnitDirection θ) (sourceUnitDirection φ)^2 = 2-2*Real.cos (θ-φ) := by
  change dist (sourceDirection θ) (sourceDirection φ)^2 = _
  rw [dist_eq_norm, norm_sub_sq_real, norm_sourceDirection, norm_sourceDirection, inner_sourceDirection]
  ring

theorem sine_separation_of_forward_chord {θ φ δ : ℝ} (hδ : 0 ≤ δ)
    (hcos : 0 ≤ Real.cos (θ-φ))
    (hd : 2*δ ≤ dist (sourceUnitDirection θ) (sourceUnitDirection φ)) :
    δ ≤ |Real.sin (θ-φ)| := by
  have he := sourceUnitDirection_dist_sq θ φ
  have htrig := Real.sin_sq_add_cos_sq (θ-φ)
  have hc := Real.cos_le_one (θ-φ)
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ 2*δ) dist_nonneg |>.mpr hd
  have hprod : 0 ≤ Real.cos (θ-φ)*(1-Real.cos (θ-φ)) := mul_nonneg hcos (sub_nonneg.mpr hc)
  have habs := sq_abs (Real.sin (θ-φ))
  nlinarith [abs_nonneg (Real.sin (θ-φ))]

theorem inactive_bin_sine_separation {δ φ : ℝ} (hδ : 0 < δ) (e : UnitCircle)
    (hmove : dist (sourceUnitDirection φ) e ≤ δ) {w f : ℝ → ℂ}
    (hcone : ∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ))
    {θ : ℝ}
    (hθ : θ ∈ tsupport (fun y => w y * selectedBinAmplitude δ
      (inactiveAngularLabels (angularBinCount δ) e (3*δ)) f y)) :
    δ ≤ |Real.sin (θ-φ)| := by
  have hw : θ ∈ tsupport w := tsupport_mul_subset_left hθ
  have hs : θ ∈ tsupport (fun y => ∑ j ∈ inactiveAngularLabels (angularBinCount δ) e (3*δ),
      periodicAngularBin (angularBinCount δ) j y) := by
    have hb := tsupport_mul_subset_left (tsupport_mul_subset_right hθ)
    apply closure_minimal (s := Function.support (fun y =>
      ((∑ j ∈ inactiveAngularLabels (angularBinCount δ) e (3*δ),
        periodicAngularBin (angularBinCount δ) j y : ℝ) : ℂ)))
      (fun y hy => subset_closure (by simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hy))
      isClosed_closure hb
  have hsep := inactive_angular_sum_support (angularBinCount δ) e (3*δ) hs
  have hchord := excluded_direction_separation (δ := δ) (ε := δ) (K := 3) hmove hsep
  apply sine_separation_of_forward_chord hδ.le (hcone θ hw)
  rw [dist_comm] at hchord
  linarith

end PlanarFalconer

end OAI
