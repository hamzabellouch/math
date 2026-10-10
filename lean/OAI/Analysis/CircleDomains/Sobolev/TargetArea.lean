import OAI.Analysis.CircleDomains.LengthArea
import OAI.Analysis.CircleDomains.Sobolev.SourceArea

namespace OAI

/-!
# Target area from the exterior area theorem

Ahlfors, *Conformal Invariants* (1973), Exterior Area Theorem, supplies the
area bound for the set omitted by a normalized univalent exterior map.
The numerical bound yields the target-area estimate by change of variables
and disjointness of the image and omitted disks.
-/

open MeasureTheory Metric Set Function Bornology
open scoped ENNReal

namespace CircleDomainRigidity

/-- The specialization of the published exterior area bound needed here.
The map is evaluated only outside the closed source disk. Univalence and
principal normalization are the hypotheses needed to obtain this bound
from the exterior area theorem; this predicate is its numerical conclusion. -/
def ExteriorOmittedAreaBound (f : ℂ → ℂ) (R : ℝ) : Prop :=
  volume ((f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi * R ^ 2)

/-- Complex change of variables identifies image area with Dirichlet area
of an injective holomorphic map. -/
theorem integral_norm_deriv_sq_eq_image_area {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hinj : InjOn f U) :
    (∫ z in U, ‖deriv f z‖ ^ 2) = (volume (f '' U)).toReal := by
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ
  have hL : ∀ z ∈ U, HasFDerivWithinAt f (L z) U z :=
    fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (L z).det = ‖deriv f z‖ ^ 2 := by
    simp [L, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hU hL hinj
    (fun _ : ℂ => (1 : ℝ))
  simpa [hdet, measureReal_def] using h.symm

/-- Finite image area also gives actual integrability of the squared
holomorphic derivative, so the Bochner integral cannot vanish by being
undefined. -/
theorem integrable_norm_deriv_sq_of_image_area_finite {f : ℂ → ℂ} {U : Set ℂ}
    (hU : MeasurableSet U) (hf : ∀ z ∈ U, DifferentiableAt ℂ f z)
    (hinj : InjOn f U) (hfinite : volume (f '' U) ≠ ∞) :
    Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict U) := by
  let L : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ
  have hL : ∀ z ∈ U, HasFDerivWithinAt f (L z) U z :=
    fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet (z : ℂ) : (L z).det = ‖deriv f z‖ ^ 2 := by
    simp [L, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]
  have h1 : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (f '' U) volume :=
    integrableOn_const hfinite
  have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    volume hU hL hinj (fun _ : ℂ => (1 : ℝ))).mp h1
  simpa [hdet, IntegrableOn] using h

/-- The genuine exterior-area input yields target-radius summability,
squared-derivative integrability, and the complete target-area estimate.
The only geometric hypotheses on the target disks are disjoint interiors
and disjointness from the image of the source domain. -/
theorem targetArea_of_exterior_area_bound {ι : Type*} [Countable ι]
    {f : ℂ → ℂ} {D : Set ℂ} (centers : ι → ℂ) (s : ι → ℝ) (R : ℝ)
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D)
    (hExterior : (closedBall (0 : ℂ) R)ᶜ ⊆ D)
    (hs : ∀ j, 0 ≤ s j)
    (hpair : Pairwise (Disjoint on fun j => ball (centers j) (s j)))
    (hdisj : ∀ j, Disjoint (f '' D) (ball (centers j) (s j)))
    (harea : ExteriorOmittedAreaBound f R) :
    Summable (fun j => s j ^ 2) ∧
    Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict (D ∩ ball 0 R)) ∧
    (∫ z in D ∩ ball 0 R, ‖deriv f z‖ ^ 2) +
      Real.pi * (∑' j, s j ^ 2) ≤ Real.pi * R ^ 2 := by
  let U := D ∩ ball (0 : ℂ) R
  let O := (f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ
  have hU : IsOpen U := hD.inter isOpen_ball
  have hUinD : U ⊆ D := inter_subset_left
  have hUO : f '' U ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have hwz : w = z := hinj (hExterior hw) hz.1 heq
    exact hw (hwz ▸ ball_subset_closedBall hz.2)
  have hdiskO : ∀ j, ball (centers j) (s j) ⊆ O := by
    intro j z hz ⟨w, hw, heq⟩
    exact Set.disjoint_left.mp (hdisj j) ⟨w, hExterior hw, heq⟩ hz
  have hdisjU : ∀ j, Disjoint (f '' U) (ball (centers j) (s j)) :=
    fun j => (hdisj j).mono_left (image_mono hUinD)
  have hbound : volume (f '' U) + ∑' j, volume (ball (centers j) (s j)) ≤
      ENNReal.ofReal (Real.pi * R ^ 2) :=
    (measure_source_add_disks_le volume (fun j => ball (centers j) (s j))
      (fun _ => measurableSet_ball) hpair hdisjU hUO hdiskO).trans harea
  have htotalFinite : volume (f '' U) + ∑' j, volume (ball (centers j) (s j)) < ∞ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have himageFinite : volume (f '' U) ≠ ∞ :=
    ne_of_lt ((le_add_right le_rfl).trans_lt htotalFinite)
  have hsumFinite : (∑' j, volume (ball (centers j) (s j))) ≠ ∞ :=
    ne_of_lt ((le_add_left le_rfl).trans_lt htotalFinite)
  have hsSum : Summable (fun j => s j ^ 2) := by
    have hsum := (ENNReal.summable_toReal hsumFinite).congr
      (fun j => real_volume_ball (centers j) (hs j))
    exact (summable_mul_left_iff Real.pi_ne_zero).mp hsum
  have hdiff : ∀ z ∈ U, DifferentiableAt ℂ f z :=
    fun z hz => (hf z hz.1).differentiableAt (hD.mem_nhds hz.1)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_add himageFinite hsumFinite,
    ENNReal.tsum_toReal_eq (fun _ => ne_of_lt measure_ball_lt_top),
    ENNReal.toReal_ofReal (mul_nonneg Real.pi_pos.le (sq_nonneg R))] at hreal
  have hsumEq : (∑' j, (volume (ball (centers j) (s j))).toReal) =
      Real.pi * (∑' j, s j ^ 2) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun j => real_volume_ball (centers j) (hs j))
  rw [hsumEq, ← integral_norm_deriv_sq_eq_image_area hU.measurableSet hdiff
    (hinj.mono hUinD)] at hreal
  exact ⟨hsSum, integrable_norm_deriv_sq_of_image_area_finite hU.measurableSet hdiff
    (hinj.mono hUinD) himageFinite, hreal⟩

/-- On a bounded measurable portion of a holomorphic domain, square
integrability of the derivative implies integrability of its modulus. -/
theorem integrable_norm_deriv_of_sq {f : ℂ → ℂ} {D U : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hU : MeasurableSet U) (hbU : IsBounded U) (hUD : U ⊆ D)
    (hsq : Integrable (fun z => ‖deriv f z‖ ^ 2) (volume.restrict U)) :
    Integrable (fun z => ‖deriv f z‖) (volume.restrict U) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hbU.measure_lt_top.ne
  have hm : AEStronglyMeasurable (fun z => ‖deriv f z‖) (volume.restrict U) :=
    ((hf.deriv hD).continuousOn.norm.mono hUD).aestronglyMeasurable hU
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hm).mpr hsq)

end CircleDomainRigidity

end OAI
