import OAI.Geometry.RCD.Coordinates.PatchLocalization
import OAI.Geometry.RCD.Coordinates.PatchCenters
import OAI.Geometry.RCD.Metric.VolumeRegime
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-!
# Localized finite patch data from a uniform volume regime

The centers form a maximal finite net. Cutoffs are affine pullbacks of a
fixed Euclidean cutoff. The half-error volume regime, coarse separation,
and slow normalization growth bound the overlap. The smooth cutoff has
core radius two and support radius three.
-/

open Set Metric MeasureTheory
open scoped NNReal ENNReal ContDiff BigOperators InnerProductSpace

noncomputable section

attribute [local instance] Classical.propDecidable

namespace RegularPointCoordinates

variable {X E F : Type*} [MetricSpace X]

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate cutoff centered at a point of the original metric space. -/
def normalizedPatchCutoff (r : ℝ) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (y : X) (P : E) : ℝ :=
  psi (r⁻¹ • T y (P - u y))

/-- The original-space active domain for one actual normalized cutoff. -/
def normalizedPatchDomain (A : Set X) (r : ℝ) (u : X → E)
    (T : X → E →L[ℝ] F) (psi : F → ℝ) (y : X) : Set X :=
  {x | x ∈ A ∧ u x ∈ tsupport (normalizedPatchCutoff r u T psi y)}

omit [MetricSpace X] in
/-- Every chosen net center belongs to its own active patch. -/
theorem self_mem_normalizedPatchDomain (A : Set X) (r : ℝ) (u : X → E)
    (T : X → E →L[ℝ] F) (psi : F → ℝ) {y : X} (hy : y ∈ A)
    (hzero : psi 0 = 1) : y ∈ normalizedPatchDomain A r u T psi y := by
  refine ⟨hy, ?_⟩
  apply subset_tsupport
  simp only [Function.mem_support, normalizedPatchCutoff, sub_self, map_zero,
    smul_zero, hzero, ne_eq]
  norm_num

/-- The metric radius forced by the normalized support and coarse separation. -/
def patchLocalizationFactor (c M L : ℝ) : ℝ := max 1 ((M * L / c) ^ 2)

theorem patchLocalizationFactor_ge_one (c M L : ℝ) :
    1 ≤ patchLocalizationFactor c M L := le_max_left _ _

/-- Undoing the physical scaling in a pointed coordinate approximation
gives the actual frozen displacement estimate. -/
theorem normalized_pair_norm_estimate (u : X → E) (T : E →L[ℝ] F)
    (x y : X) {t R delta : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (hpoint : IsPointedApproximation y (0 : F) t R delta
      (fun z => t⁻¹ • T (u z - u y)))
    (hxy : dist x y ≤ R * t) :
    |‖T (u x - u y)‖ - dist x y| ≤ delta * t := by
  have hh := hpoint.2.1 x y hxy (by simpa using mul_nonneg hR ht.le)
  have hscaled : |t⁻¹ * ‖T (u x - u y)‖ - dist x y / t| ≤ delta := by
    simpa only [sub_self, map_zero, smul_zero, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] using hh
  have hm := mul_le_mul_of_nonneg_right hscaled ht.le
  calc
    _ = |(t⁻¹ * ‖T (u x - u y)‖ - dist x y / t) * t| := by
      congr 1
      field_simp [ht.ne']
    _ = |t⁻¹ * ‖T (u x - u y)‖ - dist x y / t| * t := by
      rw [abs_mul, abs_of_pos ht]
    _ ≤ _ := hm

/-- Approximation at four times the fine radius supplies the core-two
near-pair hypothesis of the finite patch construction. -/
theorem normalized_near_pair_le (u : X → E) (T : E →L[ℝ] F)
    (x y : X) {r : ℝ} (hr : 0 < r)
    (hpoint : IsPointedApproximation y (0 : F) (4 * r) (1 / 2) (1 / 4)
      (fun z => (4 * r)⁻¹ • T (u z - u y)))
    (hxy : dist x y ≤ r) : ‖T (u x - u y)‖ ≤ 2 * r := by
  have hh := normalized_pair_norm_estimate u T x y (by positivity)
    (by norm_num) hpoint (by linarith)
  have hu := (abs_le.mp hh).2
  linarith

/-- A coarse pointed approximation at the pair scale supplies a fixed
positive separation coefficient, independently of the pair distance. -/
theorem normalized_coarse_pair_lower (u : X → E) (T : E →L[ℝ] F)
    (x y : X) (hxy : x ≠ y)
    (hpoint : IsPointedApproximation y (0 : F) (4 * dist x y) (1 / 2) (1 / 8)
      (fun z => (4 * dist x y)⁻¹ • T (u z - u y))) :
    (1 / 2) * dist x y ≤ ‖T (u x - u y)‖ := by
  have hd := dist_pos.mpr hxy
  have hh := normalized_pair_norm_estimate u T x y (by positivity)
    (by norm_num) hpoint (by linarith)
  have hl := (abs_le.mp hh).1
  linarith

/-- A dimensional overlap bound in the half-error volume regime. -/
def patchOverlapBound (n : ℕ) (c M L : ℝ) : ℕ :=
  ⌈3 * (2 * patchLocalizationFactor c M L + 1) ^ n⌉₊

/-- Concrete geometric and smoothness properties needed before assigning
positive operators and energy centers to the finite patches. -/
structure IsLocalizedPatchCover (A : Set X) (r : ℝ≥0) (u : X → E)
    (s : Finset X) (phi : X → E → ℝ) (N : ℕ) (C L : ℝ) : Prop where
  center_mem : (s : Set X) ⊆ A
  separated : (s : Set X).Pairwise (fun y z => (r : ℝ) < dist y z)
  cutoff_smooth : ∀ y, ContDiff ℝ ∞ (phi y)
  cutoff_nonneg : ∀ y P, 0 ≤ phi y P
  cutoff_le_one : ∀ y P, phi y P ≤ 1
  active_localized : ∀ x ∈ A, ∀ y ∈ s, u x ∈ tsupport (phi y) →
    dist x y ≤ C * r
  active_card : ∀ x ∈ A, (s.filter (fun y => u x ∈ tsupport (phi y))).card ≤ N
  weight_one_cover : ∀ x ∈ A, ∃ y ∈ s,
    dist x y ≤ r ∧ phi y (u x) = 1 ∧ u x ∈ tsupport (phi y) ∧
      ball x r ⊆ ball y (L * r)

namespace IsLocalizedPatchCover

variable {A : Set X} {r : ℝ≥0} {u : X → E} {s : Finset X}
  {phi : X → E → ℝ} {N : ℕ} {C L : ℝ}

/-- The actual cutoff sum is positive throughout the covered domain. -/
theorem one_le_cutoff_sum (d : IsLocalizedPatchCover A r u s phi N C L)
    {x : X} (hx : x ∈ A) : 1 ≤ ∑ y ∈ s, phi y (u x) := by
  obtain ⟨y, hy, _, hyone, _, _⟩ := d.weight_one_cover x hx
  calc
    1 = phi y (u x) := hyone.symm
    _ ≤ _ := Finset.single_le_sum (fun z _ => d.cutoff_nonneg z (u x)) hy

/-- The same sum is bounded by the geometric overlap constant: inactive
terms vanish, so the total number of net points never enters the bound. -/
theorem cutoff_sum_le (d : IsLocalizedPatchCover A r u s phi N C L)
    {x : X} (hx : x ∈ A) : (∑ y ∈ s, phi y (u x)) ≤ N := by
  let active := s.filter (fun y => u x ∈ tsupport (phi y))
  have heq : (∑ y ∈ active, phi y (u x)) = ∑ y ∈ s, phi y (u x) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hy hnot
    apply image_eq_zero_of_notMem_tsupport
    intro ha
    exact hnot (Finset.mem_filter.mpr ⟨hy, ha⟩)
  calc
    _ = ∑ y ∈ active, phi y (u x) := heq.symm
    _ ≤ ∑ _y ∈ active, (1 : ℝ) := Finset.sum_le_sum (fun y _ => d.cutoff_le_one y _)
    _ = (active.card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast d.active_card x hx

/-- Active support, restricted to the actual coordinate image, comes
from points in a uniformly enlarged original metric ball. -/
theorem support_inter_image_subset (d : IsLocalizedPatchCover A r u s phi N C L)
    {y : X} (hy : y ∈ s) :
    tsupport (phi y) ∩ u '' A ⊆ u '' (A ∩ closedBall y (C * r)) := by
  rintro P ⟨hP, x, hx, rfl⟩
  exact ⟨x, ⟨hx, d.active_localized x hx y hy hP⟩, rfl⟩

/-- The overlap bound in the exact coordinate-domain form used by
`PatchIterationGeometry.active_card`. No injectivity is needed here. -/
theorem active_card_of_mem_image (d : IsLocalizedPatchCover A r u s phi N C L)
    {P : E} (hP : P ∈ u '' A) :
    (s.filter (fun y => P ∈ tsupport (phi y))).card ≤ N := by
  obtain ⟨x, hx, rfl⟩ := hP
  exact d.active_card x hx

end IsLocalizedPatchCover

end Normed

section EnergyCenters

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual active domains supply the nonemptiness needed to choose
fixed energy centers. They remain in the original bounded domain and the
localized metric ball, and their affine displacement obeys the required
three-times pair-energy bound at every active point. -/
theorem exists_normalized_patch_energy_centers
    (A : Set X) (r : ℝ≥0) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (s : Finset X) {N : ℕ} {C L D floor : ℝ}
    (d : IsLocalizedPatchCover A r u s (normalizedPatchCutoff r u T psi) N C L)
    (hzero : psi 0 = 1) (energy : X → ℝ) (hfloor : 0 < floor)
    (hlower : ∀ x ∈ A, floor ≤ energy x)
    (op : X → E →L[ℝ] E) (hD : 0 ≤ D)
    (hpair : ∀ y ∈ s, ∀ x ∈ normalizedPatchDomain A r u T psi y,
      ∀ z ∈ normalizedPatchDomain A r u T psi y,
      ⟪u x - u z, op y (u x - u z)⟫_ℝ ≤
        D * (r : ℝ) ^ 2 * (energy x + energy z)) :
    ∃ center : X → X, ∀ y ∈ s,
      center y ∈ A ∧ u (center y) ∈ tsupport (normalizedPatchCutoff r u T psi y) ∧
      dist (center y) y ≤ C * r ∧
      ∀ x ∈ normalizedPatchDomain A r u T psi y,
        ⟪u x - u (center y), op y (u x - u (center y))⟫_ℝ ≤
          (3 * D) * (r : ℝ) ^ 2 * energy x := by
  have hc (y : X) : ∃ z : X, y ∈ s →
      z ∈ normalizedPatchDomain A r u T psi y ∧
        ∀ x ∈ normalizedPatchDomain A r u T psi y, energy z ≤ 2 * energy x := by
    by_cases hy : y ∈ s
    · obtain ⟨z, hz, hb⟩ := exists_energy_center
        ⟨y, self_mem_normalizedPatchDomain A r u T psi (d.center_mem hy) hzero⟩
        hfloor (fun x hx => hlower x hx.1)
      exact ⟨z, fun _ => ⟨hz, hb⟩⟩
    · exact ⟨y, fun hy' => False.elim (hy hy')⟩
  choose center hcenter using hc
  refine ⟨center, ?_⟩
  intro y hy
  obtain ⟨hz, henergy⟩ := hcenter y hy
  refine ⟨hz.1, hz.2, d.active_localized _ hz.1 y hy hz.2, ?_⟩
  intro x hx
  exact centered_patch_energy_le u (op y) hD (henergy x hx) (hpair y hy x hx _ hz)

end EnergyCenters

/-- The half-error relative-volume estimate gives the two bounds used by
the packing argument, with their common Euclidean volume factor explicit. -/
theorem half_volume_bounds {V omega r : ℝ} {n : ℕ}
    (homega : 0 < omega) (hr : 0 < r)
    (hvolume : |V / (omega * r ^ n) - 1| ≤ 1 / 2) :
    (omega / 2) * r ^ n ≤ V ∧ V ≤ (3 * omega / 2) * r ^ n := by
  have hden : 0 < omega * r ^ n := mul_pos homega (pow_pos hr _)
  have hv := abs_le.mp hvolume
  have hl : (1 / 2 : ℝ) ≤ V / (omega * r ^ n) := by linarith [hv.1]
  have hu : V / (omega * r ^ n) ≤ (3 / 2 : ℝ) := by linarith [hv.2]
  have hl' := (le_div_iff₀ hden).mp hl
  have hu' := (div_le_iff₀ hden).mp hu
  constructor <;> nlinarith

section Volume

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The actual maximal net and affine cutoff satisfy localization,
weight-one covering and a scale-independent overlap bound. The measure
premise is only the uniform half-error ball-volume estimate. -/
theorem maximal_normalized_patch_cover
    (μ : Measure X) (A : Set X) (hA : TotallyBounded A)
    (r : ℝ≥0) (hr : 0 < r) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (n : ℕ) {R omega c M L : ℝ}
    (homega : 0 < omega) (hc : 0 < c) (hL : 2 ≤ L)
    (hscale : (patchLocalizationFactor c M L + 1) * r ≤ R)
    (hvolume : ∀ x ∈ A, ∀ t : ℝ, 0 < t → t ≤ R →
      |μ.real (ball x t) / (omega * t ^ n) - 1| ≤ 1 / 2)
    (hfinite : ∀ x t, μ (ball x t) ≠ (⊤ : ℝ≥0∞))
    (hsmooth : ContDiff ℝ ∞ psi)
    (hzero : ∀ z, 0 ≤ psi z) (hone : ∀ z, psi z ≤ 1)
    (hcore : ∀ z, ‖z‖ ≤ 2 → psi z = 1)
    (hsupport : tsupport psi ⊆ closedBall 0 L)
    (hnear : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r →
      ‖T y (u x - u y)‖ ≤ 2 * r)
    (hseparate : ∀ x ∈ A, ∀ y ∈ A, (r : ℝ) < dist x y →
      ∃ S : E →L[ℝ] F, c * dist x y ≤ ‖S (u x - u y)‖ ∧
        ‖S (u x - u y)‖ ^ 2 ≤ M ^ 2 * (dist x y / r) * ‖T y (u x - u y)‖ ^ 2) :
    IsLocalizedPatchCover A r u (maximalPatchNet r A)
      (normalizedPatchCutoff r u T psi) (patchOverlapBound n c M L)
      (patchLocalizationFactor c M L) L := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hL0 : 0 ≤ L := by linarith
  have hfac : 1 ≤ patchLocalizationFactor c M L := patchLocalizationFactor_ge_one _ _ _
  have hrR : (r : ℝ) / 2 ≤ R := by nlinarith
  have houter : 0 < patchLocalizationFactor c M L * r + r / 2 := by nlinarith
  have houterR : patchLocalizationFactor c M L * r + r / 2 ≤ R := by nlinarith
  have hloc (x : X) (hx : x ∈ A) (y : X) (hy : y ∈ maximalPatchNet r A)
      (ha : u x ∈ tsupport (normalizedPatchCutoff r u T psi y)) :
      dist x y ≤ patchLocalizationFactor c M L * r := by
    by_cases hd : dist x y ≤ r
    · nlinarith
    have hd' : (r : ℝ) < dist x y := lt_of_not_ge hd
    obtain ⟨S, hs, hg⟩ := hseparate x hx y (maximalPatchNet_subset r A hy) hd'
    exact active_cutoff_distance_le u (T y) S psi x y hr' hc hL0 hsupport ha
      (fun _ => hs) (fun _ => hg)
  refine {
    center_mem := maximalPatchNet_subset r A
    separated := maximalPatchNet_separated r A
    cutoff_smooth := ?_
    cutoff_nonneg := fun y P => hzero _
    cutoff_le_one := fun y P => hone _
    active_localized := hloc
    active_card := ?_
    weight_one_cover := ?_ }
  · intro y
    exact hsmooth.comp (((T y).contDiff.comp (contDiff_id.sub contDiff_const)).const_smul _)
  · intro x hx
    have hcount := active_maximalPatchNet_card_le μ A r x
      (fun y => u x ∈ tsupport (normalizedPatchCutoff r u T psi y)) n hr
      (show 0 < omega / 2 by positivity)
      (fun y hy ha => by simpa only [dist_comm] using hloc x hx y hy ha)
      (fun y hy _ => (half_volume_bounds homega (by positivity)
        (hvolume y (maximalPatchNet_subset r A hy) _ (by positivity) hrR)).1)
      (half_volume_bounds homega houter (hvolume x hx _ houter houterR)).2
      (hfinite x _)
    have hratio : (3 * omega / 2) / (omega / 2) = 3 := by field_simp [homega.ne']
    simpa only [hratio, patchOverlapBound] using hcount
  · intro x hx
    exact exists_weight_one_covering_patch A hA r hr u T psi hcore
      (fun x hx y hy hd => hnear x hx y (maximalPatchNet_subset r A hy) hd) x hx hL

/-- Properness is only used to turn a bounded, possibly nonclosed domain
into the totally bounded set required for the actual finite net. -/
theorem bounded_maximal_normalized_patch_cover [ProperSpace X]
    (μ : Measure X) (A : Set X) (hA : Bornology.IsBounded A)
    (r : ℝ≥0) (hr : 0 < r) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (n : ℕ) {R omega c M L : ℝ}
    (homega : 0 < omega) (hc : 0 < c) (hL : 2 ≤ L)
    (hscale : (patchLocalizationFactor c M L + 1) * r ≤ R)
    (hvolume : ∀ x ∈ A, ∀ t : ℝ, 0 < t → t ≤ R →
      |μ.real (ball x t) / (omega * t ^ n) - 1| ≤ 1 / 2)
    (hfinite : ∀ x t, μ (ball x t) ≠ (⊤ : ℝ≥0∞))
    (hsmooth : ContDiff ℝ ∞ psi)
    (hzero : ∀ z, 0 ≤ psi z) (hone : ∀ z, psi z ≤ 1)
    (hcore : ∀ z, ‖z‖ ≤ 2 → psi z = 1)
    (hsupport : tsupport psi ⊆ closedBall 0 L)
    (hnear : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ r → ‖T y (u x - u y)‖ ≤ 2 * r)
    (hseparate : ∀ x ∈ A, ∀ y ∈ A, (r : ℝ) < dist x y →
      ∃ S : E →L[ℝ] F, c * dist x y ≤ ‖S (u x - u y)‖ ∧
        ‖S (u x - u y)‖ ^ 2 ≤ M ^ 2 * (dist x y / r) * ‖T y (u x - u y)‖ ^ 2) :
    IsLocalizedPatchCover A r u (maximalPatchNet r A)
      (normalizedPatchCutoff r u T psi) (patchOverlapBound n c M L)
      (patchLocalizationFactor c M L) L :=
  maximal_normalized_patch_cover μ A (hA.isCompact_closure.totallyBounded.subset subset_closure)
    r hr u T psi n homega hc hL hscale hvolume hfinite hsmooth hzero hone hcore hsupport hnear hseparate

/-- The coordinate premises can be stated as actual pointed
approximations and slow norm growth. Their separation and near-pair
consequences are derived before constructing the localized patch cover. -/
theorem normalized_patch_cover_of_pointed_approximations [ProperSpace X]
    (μ : Measure X) (A : Set X) (hA : Bornology.IsBounded A)
    (r : ℝ≥0) (hr : 0 < r) (u : X → E) (T : X → E →L[ℝ] F)
    (psi : F → ℝ) (n : ℕ) {R omega M L exponent : ℝ}
    (homega : 0 < omega) (hM : 0 ≤ M) (hL : 2 ≤ L) (hexponent : exponent ≤ 1 / 2)
    (hscale : (patchLocalizationFactor (1 / 2) M L + 1) * r ≤ R)
    (hvolume : ∀ x ∈ A, ∀ t : ℝ, 0 < t → t ≤ R →
      |μ.real (ball x t) / (omega * t ^ n) - 1| ≤ 1 / 2)
    (hfinite : ∀ x t, μ (ball x t) ≠ (⊤ : ℝ≥0∞))
    (hsmooth : ContDiff ℝ ∞ psi)
    (hzero : ∀ z, 0 ≤ psi z) (hone : ∀ z, psi z ≤ 1)
    (hcore : ∀ z, ‖z‖ ≤ 2 → psi z = 1)
    (hsupport : tsupport psi ⊆ closedBall 0 L)
    (hpoint : ∀ y ∈ A, IsPointedApproximation y (0 : F) (4 * r) (1 / 2) (1 / 4)
      (fun z => (4 * r)⁻¹ • T y (u z - u y)))
    (hcoarse : ∀ x ∈ A, ∀ y ∈ A, (r : ℝ) < dist x y →
      ∃ S : E →L[ℝ] F,
        IsPointedApproximation y (0 : F) (4 * dist x y) (1 / 2) (1 / 8)
          (fun z => (4 * dist x y)⁻¹ • S (u z - u y)) ∧
        ‖S (u x - u y)‖ ≤
          M * (dist x y / r) ^ exponent * ‖T y (u x - u y)‖) :
    IsLocalizedPatchCover A r u (maximalPatchNet r A)
      (normalizedPatchCutoff r u T psi) (patchOverlapBound n (1 / 2) M L)
      (patchLocalizationFactor (1 / 2) M L) L := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  apply bounded_maximal_normalized_patch_cover μ A hA r hr u T psi n homega
    (by norm_num) hL hscale hvolume hfinite hsmooth hzero hone hcore hsupport
  · intro x _ y hy hxy
    exact normalized_near_pair_le u (T y) x y hr' (hpoint y hy) hxy
  · intro x hx y hy hfar
    obtain ⟨S, hS, hslow⟩ := hcoarse x hx y hy hfar
    exact ⟨S, normalized_coarse_pair_lower u S x y (dist_pos.mp (hr'.trans hfar)) hS,
      squared_growth_of_slow_norm_growth (T y) S (u x - u y) hr' hfar.le hM hexponent hslow⟩

end Volume

section SmoothCutoff

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An actual smooth core-two, support-three cutoff on the coordinate space. -/
def patchCoreBump : ContDiffBump (0 : F) := ⟨2, 3, by norm_num, by norm_num⟩

theorem patchCoreBump_properties :
    ContDiff ℝ ∞ (patchCoreBump (F := F)) ∧
    (∀ z, 0 ≤ patchCoreBump (F := F) z) ∧
    (∀ z, patchCoreBump (F := F) z ≤ 1) ∧
    (∀ z, ‖z‖ ≤ 2 → patchCoreBump (F := F) z = 1) ∧
    tsupport (patchCoreBump (F := F)) ⊆ closedBall 0 3 := by
  refine ⟨ContDiffBump.contDiff _, fun _ => ContDiffBump.nonneg _,
    fun _ => ContDiffBump.le_one _, ?_, ?_⟩
  · intro z hz
    exact ContDiffBump.one_of_mem_closedBall _ (by simpa [patchCoreBump] using hz)
  · rw [ContDiffBump.tsupport_eq]
    exact Subset.rfl

end SmoothCutoff

section RegularVolume

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published volume convergence, Bishop--Gromov and density inputs
give one working neighborhood and one uniform overlap constant for every
smaller-scale normalized patch family. The remaining premises concern only
the coordinate normalizations: near-pair control and coarse separation
with slow growth. No patch conclusion is assumed. -/
theorem exists_regular_patch_cover_radius
    (μ : Measure X) (m : ℕ) {p : X} {a omega rho c M : ℝ}
    (ha : 0 ≤ a) (homega : 0 < omega) (hrho : 0 < rho) (hc : 0 < c)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence μ (m + 1) p omega)
    (hcomparison : BallVolumeComparison μ (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper μ (comparisonModelVolume m a) y omega)
    (hfinite : ∀ y t, μ (ball y t) ≠ (⊤ : ℝ≥0∞)) :
    ∃ R : ℝ, 0 < R ∧ R ≤ rho ∧
      ∀ (r : ℝ≥0), 0 < r → (patchLocalizationFactor c M 3 + 1) * r ≤ R →
      ∀ (u : X → E) (T : X → E →L[ℝ] F),
      (∀ x ∈ ball p R, ∀ y ∈ ball p R, dist x y ≤ r →
        ‖T y (u x - u y)‖ ≤ 2 * r) →
      (∀ x ∈ ball p R, ∀ y ∈ ball p R, (r : ℝ) < dist x y →
        ∃ S : E →L[ℝ] F, c * dist x y ≤ ‖S (u x - u y)‖ ∧
          ‖S (u x - u y)‖ ^ 2 ≤ M ^ 2 * (dist x y / r) * ‖T y (u x - u y)‖ ^ 2) →
      IsLocalizedPatchCover (ball p R) r u (maximalPatchNet r (ball p R))
        (normalizedPatchCutoff r u T (patchCoreBump (F := F)))
        (patchOverlapBound (m + 1) c M 3) (patchLocalizationFactor c M 3) 3 := by
  obtain ⟨R, hR, hRrho, hvol⟩ := exists_uniform_volume_neighborhood m ha homega
    (epsilon := 1 / 2) (by norm_num) (by norm_num) hrho
    hcompact hregular hvolume hcomparison hdensity hfinite
  refine ⟨R, hR, hRrho, ?_⟩
  intro r hr hscale u T hnear hsep
  have hp := patchCoreBump_properties (F := F)
  apply bounded_maximal_normalized_patch_cover μ (ball p R) isBounded_ball
    r hr u T (patchCoreBump (F := F)) (m + 1) homega hc (by norm_num) hscale
  · intro x hx t ht htR
    exact hvol x (by simpa only [dist_comm] using (mem_ball.mp hx).le) t ht htR
  · exact hfinite
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2
  · exact hnear
  · exact hsep

end RegularVolume

end RegularPointCoordinates

end

end OAI
