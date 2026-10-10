import OAI.Geometry.RCD.Coordinates.RegularPatchSelection
import OAI.Geometry.RCD.Coordinates.PatchDirectionalBounds

namespace OAI

/-! # Cumulative mass bounds for the selected actual patch family -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularPatchSelection

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
  {a κ B J C A Cχ enlargement zeta eta Cpin budget : ℝ}
  {e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta}
  {psi : EuclideanGevreyCutoff n} {f : RegularPinchingField e.heat Cpin budget}
  (p : RegularPatchSelection e.heat psi.value f)

def operator (i : ℕ) (y : X) : Euclidean n →L[ℝ] Euclidean n :=
  e.heat.pinchingMassMatrix (p.center i y).val (p.center i y).property (e.heat.shift + i)

def activePatchesAt (_p : RegularPatchSelection e.heat psi.value f) (q : X) (i : ℕ) : Finset X := by
  classical
  exact (e.heat.patchNet i).filter (fun y => e.heat.values q ∈ tsupport (e.heat.patchCutoff psi.value i y))

/-- Both cumulative estimates now concern the actual active net and its
fixed energy centers, including the original singular Bochner mass. -/
theorem cumulative (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1 / 64)
    (hCχ : 0 ≤ Cχ) (henlargement : 1 ≤ enlargement)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4) :
    ∃ Theta tau : ℝ, 0 < Theta ∧ 0 < tau ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ tau →
    (∀ i, 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) ^ 2) ≤ epsilon) →
    ∀ q, q ∈ e.heat.patchRegion → ∀ (xi : Euclidean n) (k : ℕ),
      (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k, ⟪xi, patchMass (p.activePatchesAt q i) (p.operator i) xi⟫_ℝ ≤
        Theta * ‖e.heat.frozenAt q k xi‖ ^ 2) ∧
      (‖e.heat.frozenAt q k xi‖ ^ 2 ≤ Theta * (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k,
        ⟪xi, patchPrincipal (p.activePatchesAt q i) (fun y => e.heat.patchCutoff psi.value i y (e.heat.values q))
          (p.operator i) xi⟫_ℝ)) := by
  classical
  obtain ⟨Theta, tau, hTheta, htau, hc⟩ := regular_patch_cumulative_comparison hX e hzeta
    (by linarith) hCχ hsmall hnear (patchOverlapBound n (1 / 2) 2 3)
  refine ⟨Theta, tau, hTheta, htau, ?_⟩
  intro epsilon hepsilon heps hcoef q hq xi k
  have cover (i) := regular_actual_patch_cover hX e hzeta1 psi i
  have hroom (i y) (hy : y ∈ p.activePatchesAt q i) : dist (p.center i y).val q ≤
      (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) / 12 :=
    p.near i y (Finset.mem_filter.mp hy).1 q ⟨hq, (Finset.mem_filter.mp hy).2⟩
  have hbig (i y) (hy : y ∈ p.activePatchesAt q i) : dist q (p.center i y).val ≤
      enlargement * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) := by
    have hr : 0 < e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15) :=
      div_pos e.heat.radius_pos (by positivity)
    have hh := hroom i y hy
    rw [dist_comm] at hh
    have hm := mul_le_mul_of_nonneg_right henlargement hr.le
    linarith
  have h := hc epsilon hepsilon heps hcoef (p.activePatchesAt q) p.center
    (fun i y => e.heat.patchCutoff psi.value i y (e.heat.values q))
    (fun i => (cover i).active_card q hq) q (e.heat.patch_region_subset hq)
    hroom hbig (fun i y _ => (cover i).cutoff_nonneg y _)
    (fun i => by
      obtain ⟨y, hy, _, hw, ha, _⟩ := (cover i).weight_one_cover q hq
      exact ⟨y, Finset.mem_filter.mpr ⟨hy, ha⟩, hw⟩) xi k
  simpa only [operator, patchMass, patchPrincipal, sum_apply, inner_sum, smul_apply,
    inner_smul_right] using h

/-- At one scale the total positive mass costs only the active overlap,
with the coefficient computed from the original Bochner cutoff bound. -/
theorem mass_small (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1 / 64) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ) {epsilon : ℝ}
    (hcoef : (patchOverlapBound n (1 / 2) 2 3 : ℝ) *
      (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2)) ≤ epsilon)
    {q : X} (hq : q ∈ e.heat.patchRegion) (xi : Euclidean n) :
    ⟪xi, patchMass (p.activePatchesAt q i) (p.operator i) xi⟫_ℝ ≤
      epsilon * ‖e.heat.frozenAt q i xi‖ ^ 2 := by
  classical
  have cover := regular_actual_patch_cover hX e hzeta1 psi i
  have hroom (y) (hy : y ∈ p.activePatchesAt q i) : dist (p.center i y).val q ≤
      32 * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) := by
    have h := p.near i y (Finset.mem_filter.mp hy).1 q ⟨hq, (Finset.mem_filter.mp hy).2⟩
    have hr : 0 < e.heat.radius / 2 ^ (e.heat.shift + i + 15) :=
      div_pos e.heat.radius_pos (by positivity)
    linarith
  have h := regular_patch_mass_sum_frozen_small hX e (e.heat.patch_region_subset hq)
    hzeta (by linarith) hCχ hsmall hnear (p.activePatchesAt q i) (p.center i)
    (cover.active_card q hq) i hroom xi
  have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖e.heat.frozenAt q i xi‖)
  simpa only [operator, patchMass, sum_apply, inner_sum] using h.trans hm

end RegularPatchSelection
end RegularPointCoordinates

end

end OAI
