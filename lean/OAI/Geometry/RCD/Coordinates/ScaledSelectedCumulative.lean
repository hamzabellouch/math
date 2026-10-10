import OAI.Geometry.RCD.Coordinates.RegularSelectedMass
import OAI.Geometry.RCD.Coordinates.ScaledPatchCumulative

namespace OAI

/-! # Fixed cumulative bounds for the actual selected patches -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem exists_scaled_selected_cumulative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (c : RegularHeatConstants n) :
    ∃ Theta tau : ℝ, 1 ≤ Theta ∧ 0 < tau ∧
    ∀ {a κ B J C A Cχ enlargement zeta eta Cpin budget : ℝ}
      (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta),
    c.Matches e.heat → 0 ≤ zeta → zeta ≤ 1 / 64 → 0 ≤ Cχ → 1 ≤ enlargement →
    (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2 →
    (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4 →
    ∀ (psi : EuclideanGevreyCutoff n) (f : RegularPinchingField e.heat Cpin budget)
      (p : RegularPatchSelection e.heat psi.value f),
    ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ tau →
    (∀ i, 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)) ^ 2) ≤ epsilon) →
    ∀ q, q ∈ e.heat.patchRegion → ∀ (xi : Euclidean n) (k : ℕ),
      (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k, ⟪xi, patchMass (p.activePatchesAt q i) (p.operator i) xi⟫_ℝ ≤
        Theta * ‖e.heat.frozenAt q k xi‖ ^ 2) ∧
      (‖e.heat.frozenAt q k xi‖ ^ 2 ≤ Theta * (‖xi‖ ^ 2 + ∑ i ∈ Finset.range k,
        ⟪xi, patchPrincipal (p.activePatchesAt q i) (fun y => e.heat.patchCutoff psi.value i y (e.heat.values q))
          (p.operator i) xi⟫_ℝ)) := by
  classical
  obtain ⟨Theta, tau, hTheta, htau, hcBuild⟩ := exists_scaled_patch_cumulative_comparison
    hX hk c (patchOverlapBound n (1 / 2) 2 3)
  refine ⟨Theta, tau, hTheta, htau, ?_⟩
  intro a κ B J C A Cχ enlargement zeta eta Cpin budget e hmatch hzeta hzeta1 hCχ
    henlargement hsmall hnear psi f p
  have hc := hcBuild e hmatch hzeta (by linarith only [hzeta1]) hCχ hsmall hnear
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
  simpa only [RegularPatchSelection.operator, patchMass, patchPrincipal, sum_apply, inner_sum, smul_apply,
    inner_smul_right] using h


end RegularPointCoordinates

end

end OAI
