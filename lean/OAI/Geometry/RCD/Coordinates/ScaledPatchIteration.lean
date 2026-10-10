import OAI.Geometry.RCD.Coordinates.RegularPatchIteration
import OAI.Geometry.RCD.Coordinates.ScaledSelectedCumulative

namespace OAI

/-! # Actual patch iteration with constants preceding its source budget -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem exists_scaled_patch_iteration {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (c : RegularHeatConstants n) :
    ∃ Theta tau : ℝ, 1 ≤ Theta ∧ 0 < tau ∧
    ∀ {a κ B J C A Cχ enlargement zeta eta Cpin budget : ℝ}
      (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (_hmatch : c.Matches e.heat) (_hzeta : 0 ≤ zeta) (_hzeta1 : zeta ≤ 1 / 64) (_hCχ : 0 ≤ Cχ)
    (_henlargement : 1 ≤ enlargement)
    (_hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (_hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (_hwide : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (psi : EuclideanGevreyCutoff n) (f : RegularPinchingField e.heat Cpin budget)
    (_p : RegularPatchSelection e.heat psi.value f),
    ∀ epsilon : ℝ,
      0 ≤ epsilon → epsilon ≤ tau → budget ≤ epsilon →
      (∀ i, 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2) ≤ epsilon) →
      (∀ i, (patchOverlapBound n (1 / 2) 2 3 : ℝ) *
        (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
          (zeta + |K| * (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) ^ 2)) ≤ epsilon) →
      ∀ (Ω : Set (Euclidean n))
        (inverse : Euclidean n → {q : X // q ∈ ball base (e.heat.radius / 32)}),
        (∀ x ∈ Ω, (inverse x).val ∈ e.heat.patchRegion ∧ e.heat.values (inverse x).val = x) →
      ∃ g : PatchIterationGeometry (ι := X) Ω (distanceSourceRadius e.heat.radius e.heat.shift)
        Theta epsilon (patchOverlapBound n (1 / 2) 2 3) (3 * Cpin)
        ((psi.constant * 536870912) ^ 2 + 4 * (psi.constant * 536870912) ^ 3)
        (psi.constant * 536870912),
        g.frozen = fun i x => e.heat.frozenAt (inverse x).val i := by
  classical
  obtain ⟨Theta, tau, hTheta, htau, hcBuild⟩ := exists_scaled_selected_cumulative hX hk c
  refine ⟨Theta + 1, tau, by linarith only [hTheta], htau, ?_⟩
  intro a κ B J C A Cχ enlargement zeta eta Cpin budget e hmatch hzeta hzeta1 hCχ
    henlargement hsmall hnear hwide psi f p
  have hc := hcBuild e hmatch hzeta hzeta1 hCχ henlargement hsmall hnear psi f p
  intro epsilon hepsilon heps hbudget hcoef hmass Ω inverse hinverse
  have cover (i) := regular_actual_patch_cover hX e hzeta1 psi i
  have hscale (i) := iterationRadius_distanceSourceRadius e.heat.radius e.heat.shift i
  have hactive (i x y) (hx : x ∈ Ω) (hy : x ∈ tsupport (e.heat.patchCutoff psi.value i y)) :
      e.heat.values (inverse x).val ∈ tsupport (e.heat.patchCutoff psi.value i y) := by
    rwa [(hinverse x hx).2]
  have hfinset (i x) (hx : x ∈ Ω) :
      activePatches (e.heat.patchNet i) (e.heat.patchCutoff psi.value i) x =
        p.activePatchesAt (inverse x).val i := by
    simp only [activePatches, RegularPatchSelection.activePatchesAt, (hinverse x hx).2]
  refine ⟨{
    patches := e.heat.patchNet
    cutoff := e.heat.patchCutoff psi.value
    operator := p.operator
    center := fun i y => e.heat.values (p.center i y).val
    frozen := fun i x => e.heat.frozenAt (inverse x).val i
    energy := fun i x => f.energy (inverse x) (e.heat.shift + i)
    frozen_mono := fun i x _ xi => e.heat.frozenAt_mono (inverse x).property i xi
    cutoff_smooth := fun i y _ x _ m => ((cover i).cutoff_smooth y).of_le (by simp) |>.contDiffAt
    active_card := ?_
    energy_nonneg := fun i x _ => (f.floor_pos (e.heat.shift + i)).le.trans (f.energy_floor (inverse x) _)
    energy_budget := fun k x _ => (f.shifted_energy_sum_le (inverse x) e.heat.shift k).trans hbudget
    operator_positive := fun i y _ x _ _ => e.heat.pinchingMassMatrix_isPositive _ _ _
    cutoff_nonneg := fun i y _ x _ _ => (cover i).cutoff_nonneg y x
    cutoff_le_one := fun i y _ x _ _ => (cover i).cutoff_le_one y x
    mass_small := ?_
    center_energy := ?_
    cutoff_first := ?_
    cutoff_second := ?_
    cutoff_jets := ?_
    mass_budget := ?_
    principal_budget := ?_ }, rfl⟩
  · intro i x hx
    rw [hfinset i x hx]
    exact (cover i).active_card (inverse x).val (hinverse x hx).1
  · intro i x hx xi
    rw [hfinset i x hx]
    exact p.mass_small hzeta hzeta1 hCχ hsmall hwide i (hmass i) (hinverse x hx).1 xi
  · intro i y hy x hx ha
    have h := p.energy i y hy (inverse x) ⟨(hinverse x hx).1, hactive i x y hx ha⟩
    simpa only [(hinverse x hx).2, hscale, RegularPatchSelection.operator] using h
  · intro i y hy x hx ha xi
    have h := (regular_cutoff_directional_bounds hX e hzeta hzeta1 hnear psi i
      (hinverse x hx).1 hy (hactive i x y hx ha) xi).1
    simpa only [(hinverse x hx).2, hscale] using h
  · intro i y hy x hx ha xi
    have h := (regular_cutoff_directional_bounds hX e hzeta hzeta1 hnear psi i
      (hinverse x hx).1 hy (hactive i x y hx ha) xi).2
    simpa only [(hinverse x hx).2, hscale] using h
  · intro i y hy x hx ha m
    have h := regular_cutoff_normalized_jet hX e hzeta hzeta1 hnear psi i
      (hinverse x hx).1 hy (hactive i x y hx ha) m
    simpa only [(hinverse x hx).2, hscale] using h
  · intro k x hx xi
    have h := (hc epsilon hepsilon heps hcoef (inverse x).val (hinverse x hx).1 xi k).1
    have hs : ∀ i, activePatches (e.heat.patchNet i) (e.heat.patchCutoff psi.value i) x =
        p.activePatchesAt (inverse x).val i := fun i => hfinset i x hx
    have hh := h.trans (mul_le_mul_of_nonneg_right (show Theta ≤ Theta + 1 by linarith)
      (sq_nonneg ‖e.heat.frozenAt (inverse x).val k xi‖))
    simpa only [hs] using hh
  · intro k x hx xi
    have h := (hc epsilon hepsilon heps hcoef (inverse x).val (hinverse x hx).1 xi k).2
    have hs : ∀ i, activePatches (e.heat.patchNet i) (e.heat.patchCutoff psi.value i) x =
        p.activePatchesAt (inverse x).val i := fun i => hfinset i x hx
    have hp := (sq_nonneg ‖e.heat.frozenAt (inverse x).val k xi‖).trans h
    have hnonneg := nonneg_of_mul_nonneg_right hp (lt_of_lt_of_le zero_lt_one hTheta)
    have hh := h.trans (mul_le_mul_of_nonneg_right (show Theta ≤ Theta + 1 by linarith) hnonneg)
    simpa only [hs, (hinverse x hx).2] using hh

end RegularPointCoordinates

end

end OAI
