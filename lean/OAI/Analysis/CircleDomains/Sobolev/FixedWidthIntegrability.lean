import OAI.Analysis.CircleDomains.Sobolev.WedgeIntegrability
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-!
# Spatial integrability at every fixed staircase width

The derivative of a smooth staircase is periodic and bounded. Thus each
fixed choice of shifts has integrable spatial wedges whenever the original
three wedge terms are integrable. In particular, the cost identity needs
no separate integrability assumption for the modified coordinates.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem periodic_deriv_shiftedStaircase {h δ : ℝ} (hh : 0 < h) (θ : ℝ) :
    Function.Periodic (deriv (shiftedStaircase h δ θ)) h := by
  intro x
  have heq : (fun t => shiftedStaircase h δ θ (t + h)) =
      (fun t => shiftedStaircase h δ θ t + h) :=
    funext (shiftedStaircase_add_period hh δ θ)
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  simpa only [deriv_comp_add_const, deriv_add_const] using hd

theorem bounded_staircase_multiplier {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ x : ℝ), χ ∈ Icc 0 1 →
      0 ≤ (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x ∧
      (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x ≤ C := by
  have hc := (contDiff_shiftedStaircase hh hδ hδh θ).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := ((periodic_deriv_shiftedStaircase hh θ).compact_of_continuous
    hh.ne' hc).exists_bound_of_continuousOn continuous_id.continuousOn
  let C : ℝ := 1 + max B 0
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro χ x hχ
  have hd0 := deriv_shiftedStaircase_nonneg hh hδ θ x
  have hdB : deriv (shiftedStaircase h δ θ) x ≤ max B 0 :=
    (le_abs_self _).trans ((hB _ (mem_range_self x)).trans (le_max_left B 0))
  refine ⟨add_nonneg (sub_nonneg.mpr hχ.2) (mul_nonneg hχ.1 hd0), ?_⟩
  have hmul : χ * deriv (shiftedStaircase h δ θ) x ≤ max B 0 := by
    calc
      _ ≤ χ * max B 0 := mul_le_mul_of_nonneg_left hdB hχ.1
      _ ≤ 1 * max B 0 := mul_le_mul_of_nonneg_right hχ.2 (le_max_right _ _)
      _ = _ := one_mul _
  dsimp [C]
  linarith [hχ.1]

theorem integrable_staircase_pair_at_shifts
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (huv : Integrable (fun z => |planarWedge (u z) (v z)|) μ)
    (huc : Integrable (fun z => |planarWedge (u z) (c z)|) μ)
    (hcv : Integrable (fun z => |planarWedge (c z) (v z)|) μ)
    (θ φ : ℝ) :
    Integrable (fun z => |planarWedge
      (staircaseCovector h δ (χ z) θ (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) φ (y z) (v z) (c z))|) μ := by
  obtain ⟨A, hA0, hA⟩ := bounded_staircase_multiplier hh hδ hδh θ
  obtain ⟨B, hB0, hB⟩ := bounded_staircase_multiplier hh hδ hδh φ
  have hmajor := ((huv.const_mul (A * B)).add (huc.const_mul (h * A))).add
    (hcv.const_mul (h * B))
  have hmu := measurable_staircaseCovector hh hδ hδh hχ measurable_const hx hu hc
    (θ := fun _ => θ)
  have hmv := measurable_staircaseCovector hh hδ hδh hχ measurable_const hy hv hc
    (θ := fun _ => φ)
  apply hmajor.mono' (((hmu.fst.mul hmv.snd).sub (hmu.snd.mul hmv.fst)).abs.aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_abs]
  have hAz := hA (χ z) (x z) ⟨hχ0 z, hχ1 z⟩
  have hBz := hB (χ z) (y z) ⟨hχ0 z, hχ1 z⟩
  have he := abs_planarWedge_cutoff_le (u z) (v z) (c z) hAz.1 hBz.1
    (abs_shiftedStaircase_sub_le hh δ θ (x z))
    (abs_shiftedStaircase_sub_le hh δ φ (y z))
  apply he.trans
  dsimp only [Pi.add_apply]
  gcongr <;> first | exact hAz.1 | exact hAz.2 | exact hBz.1 | exact hBz.2

theorem integrable_staircase_pair_at_shifts_of_memLp
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u v c : X → ℝ × ℝ) (x y χ : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (hc : Measurable c)
    (hx : Measurable x) (hy : Measurable y) (hχ : Measurable χ)
    (hu2 : MemLp u 2 μ) (hv2 : MemLp v 2 μ) (hc2 : MemLp c 2 μ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ φ : ℝ) :
    Integrable (fun z => |planarWedge
      (staircaseCovector h δ (χ z) θ (x z) (u z) (c z))
      (staircaseCovector h δ (χ z) φ (y z) (v z) (c z))|) μ :=
  integrable_staircase_pair_at_shifts u v c x y χ hu hv hc hx hy hχ hh hδ hδh hχ0 hχ1
    (integrable_abs_planarWedge_of_memLp hu2 hv2)
    (integrable_abs_planarWedge_of_memLp hu2 hc2)
    (integrable_abs_planarWedge_of_memLp hc2 hv2) θ φ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
