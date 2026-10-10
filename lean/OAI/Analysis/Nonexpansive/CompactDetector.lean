import OAI.Analysis.Nonexpansive.Diametral
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI

/-!
# One functional detecting an entire norm-compact set

The diameter theorem first gives a uniform defect threshold at each fixed
point. A finite net and its equal-weight barycenter then give a single
norming functional which detects every point of a norm-compact set.
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ReflexiveFixedPoints.NormalizedMinimalData

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- At a fixed point of the minimal set, sufficiently small fixed-point
defect forces the distance to be arbitrarily close to the diameter. -/
theorem uniform_diametral (D : NormalizedMinimalData (X := X)) (a : D.K)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y : D.K,
      ‖(D.T y : X) - (y : X)‖ ≤ δ →
      1 - η ≤ ‖(y : X) - (a : X)‖ := by
  classical
  by_contra h
  push Not at h
  have hbad : ∀ n : ℕ, ∃ y : D.K,
      ‖(D.T y : X) - (y : X)‖ ≤ 1 / ((n : ℝ) + 1) ∧
      ‖(y : X) - (a : X)‖ < 1 - η := by
    intro n
    exact h (1 / ((n : ℝ) + 1)) (by positivity)
  choose v hv hshort using hbad
  have hv0 : Tendsto (fun n => ‖(D.T (v n) : X) - (v n : X)‖)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => norm_nonneg _) hv
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : (1 : ℝ) ≤ 1 - η :=
    le_of_tendsto' (D.diametral v hv0 a) (fun n => (hshort n).le)
  linarith

/-- Every sufficiently accurate approximate fixed point has one continuous
linear functional detecting its distance from every point of a prescribed
nonempty norm-compact subset of the minimal set. -/
theorem compact_detector (D : NormalizedMinimalData (X := X))
    {E : Set X} (hE : E.Nonempty) (hEK : E ⊆ D.K) (hEc : IsCompact E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : D.K,
      ‖(D.T y : X) - (y : X)‖ ≤ δ →
      ∃ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧
        ∀ z ∈ E, 1 - ε ≤ f ((y : X) - z) := by
  classical
  obtain ⟨t, htE, hcover⟩ := hEc.elim_nhds_subcover
    (fun x => Metric.ball x (ε / 2))
    (fun x _ => Metric.ball_mem_nhds x (by positivity))
  have ht : t.Nonempty := by
    obtain ⟨z, hz⟩ := hE
    obtain ⟨x, hx, _⟩ := Set.mem_iUnion₂.mp (hcover hz)
    exact ⟨x, hx⟩
  have hm : 0 < (t.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ht
  let a : X := t.centerMass (fun _ : X => (1 : ℝ)) id
  have ha : a ∈ D.K := by
    apply D.convex.centerMass_mem
    · intro x hx
      exact zero_le_one
    · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hm
    · intro x hx
      exact hEK (htE x hx)
  have ha_formula : a = (t.card : ℝ)⁻¹ • (∑ x ∈ t, x) := by
    simp [a, Finset.centerMass]
  obtain ⟨δ, hδ, hδbound⟩ :=
    D.uniform_diametral ⟨a, ha⟩ (η := ε / (2 * (t.card : ℝ))) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hfar := hδbound y hy
  obtain ⟨f, hf, hfa⟩ := exists_dual_vector'' ℝ ((y : X) - a)
  refine ⟨f, hf, ?_⟩
  have hupper (x : X) (hx : x ∈ t) : f ((y : X) - x) ≤ 1 := by
    have hxnorm := D.norm_sub_le_one y ⟨x, hEK (htE x hx)⟩
    have hbound := f.le_of_opNorm_le_of_le hf hxnorm
    exact (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs, one_mul] using hbound)
  have hsum : (∑ x ∈ t, f ((y : X) - x)) =
      (t.card : ℝ) * f ((y : X) - a) := by
    simp only [map_sub, ha_formula, map_smul, map_sum, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  have hsum_lower : (t.card : ℝ) - ε / 2 ≤
      ∑ x ∈ t, f ((y : X) - x) := by
    rw [hsum, hfa]
    calc
      (t.card : ℝ) - ε / 2 =
          (t.card : ℝ) * (1 - ε / (2 * (t.card : ℝ))) := by
        field_simp [hm.ne']
      _ ≤ (t.card : ℝ) * ‖(y : X) - a‖ :=
        mul_le_mul_of_nonneg_left hfar hm.le
  have hdeficit : (∑ x ∈ t, (1 - f ((y : X) - x))) ≤ ε / 2 := by
    rw [Finset.sum_sub_distrib]
    have hcard : (∑ _x ∈ t, (1 : ℝ)) = (t.card : ℝ) := by simp
    rw [hcard]
    linarith only [hsum_lower]
  have hnet (x : X) (hx : x ∈ t) : 1 - ε / 2 ≤ f ((y : X) - x) := by
    have hsingle := Finset.single_le_sum
      (f := fun w : X => 1 - f ((y : X) - w))
      (fun w hw => sub_nonneg.mpr (hupper w hw)) hx
    change 1 - f ((y : X) - x) ≤ ∑ w ∈ t, (1 - f ((y : X) - w)) at hsingle
    linarith only [hsingle, hdeficit]
  intro z hz
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcover hz)
  have hclose : ‖z - x‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hzx
  have hfun_close : f (z - x) < ε / 2 := by
    have hbound := f.le_of_opNorm_le hf (z - x)
    have habs : |f (z - x)| ≤ ‖z - x‖ := by
      simpa only [Real.norm_eq_abs, one_mul] using hbound
    exact lt_of_le_of_lt ((le_abs_self _).trans habs) hclose
  have hidentity : f ((y : X) - z) = f ((y : X) - x) - f (z - x) := by
    simp only [map_sub]
    ring
  have hxlower := hnet x hx
  linarith only [hidentity, hxlower, hfun_close]

end ReflexiveFixedPoints.NormalizedMinimalData

end

end OAI
