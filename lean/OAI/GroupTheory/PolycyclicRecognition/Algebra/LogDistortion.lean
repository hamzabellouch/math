import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Tactic

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

/-- A polynomial correction to exponential contraction can be absorbed
uniformly at a time bounded by twice the logarithm of the initial size. -/
theorem exists_logarithmic_contraction_time {C : ℝ} (hC : 0 ≤ C) (b : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ R : ℝ, 0 ≤ R →
      let t := 2 * Real.log (2 + R) + a
      1 ≤ t ∧ C * (1 + t) ^ b * Real.exp (-t) * R ≤ 1 := by
  have hp : Tendsto (fun t : ℝ => t ^ b * Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b : ℝ) (1 / 2) (by norm_num)
  have hs : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [eventually_ge_atTop (z - 1)] with t ht
    linarith
  have heq (t : ℝ) : C * (1 + t) ^ b * Real.exp (-t / 2) =
      (C * Real.exp (1 / 2)) * ((1 + t) ^ b * Real.exp (-(1 / 2) * (1 + t))) := by
    have hh : Real.exp (-t / 2) = Real.exp (1 / 2) * Real.exp (-(1 / 2) * (1 + t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hh]
    ring
  have ht : Tendsto (fun t : ℝ => C * (1 + t) ^ b * Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [heq, Function.comp_def, mul_zero] using
      (hp.comp hs).const_mul (C * Real.exp (1 / 2))
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  let a := max a₀ 1
  refine ⟨a, (by dsimp [a]; positivity), fun R hR => ?_⟩
  let t := 2 * Real.log (2 + R) + a
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have ha1 : 1 ≤ a := le_max_right _ _
  have ha : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have hta : a₀ ≤ t := (le_max_left _ _).trans (by dsimp [t]; linarith)
  have hcoef : C * (1 + t) ^ b * Real.exp (-t / 2) ≤ 1 := (ha₀ t hta).le
  have hsmall : Real.exp (-t / 2) * R ≤ 1 := by
    calc
      Real.exp (-t / 2) * R ≤ Real.exp (-Real.log (2 + R)) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply Real.exp_le_exp.mpr
        dsimp [t]
        linarith
      _ = R / (2 + R) := by rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  refine ⟨ht1, ?_⟩
  have hnonneg : 0 ≤ C * (1 + t) ^ b * Real.exp (-t / 2) := by positivity
  calc
    C * (1 + t) ^ b * Real.exp (-t) * R =
        (C * (1 + t) ^ b * Real.exp (-t / 2)) * (Real.exp (-t / 2) * R) := by
      have hh : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hh]
      ring
    _ ≤ (C * (1 + t) ^ b * Real.exp (-t / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hsmall hnonneg
    _ ≤ 1 := by simpa using hcoef

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

/-- Conjugation costs at most twice the conjugating length. -/
theorem dist_one_conjugate_le (a x : G) :
    dist 1 (a * x * a⁻¹) ≤ 2 * dist 1 a + dist 1 x := by
  have hi : dist 1 a⁻¹ = dist 1 a := by
    simpa only [mul_one, mul_inv_cancel, dist_comm] using (dist_mul_left a 1 a⁻¹).symm
  calc
    dist 1 (a * x * a⁻¹) ≤ dist 1 (a * x) + dist 1 a⁻¹ := dist_one_mul_le _ _
    _ ≤ (dist 1 a + dist 1 x) + dist 1 a⁻¹ := add_le_add (dist_one_mul_le _ _) le_rfl
    _ = _ := by rw [hi]; ring

/-- Exponential contraction up to a polynomial, together with a bounded
unit neighborhood and linear conjugating paths, implies logarithmic distortion. -/
theorem logarithmic_distortion_of_contracting_flow
    {V : Type*} [NormedAddCommGroup V]
    (Exp : V → G) (d : ℝ → G) (T : ℝ → V → V)
    {C L B : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖)
    (hpath : ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t)
    (hlocal : ∀ v, ‖v‖ ≤ 1 → dist 1 (Exp v) ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨a, ha, htime⟩ := exists_logarithmic_contraction_time hC b
  let c := (2 * L * a + B) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨4 * L + c + 1, by positivity, fun v => ?_⟩
  let t := 2 * Real.log (2 + ‖v‖) + a
  obtain ⟨ht1, hsize⟩ := htime ‖v‖ (norm_nonneg v)
  have ht : 0 ≤ t := le_trans zero_le_one ht1
  have hunit : ‖T t v‖ ≤ 1 := (hcontract v t ht).trans hsize
  have hlog : Real.log 2 ≤ Real.log (2 + ‖v‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg v])
  have hconst : 2 * L * a + B ≤ c * Real.log (2 + ‖v‖) := by
    calc
      2 * L * a + B = c * Real.log 2 := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc
  calc
    dist 1 (Exp v) = dist 1 (d t * Exp (T t v) * (d t)⁻¹) := by rw [← hconj v t ht]
    _ ≤ 2 * dist 1 (d t) + dist 1 (Exp (T t v)) := dist_one_conjugate_le _ _
    _ ≤ 2 * (L * t) + B := add_le_add (by gcongr; exact hpath t ht1) (hlocal _ hunit)
    _ = 4 * L * Real.log (2 + ‖v‖) + (2 * L * a + B) := by dsimp [t]; ring
    _ ≤ (4 * L + c + 1) * Real.log (2 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
