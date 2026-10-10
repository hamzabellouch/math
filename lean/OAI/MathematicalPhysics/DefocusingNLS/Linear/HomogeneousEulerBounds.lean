import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerRecurrence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetBound

namespace OAI

/-! # Leading high-derivative row of the radial spectral equation

The original logarithmic damping is an exponential diagonal plus a bounded
matrix. Repeated falling-Euler differentiation produces its powers as the
leading velocity coefficient. The remaining coefficient is two powers of
radius smaller; this is an operator statement for both channels together.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

private theorem eulerRows_one (B C : ℝ → End) :
    homogeneousEulerRows B C 1 = (fun _ => 0, fun _ => 1) := by
  apply Prod.ext <;> funext t <;> apply ContinuousLinearMap.ext <;> intro w
  all_goals simp [homogeneousEulerRows, sub_apply, smul_apply]

theorem homogeneousEulerRows_bound (B C : ℝ → End)
    (hB : HasLogJetBound 2 B) (hC : HasLogJetBound 2 C) (n : ℕ) :
    HasLogJetBound (2 * (n : ℝ)) (homogeneousEulerRows B C (n + 1)).1 ∧
      HasLogJetBound (2 * (n : ℝ)) (homogeneousEulerRows B C (n + 1)).2 := by
  induction n with
  | zero =>
      rw [show (0 : ℕ) + 1 = 1 by rfl, eulerRows_one]
      exact ⟨by simpa using (HasLogJetBound.zero 0 :
        HasLogJetBound 0 (fun _ : ℝ => (0 : End))),
        by simpa using (HasLogJetBound.const (1 : End))⟩
  | succ n ih =>
      let S := (homogeneousEulerRows B C (n + 1)).1
      let T := (homogeneousEulerRows B C (n + 1)).2
      have hm : 2 * (n : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hSC : HasLogJetBound (2 * ((n + 1 : ℕ) : ℝ)) (fun t => T t * C t) := by
        convert ih.2.mul hC using 1
        push_cast
        ring
      have hTB : HasLogJetBound (2 * ((n + 1 : ℕ) : ℝ)) (fun t => T t * B t) := by
        convert ih.2.mul hB using 1
        push_cast
        ring
      have hS : HasLogJetBound (2 * (n : ℝ)) S := ih.1
      have hT : HasLogJetBound (2 * (n : ℝ)) T := ih.2
      have hs := ((hS.deriv.sub (hS.smul (n + 1))).mono hm).sub hSC
      have ht := (((hS.add hT.deriv).sub (hT.smul (n + 1))).mono hm).sub hTB
      change HasLogJetBound (2 * ((n + 1 : ℕ) : ℝ))
          (fun t => deriv S t - ((n + 1 : ℕ) : ℝ) • S t - T t * C t) ∧
        HasLogJetBound (2 * ((n + 1 : ℕ) : ℝ))
          (fun t => S t + deriv T t - ((n + 1 : ℕ) : ℝ) • T t - T t * B t)
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using hs
      · simpa only [Nat.cast_add, Nat.cast_one] using ht

noncomputable def homogeneousEulerLeading (D : End) (n : ℕ) (t : ℝ) : End :=
  Real.exp (2 * (n : ℝ) * t) • (-D) ^ n

theorem homogeneousEulerLeading_step (D : End) (n : ℕ) (t : ℝ) :
    -(homogeneousEulerLeading D n t * (Real.exp (2 * t) • D)) =
      homogeneousEulerLeading D (n + 1) t := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [homogeneousEulerLeading, neg_apply, smul_apply, mul_apply_eq_comp,
    ContinuousLinearMap.map_smul_of_tower, smul_smul, pow_succ, map_neg]
  rw [← Real.exp_add]
  have he : 2 * (n : ℝ) * t + 2 * t = 2 * ((n + 1 : ℕ) : ℝ) * t := by
    push_cast
    ring
  rw [he]
  simp only [smul_neg]

theorem homogeneousEulerRows_leading (B C : ℝ → End) (D : End) (B₀ : ℝ → End)
    (hB₀ : HasLogJetBound 0 B₀) (hC : HasLogJetBound 2 C)
    (hB : ∀ t, B t = B₀ t + Real.exp (2 * t) • D) (n : ℕ) :
    HasLogJetBound (2 * ((n : ℝ) - 1))
      (fun t => (homogeneousEulerRows B C (n + 1)).2 t - homogeneousEulerLeading D n t) := by
  have hBbound : HasLogJetBound 2 B := by
    have hb := (hB₀.mono (by norm_num : (0 : ℝ) ≤ 2)).add
      (HasLogJetBound.exponential 2 D)
    simpa only [show (fun t => B₀ t + Real.exp (2 * t) • D) = B from funext (fun t => (hB t).symm)] using hb
  induction n with
  | zero =>
      rw [show (0 : ℕ) + 1 = 1 by rfl, eulerRows_one]
      simpa [homogeneousEulerLeading] using
        (HasLogJetBound.zero (-2) : HasLogJetBound (-2) (fun _ : ℝ => (0 : End)))
  | succ n ih =>
      let S := (homogeneousEulerRows B C (n + 1)).1
      let T := (homogeneousEulerRows B C (n + 1)).2
      obtain ⟨hS, hT⟩ := homogeneousEulerRows_bound B C hBbound hC n
      have hrem : HasLogJetBound (2 * (n : ℝ))
          (fun t => (T t - homogeneousEulerLeading D n t) * (Real.exp (2 * t) • D)) := by
        convert ih.mul (HasLogJetBound.exponential 2 D) using 1
        ring
      have hlow : HasLogJetBound (2 * (n : ℝ))
          (fun t => S t + deriv T t - (n + 1 : ℝ) • T t - T t * B₀ t) := by
        have hm : HasLogJetBound (2 * (n : ℝ)) (fun t => T t * B₀ t) := by
          simpa only [add_zero] using hT.mul hB₀
        exact ((hS.add hT.deriv).sub (hT.smul (n + 1))).sub hm
      have heq : (fun t => (homogeneousEulerRows B C (n + 1 + 1)).2 t -
          homogeneousEulerLeading D (n + 1) t) =
          (fun t => (S t + deriv T t - (n + 1 : ℝ) • T t - T t * B₀ t) -
            (T t - homogeneousEulerLeading D n t) * (Real.exp (2 * t) • D)) := by
        funext t
        change S t + deriv T t - ((n + 1 : ℕ) : ℝ) • T t - T t * B t -
          homogeneousEulerLeading D (n + 1) t = _
        rw [hB t, ← homogeneousEulerLeading_step D n t]
        push_cast
        rw [mul_add, sub_mul]
        abel
      rw [heq]
      convert hlow.sub hrem using 1
      push_cast
      ring

/-- The actual leading diagonal has a positive lower stretch. The operator
error is uniformly smaller, simultaneously for all vectors in both channels. -/
theorem homogeneousEulerRows_norm_lower (B C : ℝ → End) (D : End) (B₀ : ℝ → End)
    (hB₀ : HasLogJetBound 0 B₀) (hC : HasLogJetBound 2 C)
    (hB : ∀ t, B t = B₀ t + Real.exp (2 * t) • D)
    (c : ℝ) (hc : 0 < c) (hD : ∀ w : V, ‖D w‖ = c * ‖w‖) (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ w : V,
      (c ^ n / 2) * Real.exp (2 * (n : ℝ) * t) * ‖w‖ ≤
        ‖(homogeneousEulerRows B C (n + 1)).2 t w‖ := by
  have hp (k : ℕ) (w : V) : ‖((-D) ^ k) w‖ = c ^ k * ‖w‖ := by
    induction k generalizing w with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, ih]
        simp only [neg_apply, norm_neg, hD, pow_succ]
        ring
  have hlead (t : ℝ) (w : V) :
      ‖homogeneousEulerLeading D n t w‖ = c ^ n * Real.exp (2 * (n : ℝ) * t) * ‖w‖ := by
    simp only [homogeneousEulerLeading, smul_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hp]
    ring
  obtain ⟨E, hE, hb⟩ := (homogeneousEulerRows_leading B C D B₀ hB₀ hC hB n).bound 0
  have hsmall : ∀ᶠ t : ℝ in atTop, E * Real.exp (-2 * t) ≤ c ^ n / 2 := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)).const_mul E
    have hpos : E * 0 < c ^ n / 2 := by
      rw [mul_zero]
      exact div_pos (pow_pos hc _) (by norm_num)
    have hh' := hh.eventually (gt_mem_nhds hpos)
    simpa only [Function.comp_def, id_eq, neg_mul] using hh'.mono (fun _ h => h.le)
  filter_upwards [hb, hsmall] with t ht hs
  intro w
  simp only [iteratedDeriv_zero] at ht
  let T := (homogeneousEulerRows B C (n + 1)).2 t
  let A := homogeneousEulerLeading D n t
  have herr : ‖(T - A) w‖ ≤ (c ^ n / 2) * Real.exp (2 * (n : ℝ) * t) * ‖w‖ := by
    have he := (ContinuousLinearMap.le_opNorm (T - A) w).trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg w))
    apply he.trans
    have heq : Real.exp (2 * ((n : ℝ) - 1) * t) =
        Real.exp (-2 * t) * Real.exp (2 * (n : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right hs
      (mul_nonneg (Real.exp_pos (2 * (n : ℝ) * t)).le (norm_nonneg w))
    convert hh using 1 <;> ring
  have htri : ‖A w‖ ≤ ‖T w‖ + ‖(T - A) w‖ := by
    calc
      ‖A w‖ = ‖T w - (T - A) w‖ := by simp only [sub_apply, sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  change ‖homogeneousEulerLeading D n t w‖ ≤ _ at htri
  rw [hlead] at htri
  change _ ≤ ‖T w‖
  linarith

end DefocusingNLS

end OAI
