import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingScale

namespace OAI

/-!
# Uniform control on a terminal shearing window

A quadratic displacement bounded up to its stopping time changes by at
most a fixed multiple of the relative window length near that time. This
is the quantitative algebra needed to replace a short orbit window by a
single terminal shear in the measure argument.
-/

noncomputable section
open Set Matrix Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma quadratic_sample_coefficient_bounds (B C a : ℝ)
    (hfull : |B + C| ≤ a) (hhalf : |B / 2 + C / 4| ≤ a) :
    |B| ≤ 5 * a ∧ |C| ≤ 6 * a := by
  have h1 := abs_le.mp hfull
  have h2 := abs_le.mp hhalf
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

lemma quadratic_terminal_window_bound (B C a s : ℝ)
    (hfull : |B + C| ≤ a) (hhalf : |B / 2 + C / 4| ≤ a)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    |B * s + C * s ^ 2 - (B + C)| ≤ 17 * a * (1 - s) := by
  obtain ⟨hB, hC⟩ := quadratic_sample_coefficient_bounds B C a hfull hhalf
  have ha : 0 ≤ a := (abs_nonneg (B + C)).trans hfull
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have he : B * s + C * s ^ 2 - (B + C) = (s - 1) * (B + (s + 1) * C) := by ring
  rw [he, abs_mul, abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub]
  calc
    (1 - s) * |B + (s + 1) * C| ≤
        (1 - s) * (|B| + |s + 1| * |C|) := by
      apply mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hs1)
      simpa only [abs_mul] using abs_add_le B ((s + 1) * C)
    _ ≤ (1 - s) * (5 * a + 2 * (6 * a)) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ s + 1)]
      apply mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr hs1)
      apply add_le_add hB
      exact (mul_le_mul_of_nonneg_right (by linarith : s + 1 ≤ 2) (abs_nonneg C)).trans
        (mul_le_mul_of_nonneg_left hC (by norm_num))
    _ = 17 * a * (1 - s) := by ring

/-- Every matrix entry stays close to its terminal value on a short
relative window, uniformly over all stopping times and nearby matrices. -/
theorem root_conjugation_terminal_window {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) {T a : ℝ} (hT : 0 < T)
    (hbound : ∀ t ∈ Icc 0 T, rootShearSize hij g t ≤ a)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (r q : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij (s * T) * g *
        Matrix.SpecialLinearGroup.transvection hij (-(s * T))).val r q -
      (Matrix.SpecialLinearGroup.transvection hij T * g *
        Matrix.SpecialLinearGroup.transvection hij (-T)).val r q| ≤
      17 * a * (1 - s) := by
  let b : ℝ := (if r = i then g.val j q else 0) -
    (if q = j then g.val r i else 0)
  let c : ℝ := if r = i ∧ q = j then -g.val j i else 0
  have hpoly (t : ℝ) :
      (Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).val r q =
        g.val r q + b * t + c * t ^ 2 := by
    rw [root_conjugation_entry]
    dsimp only [b, c]
    split_ifs <;> ring
  have hfull : |b * T + c * T ^ 2| ≤ a := by
    have hh := (entry_sub_le_rootShearSize hij g T r q).trans
      (hbound T ⟨hT.le, le_rfl⟩)
    rw [hpoly] at hh
    convert hh using 1; congr 1; ring
  have hhalf : |(b * T) / 2 + (c * T ^ 2) / 4| ≤ a := by
    have hh := (entry_sub_le_rootShearSize hij g (T / 2) r q).trans
      (hbound (T / 2) ⟨by linarith, by linarith⟩)
    rw [hpoly] at hh
    convert hh using 1; congr 1; ring
  have hh := quadratic_terminal_window_bound (b * T) (c * T ^ 2) a s hfull hhalf hs
  rw [hpoly, hpoly]
  convert hh using 1; congr 1; ring

/-- A relative window shrinking to the terminal time has the same
matrix limit as the terminal shear, even though the stopping times may
diverge. -/
theorem root_conjugation_window_tendsto {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (T s : ℕ → ℝ) (a : ℝ)
    (hT : ∀ m, 0 < T m)
    (hbound : ∀ m, ∀ t ∈ Icc 0 (T m), rootShearSize hij (g m) t ≤ a)
    (hs : ∀ m, s m ∈ Icc (0 : ℝ) 1) (hslim : Tendsto s atTop (𝓝 1))
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-T m)) atTop (𝓝 h)) :
    Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (s m * T m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-(s m * T m))) atTop (𝓝 h) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro q
  have herror : Tendsto (fun m => 17 * a * (1 - s m)) atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 17 * a) atTop (𝓝 (17 * a))).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hslim)
  have hdiff : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (s m * T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-(s m * T m))).val r q -
      (Matrix.SpecialLinearGroup.transvection hij (T m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-T m)).val r q) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ herror
    intro m
    simpa only [Real.norm_eq_abs] using
      root_conjugation_terminal_window hij (g m) (hT m) (hbound m) (s m) (hs m) r q
  have hentry : Continuous (fun A : G n => A.val r q) := by fun_prop
  have hh := hentry.tendsto h |>.comp hlim
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hdiff.add hh

end DukePrimeDegree

end

end OAI
