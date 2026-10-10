import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTorus
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-!
# The linear Schrödinger group on the Fourier Sobolev model

Multiplication of each frequency by `exp(-i t |n|²)` defines a strongly
continuous unitary group. The same coefficient model is used for every
Sobolev index, so these isometries act on the paper's weighted Fourier spaces.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- The exact free Schrödinger phase for a Fourier frequency. -/
noncomputable def schrodingerMultiplier (t : ℝ) (n : frequencyLattice) : ℂ :=
  Complex.exp (-Complex.I * ((t * ‖n‖ ^ 2 : ℝ) : ℂ))

@[simp] theorem schrodingerMultiplier_norm (t : ℝ) (n : frequencyLattice) :
    ‖schrodingerMultiplier t n‖ = 1 := by
  simp only [schrodingerMultiplier, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]

@[simp] theorem schrodingerMultiplier_zero (n : frequencyLattice) :
    schrodingerMultiplier 0 n = 1 := by
  simp [schrodingerMultiplier]

theorem schrodingerMultiplier_add (t s : ℝ) (n : frequencyLattice) :
    schrodingerMultiplier (t + s) n =
      schrodingerMultiplier t n * schrodingerMultiplier s n := by
  unfold schrodingerMultiplier
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_schrodingerMultiplier (n : frequencyLattice) :
    Continuous (fun t : ℝ => schrodingerMultiplier t n) := by
  unfold schrodingerMultiplier
  fun_prop

/-- Free evolution preserves the norm of every weighted Fourier vector. -/
noncomputable def schrodingerFlow (t : ℝ) : FourierL2 →ₗᵢ[ℂ] FourierL2 where
  toFun f := ⟨fun n => schrodingerMultiplier t n * f n,
    (lp.memℓp f).mono' (by intro n; simp)⟩
  map_add' f g := by
    ext n
    change schrodingerMultiplier t n * (f n + g n) =
      schrodingerMultiplier t n * f n + schrodingerMultiplier t n * g n
    exact mul_add _ _ _
  map_smul' c f := by ext n; simp [mul_left_comm]
  norm_map' f := by
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simp
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simp

@[simp] theorem schrodingerFlow_apply (t : ℝ) (f : FourierL2) (n : frequencyLattice) :
    schrodingerFlow t f n = schrodingerMultiplier t n * f n := rfl

@[simp] theorem schrodingerFlow_zero (f : FourierL2) : schrodingerFlow 0 f = f := by
  ext n
  simp

theorem schrodingerFlow_add (t s : ℝ) (f : FourierL2) :
    schrodingerFlow (t + s) f = schrodingerFlow t (schrodingerFlow s f) := by
  ext n
  simp [schrodingerMultiplier_add, mul_assoc]

/-- Free evolution is a complex-linear isometric equivalence, with inverse time `-t`. -/
noncomputable def schrodingerUnitary (t : ℝ) : FourierL2 ≃ₗᵢ[ℂ] FourierL2 :=
  LinearIsometryEquiv.ofSurjective (schrodingerFlow t) (by
    intro f
    refine ⟨schrodingerFlow (-t) f, ?_⟩
    rw [← schrodingerFlow_add]
    simp)

@[simp] theorem schrodingerUnitary_apply (t : ℝ) (f : FourierL2) :
    schrodingerUnitary t f = schrodingerFlow t f := rfl

/-- The free evolution is strongly continuous in every Fourier Sobolev norm. -/
theorem continuous_schrodingerFlow (f : FourierL2) :
    Continuous (fun t : ℝ => schrodingerFlow t f) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hs : Summable (fun n : frequencyLattice => 4 * ‖f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mul_left 4
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (f := fun t n => ‖schrodingerFlow t f n - schrodingerFlow t₀ f n‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (𝓕 := 𝓝 t₀)
    (by
      intro n
      have hc : Continuous (fun t : ℝ =>
          ‖schrodingerFlow t f n - schrodingerFlow t₀ f n‖ ^ 2) := by
        change Continuous (fun t : ℝ =>
          ‖schrodingerMultiplier t n * f n - schrodingerMultiplier t₀ n * f n‖ ^ 2)
        exact ((((continuous_schrodingerMultiplier n).fun_mul continuous_const).fun_sub
          continuous_const).norm.fun_pow 2)
      simpa using (hc.continuousAt (x := t₀)).tendsto)
    (Filter.Eventually.of_forall (by
      intro t n
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn : ‖schrodingerFlow t f n - schrodingerFlow t₀ f n‖ ≤ 2 * ‖f n‖ := by
        calc
          _ ≤ ‖schrodingerFlow t f n‖ + ‖schrodingerFlow t₀ f n‖ := norm_sub_le _ _
          _ = 2 * ‖f n‖ := by simp; ring
      nlinarith [norm_nonneg (schrodingerFlow t f n - schrodingerFlow t₀ f n),
        norm_nonneg (f n)]))
  have hsq : Tendsto (fun t => ‖schrodingerFlow t f - schrodingerFlow t₀ f‖ ^ 2)
      (𝓝 t₀) (𝓝 0) := by
    have heq (t : ℝ) := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (schrodingerFlow t f - schrodingerFlow t₀ f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] at heq
    simpa only [heq, tsum_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn' : Tendsto (fun t => ‖schrodingerFlow t f - schrodingerFlow t₀ f‖)
      (𝓝 t₀) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

end DefocusingNLS

end OAI
