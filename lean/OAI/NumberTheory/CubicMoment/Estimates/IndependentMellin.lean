import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightTail
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-! Exact Mellin separation of independent coordinate weights on a finite
arithmetic sum. The joint weight has explicitly factored L1 mass. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma zeroLineMellin_point (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {N X : ℝ} (hN : 0 < N) (hX : 0 < X) :
    W (N/X) = ∫ τ : ℝ, zeroLineMellinWeight W X τ*mellinPhase (-τ) N := by
  have h : W (N/X) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W ((τ:ℂ)*Complex.I)*(X:ℂ)^((τ:ℂ)*Complex.I)*
        (N:ℂ)^(-((τ:ℂ)*Complex.I)) := by
    simpa using smooth_mellin_finite (fun _ : Unit => (1:ℂ)) (fun _ : Unit => N)
      (fun _ => hN) W hW hpos hsm 0 hX
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with τ
  rw [mellinPhase_eq_cpow hN]
  have he : ((-τ:ℝ):ℂ)*Complex.I = -((τ:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

lemma integrable_zeroLineMellin_phase (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {X : ℝ} (hX : 0 < X) (N : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight W X τ*mellinPhase (-τ) N) := by
  have hw := zeroLineMellinWeight_integrable W hW hpos hsm hX
  have hp : Continuous (fun τ : ℝ => mellinPhase (-τ) N) := by
    unfold mellinPhase
    fun_prop
  apply hw.norm.mono' (hw.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards with τ
  change ‖zeroLineMellinWeight W X τ*mellinPhase (-τ) N‖ ≤ ‖zeroLineMellinWeight W X τ‖
  rw [norm_mul,mellinPhase_norm,mul_one]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def independentMellinWeight (W : ι → ℝ → ℂ) (X : ι → ℝ) (τ : ι → ℝ) : ℂ :=
  ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)

lemma independentMellinWeight_integrable (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    Integrable (independentMellinWeight W X) :=
  Integrable.fintype_prod (fun i => zeroLineMellinWeight_integrable (W i) (hW i) (hpos i) (hsm i) (hX i))

lemma independentMellinWeight_mass (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i) :
    (∫ τ : ι → ℝ, ‖independentMellinWeight W X τ‖) = ∏ i, zeroLineMellinMass (W i) := by
  simp only [independentMellinWeight,norm_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (t : ℝ) => ‖zeroLineMellinWeight (W i) (X i) t‖)]
  simp_rw [zeroLineMellinWeight_mass _ (hX _)]

/-- All original factor weights are separated simultaneously. No cutoff or
Mellin-tail assumption is used in this identity. -/
theorem independent_mellin_finite (a : κ → ℂ) (N : ι → κ → ℝ)
    (hN : ∀ i n, 0 < N i n) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) :
    (∑ n, a n*∏ i, W i (N i n/X i)) =
      ∫ τ : ι → ℝ, independentMellinWeight W X τ *
        ∑ n, a n*∏ i, mellinPhase (-(τ i)) (N i n) := by
  have hi (n : κ) : Integrable (fun τ : ι → ℝ =>
      a n*∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n)) :=
    (Integrable.fintype_prod (fun i =>
      integrable_zeroLineMellin_phase (W i) (hW i) (hpos i) (hsm i) (hX i) (N i n))).const_mul (a n)
  calc
    _ = ∑ n, a n*∫ τ : ι → ℝ,
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_fintype_prod_volume_eq_prod (fun (i : ι) (τ : ℝ) =>
        zeroLineMellinWeight (W i) (X i) τ*mellinPhase (-τ) (N i n))]
      simp_rw [← zeroLineMellin_point (W _) (hW _) (hpos _) (hsm _) (hN _ n) (hX _)]
    _ = ∫ τ : ι → ℝ, ∑ n, a n*
        ∏ i, zeroLineMellinWeight (W i) (X i) (τ i)*mellinPhase (-(τ i)) (N i n) := by
      simp_rw [← integral_const_mul]
      exact (integral_finsetSum _ (fun n _ => hi n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with τ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.prod_mul_distrib]
      unfold independentMellinWeight
      ring

end CubicFirstMoment

end

end OAI
