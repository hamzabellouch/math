import Mathlib
import OAI.Analysis.CoulombIonization.Variational.WeightedVariance
import OAI.Analysis.CoulombIonization.Variational.FatouIntegrable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section LinearCoulomb
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma linear_radialField_fderiv (P : E →L[ℝ] Space) (v : E) {ε : ℝ}
    (hε : 0 < ε) (a : Fin 3) (x : E) :
    fderiv ℝ (fun y => radialField ε a (P y)) x v =
      fderiv ℝ (radialField ε a) (P x) (P v) := by
  have hh := ((radialField_smooth hε a).differentiable (by simp) (P x)).hasFDerivAt.comp x
    (P.hasFDerivAt (x := x))
  change (fderiv ℝ ((radialField ε a) ∘ P) x) _ = _
  rw [hh.fderiv]
  rfl

lemma linear_regularized_coulomb_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {Z ε : ℝ}
    (hZ : 0 ≤ Z) (hε : 0 < ε) {f : E → ℂ} {g : Fin 3 → E → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, 2 * Z * regularizedCoulomb ε (P x) * ‖f x‖ ^ 2) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  let b : Fin 3 → E → ℝ := fun a x => Z * radialField ε a (P x)
  have hb (a : Fin 3) : ContDiff ℝ ∞ (b a) :=
    contDiff_const.mul ((radialField_smooth hε a).comp P.contDiff)
  have hdb (a : Fin 3) (x : E) : fderiv ℝ (b a) x (v a) =
        Z * fderiv ℝ (radialField ε a) (P x) (EuclideanSpace.single a 1) := by
    have hh := ((radialField_smooth hε a).comp P.contDiff).differentiable (by simp) x
    change DifferentiableAt ℝ (fun y : E => radialField ε a (P y)) x at hh
    change (fderiv ℝ (fun y : E => Z * radialField ε a (P y)) x) _ = _
    rw [(hh.hasFDerivAt.const_mul Z).fderiv]
    simp only [smul_apply, smul_eq_mul, linear_radialField_fderiv P _ hε, hPv]
  refine weak_square_completion_bound hf hg v hweak hb
    (B := fun _ => Z) (D := fun _ => Z * ε⁻¹) (BV := 2 * Z * ε⁻¹) (C := Z ^ 2)
    (V := fun x => 2 * Z * regularizedCoulomb ε (P x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a x
    change ‖Z * radialField ε a (P x)‖ ≤ Z
    rw [norm_mul, Real.norm_of_nonneg hZ]
    exact (mul_le_mul_of_nonneg_left (radialField_norm_le hε a (P x)) hZ).trans_eq
      (mul_one Z)
  · intro a x
    rw [hdb, Real.norm_of_nonneg
      (mul_nonneg hZ (radialField_derivative_bounds hε a (P x)).1)]
    exact mul_le_mul_of_nonneg_left (radialField_derivative_bounds hε a (P x)).2 hZ
  · exact continuous_const.mul ((regularizedCoulomb_continuous hε).comp P.continuous)
  · intro x
    exact mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (P x))
  · intro x
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (regularizedCoulomb_nonneg ε (P x)))]
    exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le hε (P x)) (by positivity)
  · positivity
  · intro x
    simp only [b, mul_pow, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_radialField_sq_le hε (P x))
      (sq_nonneg Z)).trans_eq (mul_one _)
  · intro x
    simp only [hdb, ← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (radialField_divergence hε (P x)) hZ
    simpa only [regularizedCoulomb, mul_div_assoc, mul_left_comm Z 2, mul_assoc] using hh

lemma linear_coulomb_integrable (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖P x‖) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n x => regularizedCoulomb (ε n) (P x) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := (ε n)⁻¹)
      ((regularizedCoulomb_continuous (hε n)).comp P.continuous).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖regularizedCoulomb (ε n) (P x)‖ ≤ _
      rw [Real.norm_of_nonneg (regularizedCoulomb_nonneg (ε n) (P x))]
      exact regularizedCoulomb_le (hε n) (P x)
  refine integrable_of_nonneg_ae_limit hi
    ((hf.aestronglyMeasurable.norm.pow 2).div₀ P.continuous.norm.aestronglyMeasurable)
    (fun n => Eventually.of_forall fun x => mul_nonneg
      (regularizedCoulomb_nonneg (ε n) (P x)) (sq_nonneg _))
    (Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)) ?_
    (C := (∑ a, ∫ x, ‖g a x‖ ^ 2) + (∫ x, ‖f x‖ ^ 2)) ?_
  · exact Eventually.of_forall fun x => by
      have hh := (regularizedCoulomb_tendsto htε (P x)).mul_const (‖f x‖ ^ 2)
      have heq : (1 / ‖P x‖) * ‖f x‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ := by ring
      simpa only [heq] using hh
  · intro n
    have hb := linear_regularized_coulomb_bound P v hPv (le_refl (0 : ℝ) |>.trans zero_le_one)
      (hε n) hf hg hweak
    have hu0 : 0 ≤ ∫ x, u n x := integral_nonneg fun x => mul_nonneg
      (regularizedCoulomb_nonneg (ε n) (P x)) (sq_nonneg _)
    simp only [mul_one, one_pow, one_mul, mul_assoc, integral_const_mul] at hb
    change 2 * (∫ x, u n x) ≤ _ at hb
    linarith

lemma linear_coulomb_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {Z : ℝ} (hZ : 0 ≤ Z)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    2 * Z * (∫ x, ‖f x‖ ^ 2 / ‖P x‖) ≤
      (∑ a, ∫ x, ‖g a x‖ ^ 2) + Z ^ 2 * (∫ x, ‖f x‖ ^ 2) := by
  have hnu := linear_coulomb_integrable P v hPv hf hg hweak
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ :=
    fun n x => 2 * Z * regularizedCoulomb (ε n) (P x) * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := 2 * Z * (ε n)⁻¹)
      (continuous_const.mul ((regularizedCoulomb_continuous (hε n)).comp
        P.continuous)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖2 * Z * regularizedCoulomb (ε n) (P x)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (regularizedCoulomb_nonneg (ε n) (P x)))]
      exact mul_le_mul_of_nonneg_left (regularizedCoulomb_le (hε n) (P x)) (by positivity)
  rw [← integral_const_mul]
  apply integral_le_of_nonneg_ae_limit hi (hnu.const_mul (2 * Z))
  · intro n
    exact Eventually.of_forall fun x => mul_nonneg
      (mul_nonneg (by positivity) (regularizedCoulomb_nonneg (ε n) (P x))) (sq_nonneg _)
  · exact Eventually.of_forall fun x => mul_nonneg (by positivity) (by positivity)
  · exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (P x)).const_mul (2 * Z)
        ).mul_const (‖f x‖ ^ 2)
      have heq : 2 * Z * (1 / ‖P x‖) * ‖f x‖ ^ 2 =
          2 * Z * (‖f x‖ ^ 2 / ‖P x‖) := by ring
      simpa only [heq] using hh
  · exact add_nonneg (Finset.sum_nonneg fun a _ => integral_nonneg fun x => sq_nonneg _)
      (mul_nonneg (sq_nonneg Z) (integral_nonneg fun x => sq_nonneg _))
  · intro n
    exact linear_regularized_coulomb_bound P v hPv hZ (hε n) hf hg hweak

lemma linear_coulomb_infinitesimal_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {δ : ℝ} (hδ : 0 < δ)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, ‖f x‖ ^ 2 / ‖P x‖) ≤
      δ * (∑ a, ∫ x, ‖g a x‖ ^ 2) + (1 / (4 * δ)) * (∫ x, ‖f x‖ ^ 2) := by
  have hh := mul_le_mul_of_nonneg_left
    (linear_coulomb_bound P v hPv (Z := 1 / (2 * δ)) (by positivity) hf hg hweak)
    hδ.le
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have he1 : δ * (2 * (1 / (2 * δ)) * (∫ x, ‖f x‖ ^ 2 / ‖P x‖)) =
      (∫ x, ‖f x‖ ^ 2 / ‖P x‖) := by field_simp [hδ0]
  have he2 : δ * ((∑ a, ∫ x, ‖g a x‖ ^ 2) + (1 / (2 * δ)) ^ 2 *
      (∫ x, ‖f x‖ ^ 2)) = δ * (∑ a, ∫ x, ‖g a x‖ ^ 2) +
        (1 / (4 * δ)) * (∫ x, ‖f x‖ ^ 2) := by field_simp [hδ0]; ring
  rwa [he1, he2] at hh

end LinearCoulomb

lemma nuclear_integrable {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖) := by
  let P : Configuration N →L[ℝ] Space := ContinuousLinearMap.proj i
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i = _
    simp [direction]
  exact linear_coulomb_integrable (E := Configuration N) P (direction i) hp hf hg hweak

lemma pair_integrable {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i - x j‖) := by
  let P : Configuration N →L[ℝ] Space :=
    (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space) -
      (ContinuousLinearMap.proj j : Configuration N →L[ℝ] Space)
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i - direction i a j = _
    simp [direction, hij.symm]
  exact linear_coulomb_integrable (E := Configuration N) P (direction i) hp hf hg hweak

end CoulombAtom

end

end OAI
