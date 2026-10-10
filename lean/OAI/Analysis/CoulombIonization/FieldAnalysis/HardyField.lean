import Mathlib
import OAI.Analysis.CoulombIonization.Variational.FatouIntegrable
import OAI.Analysis.CoulombIonization.Variational.HardySquare

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

def hardyDenom (ε : ℝ) (x : Space) : ℝ := ‖x‖ ^ 2 + ε

def hardyField (ε : ℝ) (a : Fin 3) (x : Space) : ℝ := x a / (2 * hardyDenom ε x)

lemma hardyDenom_pos {ε : ℝ} (hε : 0 < ε) (x : Space) : 0 < hardyDenom ε x := by
  dsimp [hardyDenom]
  positivity

lemma hardyDenom_smooth (ε : ℝ) : ContDiff ℝ ∞ (hardyDenom ε) :=
  contDiff_id.norm_sq ℝ |>.add contDiff_const

lemma hardyField_smooth {ε : ℝ} (hε : 0 < ε) (a : Fin 3) :
    ContDiff ℝ ∞ (hardyField ε a) :=
  (EuclideanSpace.proj a).contDiff.div (contDiff_const.mul (hardyDenom_smooth ε))
    (fun x => mul_ne_zero (by norm_num) (hardyDenom_pos hε x).ne')

lemma hardyField_fderiv {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1) =
      1 / (2 * hardyDenom ε x) - (x a) ^ 2 / (hardyDenom ε x) ^ 2 := by
  have ht := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const ε
  have hi := (hasDerivAt_inv (hardyDenom_pos hε x).ne').comp_hasFDerivAt x ht
  have hp := (((EuclideanSpace.proj a).hasFDerivAt (x := x)).mul hi).const_mul (1 / 2 : ℝ)
  have he : hardyField ε a =
      (fun y => (1 / 2 : ℝ) * ((EuclideanSpace.proj a : Space → ℝ) *
        ((fun y : ℝ => y⁻¹) ∘ hardyDenom ε)) y) := by
    funext y
    simp only [hardyField, Pi.mul_apply, Function.comp_apply, EuclideanSpace.proj,
      PiLp.proj_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, hp.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    EuclideanSpace.proj, PiLp.proj_apply]
  dsimp [hardyDenom]
  simp only [Pi.single_eq_same]
  field_simp
  ring

lemma hardyField_norm_bound {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖hardyField ε a x‖ ≤ 1 + ε⁻¹ := by
  have hd := hardyDenom_pos hε x
  have hxd : |x a| ≤ hardyDenom ε x + 1 := by
    have hh := coordinate_sq_le x a
    have hsq := sq_nonneg (|x a| - 1 / 2)
    dsimp [hardyDenom]
    nlinarith [sq_abs (x a)]
  have he : ε ≤ hardyDenom ε x := by dsimp [hardyDenom]; nlinarith [sq_nonneg ‖x‖]
  change |x a / (2 * hardyDenom ε x)| ≤ _
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hd)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hd)).mpr
  have hi : 1 ≤ ε⁻¹ * hardyDenom ε x := by
    calc
      1 = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hε.le)
  nlinarith [inv_pos.mpr hε]

lemma hardyField_derivative_bound {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1)‖ ≤ 2 / ε := by
  rw [hardyField_fderiv hε]
  have hd := hardyDenom_pos hε x
  have he : ε ≤ hardyDenom ε x := by dsimp [hardyDenom]; nlinarith [sq_nonneg ‖x‖]
  have hx : (x a) ^ 2 ≤ hardyDenom ε x := by
    have hh := coordinate_sq_le x a
    dsimp [hardyDenom]
    linarith
  have hq : 0 ≤ (x a) ^ 2 / (hardyDenom ε x) ^ 2 := by positivity
  have hq' : (x a) ^ 2 / (hardyDenom ε x) ^ 2 ≤ 1 / hardyDenom ε x := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    field_simp
    exact hx
  have hi : 1 / hardyDenom ε x ≤ 1 / ε := one_div_le_one_div_of_le hε he
  simp only [div_eq_mul_inv] at hi hq hq' ⊢
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hp : 0 ≤ 1 / (2 * hardyDenom ε x) := by positivity
    simp only [div_eq_mul_inv] at hp
    linarith [inv_pos.mpr hε]
  · have hh : 1 / (2 * hardyDenom ε x) ≤ 1 / hardyDenom ε x := by
      apply one_div_le_one_div_of_le hd
      linarith
    simp only [div_eq_mul_inv] at hh
    linarith [inv_pos.mpr hε]

lemma hardyField_potential {ε : ℝ} (hε : 0 < ε) (x : Space) :
    1 / (4 * hardyDenom ε x) ≤ ∑ a : Fin 3,
      (fderiv ℝ (hardyField ε a) x (EuclideanSpace.single a 1) - (hardyField ε a x) ^ 2) := by
  have hd := hardyDenom_pos hε x
  simp only [hardyField_fderiv hε, hardyField, div_pow, mul_pow, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div,
    sum_coordinate_sq]
  have he : 3 * (1 / (2 * hardyDenom ε x)) - ‖x‖ ^ 2 / hardyDenom ε x ^ 2 -
      ‖x‖ ^ 2 / (4 * hardyDenom ε x ^ 2) =
      1 / (4 * hardyDenom ε x) + 5 * ε / (4 * hardyDenom ε x ^ 2) := by
    field_simp
    dsimp [hardyDenom]
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  exact le_add_of_nonneg_right (by positivity)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma linear_hardyField_fderiv (P : E →L[ℝ] Space) (v : E) {ε : ℝ}
    (hε : 0 < ε) (a : Fin 3) (x : E) :
    fderiv ℝ (fun y => hardyField ε a (P y)) x v =
      fderiv ℝ (hardyField ε a) (P x) (P v) := by
  have hh := ((hardyField_smooth hε a).differentiable (by simp) (P x)).hasFDerivAt.comp x
    (P.hasFDerivAt (x := x))
  change (fderiv ℝ ((hardyField ε a) ∘ P) x) _ = _
  rw [hh.fderiv]
  rfl

lemma linear_regularized_hardy_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1) {ε : ℝ}
    (hε : 0 < ε) {f : E → ℂ} {g : Fin 3 → E → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    (∫ x, (regularizedCoulomb ε (P x)) ^ 2 * ‖f x‖ ^ 2) ≤
      4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hs := weak_square_completion_potential_bound hf hg v hweak
    (b := fun a x => hardyField (ε ^ 2) a (P x))
    (fun a => (hardyField_smooth hε2 a).comp P.contDiff)
    (B := fun _ => 1 + (ε ^ 2)⁻¹) (D := fun _ => 2 / ε ^ 2)
    (fun a x => hardyField_norm_bound hε2 a (P x))
    (fun a x => by
      change ‖fderiv ℝ (fun y => hardyField (ε ^ 2) a (P y)) x (v a)‖ ≤ _
      rw [linear_hardyField_fderiv P _ hε2, hPv]
      exact hardyField_derivative_bound hε2 a (P x))
    (V := fun x => (regularizedCoulomb ε (P x)) ^ 2 / 4)
    (((regularizedCoulomb_continuous hε).comp P.continuous).pow 2 |>.div_const 4)
    (fun x => by positivity) (BV := (ε⁻¹) ^ 2 / 4)
    (fun x => by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (regularizedCoulomb ε (P x)) ^ 2 / 4)]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (regularizedCoulomb_nonneg ε (P x))
          (regularizedCoulomb_le hε (P x)) 2) (by norm_num))
    (fun x => by
      simp only [linear_hardyField_fderiv P _ hε2, hPv]
      apply le_trans _ (hardyField_potential hε2 (P x))
      have hd := hardyDenom_pos hε2 (P x)
      rw [regularizedCoulomb, regularizedRadius_sq, div_pow]
      change (‖P x‖ ^ 2 / (hardyDenom (ε ^ 2) (P x)) ^ 2) / 4 ≤
        1 / (4 * hardyDenom (ε ^ 2) (P x))
      apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
      apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
      field_simp
      dsimp [hardyDenom]
      nlinarith)
  have he : (fun x => (regularizedCoulomb ε (P x)) ^ 2 / 4 * ‖f x‖ ^ 2) =
      (fun x => (1 / 4 : ℝ) * ((regularizedCoulomb ε (P x)) ^ 2 * ‖f x‖ ^ 2)) := by
    funext x; ring
  rw [he, integral_const_mul] at hs
  linarith

lemma linear_hardy_integrable_bound (P : E →L[ℝ] Space) (v : Fin 3 → E)
    (hPv : ∀ a, P (v a) = EuclideanSpace.single a 1)
    {f : E → ℂ} {g : Fin 3 → E → ℂ} (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (v a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖P x‖ ^ 2) ∧
    (∫ x, ‖f x‖ ^ 2 / ‖P x‖ ^ 2) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n x => (regularizedCoulomb (ε n) (P x)) ^ 2 * ‖f x‖ ^ 2
  have hi (n : ℕ) : Integrable (u n) := by
    apply hf.norm.integrable_sq.bdd_mul (c := ((ε n)⁻¹) ^ 2)
      (((regularizedCoulomb_continuous (hε n)).comp P.continuous).pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖(regularizedCoulomb (ε n) (P x)) ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (regularizedCoulomb_nonneg (ε n) (P x))
        (regularizedCoulomb_le (hε n) (P x)) 2
  have hu0 (n : ℕ) : ∀ᵐ x, 0 ≤ u n x :=
    Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hf0 : ∀ᵐ x, 0 ≤ ‖f x‖ ^ 2 / ‖P x‖ ^ 2 :=
    Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have ht : ∀ᵐ x, Tendsto (fun n => u n x) atTop (𝓝 (‖f x‖ ^ 2 / ‖P x‖ ^ 2)) := by
    exact Eventually.of_forall fun x => by
      have hh := ((regularizedCoulomb_tendsto htε (P x)).pow 2).mul_const (‖f x‖ ^ 2)
      have heq : (1 / ‖P x‖) ^ 2 * ‖f x‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ ^ 2 := by ring
      simpa only [heq] using hh
  have hb (n : ℕ) : (∫ x, u n x) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 :=
    linear_regularized_hardy_bound P v hPv (hε n) hf hg hweak
  have hfin := integrable_of_nonneg_ae_limit hi
    ((hf.aestronglyMeasurable.norm.pow 2).div₀ (P.continuous.norm.pow 2).aestronglyMeasurable)
    hu0 hf0 ht hb
  exact ⟨hfin, integral_le_of_nonneg_ae_limit hi hfin hu0 hf0 ht
    (by positivity) hb⟩

end CoulombAtom

end

end OAI
