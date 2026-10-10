import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Sum
import OAI.Analysis.CoulombIonization.Variational.ComplexRealWeightPairing

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma bindingWeight_continuous {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    Continuous (bindingWeight R ε) := by
  have he : bindingWeight R ε = fun x => bindingRoot R ε x ^ 2 := by
    funext x; exact (bindingRoot_sq hR hε x).symm
  rw [he]
  exact (bindingRoot_smooth hR hε).continuous.pow 2

lemma bindingWeight_integrable {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => bindingWeight R ε (x i) * f x) := by
  apply weighted_integrable hf ((bindingWeight_continuous hR hε).comp (continuous_apply i))
  intro x
  change ‖bindingWeight R ε (x i)‖ ≤ R
  rw [Real.norm_of_nonneg (bindingWeight_pos hR hε (x i)).le]
  exact bindingWeight_le hR hε (x i)

lemma bindingTotal_integral {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    (∫ x, (bindingTotalMultiplier hR hε).value x * f x) =
      ∑ i, ∫ x, bindingWeight R ε (x i) * f x := by
  simp only [bindingTotalMultiplier_value hR hε, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => bindingWeight_integrable hR hε i hf)

lemma bindingKinetic_lower {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i : Fin N) :
    (∑ j, ∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2) -
      (∑ a, ∫ x, bindingWeight R ε (x i) * ‖F.val (some (i,a)) x‖ ^ 2) ≤
    ∑ j, ∑ a, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re := by
  classical
  let A (j : Fin N) := ∑ a, ∫ x,
    bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2
  let B (j : Fin N) := ∑ a, (⟪((bindingMultiplier hR hε i).apply
    ((bindingMultiplier hR hε i).apply F)).val (some (j,a)), F.val (some (j,a))⟫_ℂ).re
  have hoff (j : Fin N) (hji : j ≠ i) : B j = A j := by
    apply Finset.sum_congr rfl; intro a _
    exact binding_pairing_off hR hε F i j hji.symm a
  have he : (∑ j, if j ≠ i then B j else 0) = ∑ j, if j ≠ i then A j else 0 := by
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hji
    · exact hoff j hji
    · rfl
  have ha := sum_excluding_add i A
  have hb := sum_excluding_add i B
  have hp : 0 ≤ B i := bindingMultiplier_kinetic_nonneg hR hε i F
  change (∑ j, A j) - A i ≤ ∑ j, B j
  rw [he] at hb
  linarith


open MeasureTheory Filter
open scoped Topology BigOperators

def bindingApprox (n : ℕ) (x : Space) : ℝ :=
  bindingWeight ((n:ℝ)+1) (((n:ℝ)+1)⁻¹) x

lemma bindingApprox_pos (n : ℕ) (x : Space) : 0 < bindingApprox n x :=
  bindingWeight_pos (by positivity) (by positivity) x

lemma regularizedRadius_le_add {ε : ℝ} (hε : 0 ≤ ε) (x : Space) :
    regularizedRadius ε x ≤ ‖x‖ + ε := by
  unfold regularizedRadius
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg x]

lemma bindingApprox_le (n : ℕ) (x : Space) : bindingApprox n x ≤ ‖x‖ + 1 := by
  have he : ((n:ℝ)+1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  exact (bindingWeight_le_radius (by positivity) (by positivity) x).trans
    ((regularizedRadius_le_add (by positivity) x).trans (by linarith))

lemma bindingWeight_div_form {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (x : Space) :
    bindingWeight R ε x = regularizedRadius ε x / (1 + regularizedRadius ε x * R⁻¹) := by
  have ht := regularizedRadius_pos hε x
  unfold bindingWeight
  field_simp

lemma bindingApprox_tendsto (x : Space) : Tendsto (fun n => bindingApprox n x) atTop (𝓝 ‖x‖) := by
  have hR : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => by linarith) tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp hR
  have ht : Tendsto (fun n : ℕ => regularizedRadius (((n:ℝ)+1)⁻¹) x) atTop (𝓝 ‖x‖) := by
    have hh := ((tendsto_const_nhds (x := ‖x‖ ^ 2)).add (he.pow 2)).sqrt
    simpa only [regularizedRadius, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)] using hh
  have hd := ht.div (tendsto_const_nhds.add (ht.mul he)) (by norm_num : (1:ℝ)+‖x‖*0 ≠ 0)
  have hh : Tendsto (fun n : ℕ => regularizedRadius (((n:ℝ)+1)⁻¹) x /
      (1+regularizedRadius (((n:ℝ)+1)⁻¹) x * ((n:ℝ)+1)⁻¹)) atTop (𝓝 ‖x‖) := by
    convert hd using 1
    simp only [mul_zero, add_zero, div_one]
  apply hh.congr'
  exact Eventually.of_forall fun n => (bindingWeight_div_form
    (by positivity : 0 < (n:ℝ)+1) (by positivity) x).symm

lemma configuration_nuclear_ne {N : ℕ} (i : Fin N) :
    ∀ᵐ x : Configuration N, x i ≠ 0 :=
  Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i 0

lemma configuration_pair_ne {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x : Configuration N, x i ≠ x j := by
  classical
  let L : Configuration N →ₗ[ℝ] Space := LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) j
  have hL : L ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Space)
    intro hh
    have he := congrArg (fun M : Configuration N →ₗ[ℝ] Space => M (Function.update (fun _ => 0) i v)) hh
    simp only [L, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.zero_apply,
      Function.update_self, Function.update_of_ne hij.symm, sub_zero] at he
    exact hv he
  have hk : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hh := Measure.addHaar_submodule volume (LinearMap.ker L) hk
  have hm : volume {x : Configuration N | x i = x j} = 0 := by
    convert hh using 2
    ext x
    change (x i = x j) ↔ L x = 0
    simp only [L, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero]
  exact ae_iff.mpr (by simpa only [not_not] using hm)


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma bindingApprox_continuous (n : ℕ) : Continuous (bindingApprox n) :=
  bindingWeight_continuous (by positivity) (by positivity)

lemma bindingApprox_integrable {N : ℕ} (n : ℕ) (i : Fin N)
    {f : Configuration N → ℝ} (hf : Integrable f) :
    Integrable (fun x => bindingApprox n (x i) * f x) :=
  bindingWeight_integrable (by positivity) (by positivity) i hf

lemma bindingApprox_nuclear_tendsto {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hi : Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖)) :
    Tendsto (fun n => ∫ x, bindingApprox n (x i) * (‖f x‖ ^ 2 / ‖x i‖)) atTop
      (𝓝 (∫ x, ‖f x‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖f x‖ ^ 2 + ‖f x‖ ^ 2 / ‖x i‖)
  · intro n
    exact (bindingApprox_integrable n i hi).aestronglyMeasurable
  · exact hf.norm.integrable_sq.add hi
  · intro n
    filter_upwards [configuration_nuclear_ne i] with x hx
    have hr : 0 < ‖x i‖ := norm_pos_iff.mpr hx
    rw [Real.norm_of_nonneg (mul_nonneg (bindingApprox_pos n (x i)).le (by positivity))]
    calc
      _ ≤ (‖x i‖ + 1) * (‖f x‖ ^ 2 / ‖x i‖) :=
        mul_le_mul_of_nonneg_right (bindingApprox_le n (x i)) (by positivity)
      _ = _ := by field_simp
  · filter_upwards [configuration_nuclear_ne i] with x hx
    have ht := (bindingApprox_tendsto (x i)).mul
      (tendsto_const_nhds (x := ‖f x‖ ^ 2 / ‖x i‖))
    convert ht using 1
    rw [mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

def bindingPairApprox {N : ℕ} (n : ℕ) (i j : Fin N) (x : Configuration N) : ℝ :=
  min 1 ((bindingApprox n (x i) + bindingApprox n (x j)) / ‖x i-x j‖)

lemma bindingPairApprox_nonneg {N : ℕ} (n : ℕ) (i j : Fin N) (x : Configuration N) :
    0 ≤ bindingPairApprox n i j x := by
  apply le_min (by norm_num)
  exact div_nonneg (add_nonneg (bindingApprox_pos n (x i)).le
    (bindingApprox_pos n (x j)).le) (norm_nonneg _)

lemma bindingPairApprox_le {N : ℕ} (n : ℕ) (i j : Fin N) (x : Configuration N) :
    bindingPairApprox n i j x ≤ 1 := min_le_left _ _

lemma bindingPairApprox_measurable {N : ℕ} (n : ℕ) (i j : Fin N) :
    Measurable (bindingPairApprox n i j) := by
  exact measurable_const.min
    ((((bindingApprox_continuous n).comp (continuous_apply i)).measurable.add
      (((bindingApprox_continuous n).comp (continuous_apply j)).measurable)).div
        (((continuous_apply i).sub (continuous_apply j)).norm.measurable))

lemma bindingPairApprox_tendsto {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    ∀ᵐ x : Configuration N, Tendsto (fun n => bindingPairApprox n i j x)
      atTop (𝓝 (1:ℝ)) := by
  filter_upwards [configuration_pair_ne i j hij] with x hx
  have hr : 0 < ‖x i-x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have ht := (tendsto_const_nhds (x := (1:ℝ))).min
    (((bindingApprox_tendsto (x i)).add (bindingApprox_tendsto (x j))).div_const ‖x i-x j‖)
  have hh : (1:ℝ) ≤ (‖x i‖ + ‖x j‖) / ‖x i-x j‖ := by
    rw [le_div_iff₀ hr, one_mul]
    exact norm_sub_le _ _
  simpa only [bindingPairApprox, min_eq_left hh] using ht

lemma bindingPairApprox_integrable {N : ℕ} (n : ℕ) (i j : Fin N)
    {f : Configuration N → ℂ} (hf : MemLp f 2) :
    Integrable (fun x => bindingPairApprox n i j x * ‖f x‖ ^ 2) := by
  apply hf.norm.integrable_sq.bdd_mul (c := 1)
    (bindingPairApprox_measurable n i j).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (bindingPairApprox_nonneg n i j x)]
    exact bindingPairApprox_le n i j x

lemma bindingPairApprox_integral_tendsto {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {f : Configuration N → ℂ} (hf : MemLp f 2) :
    Tendsto (fun n => ∫ x, bindingPairApprox n i j x * ‖f x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖f x‖ ^ 2)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ ^ 2)
  · intro n
    exact (bindingPairApprox_integrable n i j hf).aestronglyMeasurable
  · exact hf.norm.integrable_sq
  · intro n
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (bindingPairApprox_nonneg n i j x) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (bindingPairApprox_le n i j x)
  · filter_upwards [bindingPairApprox_tendsto i j hij] with x hx
    simpa only [one_mul] using hx.mul (tendsto_const_nhds (x := ‖f x‖ ^ 2))


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
