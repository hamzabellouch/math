import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.Restriction

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
section

lemma complex_real_weight_pairing (w : ℝ) (a : ℂ) :
    (⟪(w : ℂ) * a, a⟫_ℂ).re = w * ‖a‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, Complex.conj_re, Complex.conj_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma l2_real_weight_pairing {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w : X → ℝ) (f g : Lp ℂ 2 μ)
    (hg : (g : X → ℂ) =ᵐ[μ] fun x => (w x : ℂ) * f x) :
    (⟪g, f⟫_ℂ).re = ∫ x, w x * ‖f x‖ ^ 2 ∂μ := by
  rw [l2_inner_re]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx, complex_real_weight_pairing]

lemma norm_div_sqrt_real_sq (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖a / (Real.sqrt r : ℂ)‖ ^ 2 = ‖a‖ ^ 2 / r := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr]

attribute [local irreducible] graphNuclear graphPair graphComponent FermionMultiplier.apply

lemma FermionMultiplier.nuclear_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) :
    (⟪graphNuclear s i (p.apply F), graphNuclear s i F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_nuclear F s i)]
  apply integral_congr_ae
  filter_upwards [graphNuclear_ae s i F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

lemma FermionMultiplier.pair_weighted_pairing {N : ℕ} (p : FermionMultiplier N)
    (F : fermionGraph N) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    (⟪graphPair s i j hij (p.apply F), graphPair s i j hij F⟫_ℂ).re =
      ∫ x, p.value x * (‖graphComponent s none F x‖ ^ 2 / ‖x i-x j‖) := by
  rw [l2_real_weight_pairing p.value _ _ (p.apply_pair F s i j hij)]
  apply integral_congr_ae
  filter_upwards [graphPair_ae s i j hij F] with x hx
  rw [hx, norm_div_sqrt_real_sq _ (norm_nonneg _)]

lemma binding_pairing_off {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (F : weakGraph (sectorDirections N)) (i j : Fin N) (hij : i ≠ j) (a : Fin 3) :
    (⟪((bindingMultiplier hR hε i).apply ((bindingMultiplier hR hε i).apply F)).val
      (some (j,a)), F.val (some (j,a))⟫_ℂ).re =
      ∫ x, bindingWeight R ε (x i) * ‖F.val (some (j,a)) x‖ ^ 2 := by
  apply l2_real_weight_pairing
  have hd (x : Configuration N) : lineDeriv ℝ (bindingMultiplier hR hε i).value x
      (sectorDirections N (j,a)) = 0 := by
    simp only [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      ite_eq_right (Ne.symm hij)]
  filter_upwards [(bindingMultiplier hR hε i).apply_gradient
    ((bindingMultiplier hR hε i).apply F) (j,a),
    (bindingMultiplier hR hε i).apply_gradient F (j,a)] with x hx hy
  rw [hd, Complex.ofReal_zero, zero_mul, add_zero] at hx hy
  rw [hx, hy]
  change (bindingRoot R ε (x i) : ℂ) * ((bindingRoot R ε (x i) : ℂ) * _) = _
  rw [← mul_assoc, ← pow_two, ← Complex.ofReal_pow, bindingRoot_sq hR hε]

end

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

lemma weighted_integrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {w : X → ℝ} (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun x => w x * f x) μ :=
  hf.bdd_mul hw.aestronglyMeasurable (Eventually.of_forall hC)

lemma integral_weighted_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w f g : X → ℝ) (hf : Integrable (fun x => w x * f x) μ)
    (hg : Integrable (fun x => w x * g x) μ) :
    (∫ x, w x * (f x + g x) ∂μ) = (∫ x, w x * f x ∂μ) + ∫ x, w x * g x ∂μ := by
  simp only [mul_add]
  exact integral_add hf hg

lemma integral_weighted_sub {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w f g : X → ℝ) (hf : Integrable (fun x => w x * f x) μ)
    (hg : Integrable (fun x => w x * g x) μ) :
    (∫ x, w x * (f x - g x) ∂μ) = (∫ x, w x * f x ∂μ) - ∫ x, w x * g x ∂μ := by
  simp only [mul_sub]
  exact integral_sub hf hg

lemma integral_weighted_sum {X α : Type*} [MeasurableSpace X] [Fintype α]
    {μ : Measure X} (w : X → ℝ) (f : α → X → ℝ)
    (hf : ∀ i, Integrable (fun x => w x * f i x) μ) :
    (∫ x, w x * ∑ i, f i x ∂μ) = ∑ i, ∫ x, w x * f i x ∂μ := by
  simp only [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => hf i)

lemma integral_weighted_const_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (w f : X → ℝ) (c : ℝ) :
    (∫ x, w x * (c * f x) ∂μ) = c * ∫ x, w x * f x ∂μ := by
  simp only [mul_left_comm (w _) c]
  exact integral_const_mul c _

lemma integral_weighted_quantumDensity {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (Z : ℝ) (s : Spins N)
    (w : Configuration N → ℝ) (hw : Continuous w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      (1/2:ℝ) * (∑ i, ∑ a, ∫ x, w x * ‖ψ.gradient s i a x‖ ^ 2) -
      Z * (∑ i, ∫ x, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
      (1/2:ℝ) * (∑ i, ∑ j, ∫ x, w x *
        (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
  classical
  have hk (i : Fin N) (a : Fin 3) := weighted_integrable (hψ.2.1 s i a).norm.integrable_sq hw hC
  have hn (i : Fin N) := weighted_integrable
    (nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
  have hp (i j : Fin N) : Integrable (fun x => w x *
      (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    split_ifs with hij
    · exact weighted_integrable (pair_integrable i j hij (hψ.1 s)
        (hψ.2.1 s i) (hψ.2.2.1 s i)) hw hC
    · simp only [mul_zero]; exact integrable_zero _ _ _
  have hks := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun a _ => hk i a))
  have hns := integrable_finsetSum Finset.univ (fun i _ => hn i)
  have hps := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hp i j))
  have hleft : (∫ x, w x * quantumEnergyDensity Z ψ s x) =
      ∫ x, (1/2:ℝ) * (∑ i, ∑ a, w x * ‖ψ.gradient s i a x‖ ^ 2) -
        Z * (∑ i, w x * (‖ψ.value s x‖ ^ 2 / ‖x i‖)) +
        (1/2:ℝ) * (∑ i, ∑ j, w x *
          (if i ≠ j then ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [quantumEnergyDensity, mul_add, mul_sub, mul_left_comm (w x) (1/2:ℝ),
        mul_left_comm (w x) Z, Finset.mul_sum]
  have ha := integral_add ((hks.const_mul (1/2:ℝ)).sub (hns.const_mul Z))
    (hps.const_mul (1/2:ℝ))
  have hb := integral_sub (hks.const_mul (1/2:ℝ)) (hns.const_mul Z)
  simp only [Pi.sub_apply] at ha hb
  rw [hleft, ha, hb]
  simp only [integral_const_mul]
  simp_rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hk i a)),
    integral_finsetSum _ (fun a _ => hk _ a), integral_finsetSum _ (fun i _ => hn i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hp i j)),
    integral_finsetSum _ (fun j _ => hp _ j)]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

end CoulombAtom

end

end OAI
