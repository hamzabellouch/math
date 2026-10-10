import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.WeightedIntegralSquare

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.ShellND
open MeasureTheory Filter

theorem integrable_coeff_norm_power {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c F : α → ℂ) (hic : Integrable c μ) (hF : Measurable F)
    {C : ℝ} (hb : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    Integrable (fun x => ‖c x‖ * ‖F x‖^n) μ := by
  apply (hic.norm.mul_const (C^n)).mono'
    (hic.aestronglyMeasurable.norm.mul (hF.aestronglyMeasurable.norm.pow n))
  filter_upwards with x
  change ‖‖c x‖ * ‖F x‖^n‖ ≤ ‖c x‖ * C^n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb x) n) (norm_nonneg _)

theorem continuous_coefficient_shell_square {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : α → ℂ) (hc : Measurable c) (hic : Integrable c ν)
    (F : α × ℝ → ℂ) (hF : Measurable F)
    {C B : ℝ} (hb : ∀ p, ‖F p‖ ≤ C)
    (hB : ∀ ξ, (∫ r, ‖F (ξ,r)‖^2 ∂μ) ≤ B) :
    (∫ r, ‖∫ ξ, c ξ * F (ξ,r) ∂ν‖^2 ∂μ) ≤ (∫ ξ, ‖c ξ‖ ∂ν)^2 * B := by
  let W := ∫ ξ, ‖c ξ‖ ∂ν
  have hW : 0 ≤ W := integral_nonneg (fun _ => norm_nonneg _)
  have hiJoint : Integrable (fun p : α × ℝ => ‖c p.1‖ * ‖F p‖^2)
      (ν.prod μ) := by
    apply ((hic.norm.comp_fst μ).mul_const (C^2)).mono'
      ((hic.aestronglyMeasurable.norm.comp_fst).mul (hF.aestronglyMeasurable.norm.pow 2))
    filter_upwards with p
    change ‖‖c p.1‖ * ‖F p‖^2‖ ≤ ‖c p.1‖ * C^2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb p) 2) (norm_nonneg _)
  have hPoint (r : ℝ) : ‖∫ ξ, c ξ * F (ξ,r) ∂ν‖^2 ≤
      W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2 ∂ν) := by
    have hmF : Measurable (fun ξ => F (ξ,r)) := hF.comp (measurable_id.prodMk measurable_const)
    have hi₁ := integrable_coeff_norm_power ν c (fun ξ => F (ξ,r)) hic hmF (fun ξ => hb (ξ,r)) 1
    have hi₂ := integrable_coeff_norm_power ν c (fun ξ => F (ξ,r)) hic hmF (fun ξ => hb (ξ,r)) 2
    exact norm_integral_coeff_square ν c (fun ξ => F (ξ,r)) hic
      (by simpa only [pow_one] using hi₁) hi₂
  have hm : Measurable (fun r => ∫ ξ, c ξ * F (ξ,r) ∂ν) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  have hiBound : Integrable (fun r => W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2 ∂ν)) μ :=
    hiJoint.integral_prod_right.const_mul W
  have hiMix : Integrable (fun r => ‖∫ ξ, c ξ * F (ξ,r) ∂ν‖^2) μ :=
    hiBound.mono' (hm.norm.pow_const 2).aestronglyMeasurable (by
      filter_upwards with r
      change ‖‖∫ ξ, c ξ * F (ξ,r) ∂ν‖^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖∫ ξ, c ξ * F (ξ,r) ∂ν‖))]
      exact hPoint r)
  calc
    _ ≤ ∫ r, W * (∫ ξ, ‖c ξ‖ * ‖F (ξ,r)‖^2 ∂ν) ∂μ :=
      integral_mono hiMix hiBound hPoint
    _ = W * (∫ ξ, ‖c ξ‖ * (∫ r, ‖F (ξ,r)‖^2 ∂μ) ∂ν) := by
      rw [integral_const_mul, ← integral_integral_swap
        (f := fun ξ r => ‖c ξ‖ * ‖F (ξ,r)‖^2) hiJoint]
      simp_rw [integral_const_mul]
    _ ≤ W * (∫ ξ, ‖c ξ‖ * B ∂ν) := by
      apply mul_le_mul_of_nonneg_left _ hW
      apply integral_mono
      · simpa only [integral_const_mul] using hiJoint.integral_prod_left
      · exact hic.norm.mul_const B
      · intro ξ
        exact mul_le_mul_of_nonneg_left (hB ξ) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; dsimp [W]; ring

end Attempt4PrefixShell.ShellND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.ShellND
open MeasureTheory Filter

theorem finite_weighted_shell_square {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖∑ i ∈ s, F i r‖^2 ∂μ) ≤ (∑ i ∈ s, w i)^2*B := by
  classical
  have hz (i : ι) (his : i ∈ s) (hwi : w i = 0) :
      ∀ᵐ r ∂μ, F i r = 0 := by
    have he : (∫ r, ‖F i r‖^2 ∂μ) = 0 :=
      le_antisymm (by simpa [hwi] using hB i his)
        (integral_nonneg (fun _ => sq_nonneg _))
    have hh := (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg (‖F i r‖)) (hi i his)).mp he
    filter_upwards [hh] with r hr
    simpa using hr
  have hae : ∀ᵐ r ∂μ, ∀ i ∈ s, w i = 0 → F i r = 0 := by
    exact (eventually_all_finset s).mpr (fun i his =>
      (ae_all_iff).mpr (fun hwi => hz i his hwi))
  let G : ℝ → ℝ := fun r => ∑ i ∈ s, ‖F i r‖^2 / w i
  let W : ℝ := ∑ i ∈ s, w i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hgi : Integrable G μ := integrable_finsetSum s
    (fun i his => (hi i his).div_const (w i))
  have hpoint : ∀ᵐ r ∂μ, ‖∑ i ∈ s, F i r‖^2 ≤ W*G r := by
    filter_upwards [hae] with r hr
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
      (fun i his => div_nonneg (sq_nonneg _) (hw i his))
    intro i his
    by_cases hwi : w i = 0
    · simp [hwi,hr i his hwi]
    · rw [mul_div_cancel₀ _ hwi]
  have hsi : Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
    have hsm : AEStronglyMeasurable (fun r => ∑ i ∈ s, F i r) μ := by
      convert Finset.aestronglyMeasurable_sum s hm using 1
      ext r
      simp
    apply (hgi.const_mul W).mono' (hsm.norm.pow 2)
    filter_upwards [hpoint] with r hr
    change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hr
  have hBi (i : ι) (his : i ∈ s) :
      (∫ r, ‖F i r‖^2 ∂μ) / w i ≤ w i*B := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · apply (div_le_iff₀ (lt_of_le_of_ne (hw i his) (Ne.symm hwi))).mpr
      nlinarith [hB i his]
  calc
    _ ≤ ∫ r, W*G r ∂μ := integral_mono_ae hsi (hgi.const_mul W) hpoint
    _ = W * ∑ i ∈ s, (∫ r, ‖F i r‖^2 ∂μ) / w i := by
      rw [integral_const_mul,integral_finsetSum s (fun i his => (hi i his).div_const (w i))]
      simp only [integral_div]
    _ ≤ W * ∑ i ∈ s, w i*B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hBi) hW
    _ = _ := by rw [← Finset.sum_mul]; dsimp [W]; ring

end Attempt4PrefixShell.ShellND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell.ShellND
open MeasureTheory

theorem list_weighted_shell_square {ι : Type*} (L : List ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ) (w : ι → ℝ) {B : ℝ}
    (hw : ∀ i ∈ L, 0 ≤ w i)
    (hi : ∀ i ∈ L, Integrable (fun r => ‖F i r‖^2) μ)
    (hm : ∀ i ∈ L, AEStronglyMeasurable (F i) μ)
    (hB : ∀ i ∈ L, (∫ r, ‖F i r‖^2 ∂μ) ≤ (w i)^2*B) :
    (∫ r, ‖(L.map (fun i => F i r)).sum‖^2 ∂μ) ≤ (L.map w).sum^2*B := by
  have hh := finite_weighted_shell_square (Finset.univ : Finset (Fin L.length)) μ
    (fun i => F L[i]) (fun i => w L[i])
    (fun i _ => hw _ (List.getElem_mem i.isLt))
    (fun i _ => hi _ (List.getElem_mem i.isLt))
    (fun i _ => hm _ (List.getElem_mem i.isLt))
    (fun i _ => hB _ (List.getElem_mem i.isLt))
  have he (f : ι → ℂ) : (∑ i : Fin L.length, f L[i]) = (L.map f).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L f
  have hw' : (∑ i : Fin L.length, w L[i]) = (L.map w).sum := by
    rw [← List.sum_ofFn]
    congr 1
    exact List.ofFn_getElem_eq_map L w
  simp_rw [show ∀ r, (∑ i : Fin L.length, F L[i] r) =
    (L.map (fun i => F i r)).sum from fun r => he (fun i => F i r),hw'] at hh
  exact hh

end Attempt4PrefixShell.ShellND
end GraphLiteralSupport
end
end

end OAI
