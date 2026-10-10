import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Basis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

lemma memLp_slice_ae (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => ψ (x,y)) 2 ν := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).aestronglyMeasurable).mp (Lp.memLp ψ)
  filter_upwards [(Lp.memLp ψ).aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with x hx hy
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hy

def contractFunction (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) (x : A) : ℂ :=
  ∫ y, star (b y) * ψ (x,y) ∂ν

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma contractFunction_slice (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) (x : A)
    (hx : MemLp (fun y => ψ (x,y)) 2 ν) :
    contractFunction b ψ x = inner ℂ b (hx.toLp (fun y => ψ (x,y))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx.coeFn_toLp] with y hy
  simp only [hy, inner]
  ring

lemma contractFunction_sq_le (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ‖contractFunction b ψ x‖^2 ≤ ‖b‖^2*(∫ y, ‖ψ (x,y)‖^2 ∂ν) := by
  filter_upwards [memLp_slice_ae ψ] with x hx
  rw [contractFunction_slice b ψ x hx]
  have hc := norm_inner_le_norm (𝕜 := ℂ) b (hx.toLp (fun y => ψ (x,y)))
  have hn : ‖hx.toLp (fun y => ψ (x,y))‖^2 = ∫ y, ‖ψ (x,y)‖^2 ∂ν := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hx.coeFn_toLp] with y hy
    rw [hy]
  have hc2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
  simpa only [mul_pow, hn] using hc2

lemma contractFunction_memLp (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    MemLp (contractFunction b ψ) 2 μ := by
  have hm : AEStronglyMeasurable (contractFunction b ψ) μ :=
    ((Lp.memLp b).aestronglyMeasurable.comp_snd.star.mul
      (Lp.memLp ψ).aestronglyMeasurable).integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp ψ).aestronglyMeasurable).mp (Lp.memLp ψ)
  refine (hi.integral_prod_left.const_mul (‖b‖^2)).mono' (hm.norm.pow 2) ?_
  filter_upwards [contractFunction_sq_le b ψ] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖contractFunction b ψ x‖))] using hx

def contractL2 (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 μ :=
  (contractFunction_memLp b ψ).toLp _

lemma contractL2_ae (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    contractL2 b ψ =ᵐ[μ] contractFunction b ψ := MemLp.coeFn_toLp _

lemma tensorRight_adjoint_eq_contract (b : Lp ℂ 2 ν) (ψ : Lp ℂ 2 (μ.prod ν)) :
    (tensorRight b).adjoint ψ = contractL2 b ψ := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, tensorRight_apply, L2.inner_def, L2.inner_def]
  have hprod : Integrable (fun z : A × B => inner ℂ (u z.1 * b z.2) (ψ z)) (μ.prod ν) := by
    apply (L2.integrable_inner (tensor u b) ψ).congr
    filter_upwards [tensor_ae u b] with z hz
    rw [hz]
  calc
    _ = ∫ z : A × B, star (u z.1) * (star (b z.2) * ψ z) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [tensor_ae u b] with z hz
      simp only [hz, inner, star_mul]
      ring
    _ = ∫ x, ∫ y, star (u x) * (star (b y) * ψ (x,y)) ∂ν ∂μ := by
      apply integral_prod
      convert hprod using 1
      ext z
      simp only [inner, star_mul]
      ring
    _ = ∫ x, inner ℂ (u x) (contractL2 b ψ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [contractL2_ae b ψ] with x hx
      rw [integral_const_mul]
      simp only [hx, contractFunction, inner]
      ring

lemma tensorRight_slice_parseval {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, (∑' j, ENNReal.ofReal (‖((tensorRight (b j)).adjoint ψ) x‖^2)) =
      ∫⁻ y, ENNReal.ofReal (‖ψ (x,y)‖^2) ∂ν := by
  have hj (j : ι) : (fun x => ((tensorRight (b j)).adjoint ψ) x) =ᵐ[μ]
      contractFunction (b j) ψ := by
    rw [tensorRight_adjoint_eq_contract]
    exact contractL2_ae (b j) ψ
  filter_upwards [memLp_slice_ae ψ, ae_all_iff.mpr hj] with x hx hjs
  let u := hx.toLp (fun y => ψ (x,y))
  have hs := basis_parseval b u
  have hn : ‖u‖^2 = ∫ y, ‖ψ (x,y)‖^2 ∂ν := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hx.coeFn_toLp] with y hy
    rw [hy]
  calc
    _ = ∑' j, ENNReal.ofReal (‖inner ℂ (b j) u‖^2) := by
      apply tsum_congr
      intro j
      rw [hjs j, contractFunction_slice (b j) ψ x hx]
    _ = ENNReal.ofReal (‖u‖^2) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]
    _ = _ := by
      rw [hn]
      apply ofReal_integral_eq_lintegral_ofReal
      · exact (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
end CoulombPauli

end

end OAI
