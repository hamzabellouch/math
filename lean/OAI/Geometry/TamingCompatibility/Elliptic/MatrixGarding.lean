import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ConstantGeometricEnergy

namespace OAI


noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace TamingCompatibility.MatrixEnergy
open EuclideanEnergy

lemma comparison_pointwise (c : Fin 4 → Pair →L[ℝ] V)
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (A B : S) (x : V) {δ C : ℝ} (ha : ∀ i, ‖a i x - c i‖ ≤ δ) (hb : ‖b x‖ ≤ C) :
    ‖constantSystem c A B x‖^2 ≤ 2 * ‖system a b A B x‖^2 +
      16*δ^2*gradientEnergy A B x + 4*C^2*((A x)^2+(B x)^2) := by
  let E : V := ∑ i, (a i x-c i) (pair (coordinateDeriv i A x) (coordinateDeriv i B x))
  let L : V := b x (pair (A x) (B x))
  have he : constantSystem c A B x = system a b A B x + -(E+L) := by
    simp only [constantSystem,system,E,L,sub_apply,Finset.sum_sub_distrib]
    abel
  have h0 := norm_add_sq_le (system a b A B x) (-(E+L))
  rw [← he,norm_neg] at h0
  have h1 := norm_add_sq_le E L
  have hE := principalError_bound (fun i y => a i y-c i) A B x ha
  have hL := lowerError_bound b A B x hb
  change ‖E‖^2 ≤ _ at hE
  change ‖L‖^2 ≤ _ at hL
  nlinarith

theorem garding (c : Fin 4 → Pair →L[ℝ] V) {K δ C : ℝ} (hK : 0 < K)
    (hsmall : 16*K*δ^2 ≤ 1/2)
    (henergy : ∀ A B : S, (∫ x, gradientEnergy A B x) ≤
      K * (∫ x, ‖constantSystem c A B x‖^2))
    (a : Fin 4 → V → Pair →L[ℝ] V) (b : V → Pair →L[ℝ] V)
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x-c i‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) (A B : S) :
    (∫ x, gradientEnergy A B x) ≤ 4*K * (∫ x, ‖system a b A B x‖^2) +
      8*K*C^2 * (∫ x, (A x)^2+(B x)^2) := by
  have ha' (x : V) (i : Fin 4) : ‖a i x‖ ≤ δ + ∑ j, ‖c j‖ := by
    calc
      ‖a i x‖ ≤ ‖a i x-c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ j, ‖c j‖ := add_le_add (ha x i)
        (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hS := system_integrable a b A B hac hbc ha' hb
  have hG := gradientEnergy_integrable A B
  have hF := (schwartz_sq_integrable A).add (schwartz_sq_integrable B)
  have hcomp := integral_mono (constantSystem_integrable c A B)
    (((hS.const_mul 2).add (hG.const_mul (16*δ^2))).add (hF.const_mul (4*C^2)))
    (fun x => comparison_pointwise c a b A B x (ha x) (hb x))
  dsimp only [Pi.add_apply] at hcomp
  erw [integral_add ((hS.const_mul 2).add (hG.const_mul (16*δ^2))) (hF.const_mul (4*C^2)),
    integral_add (hS.const_mul 2) (hG.const_mul (16*δ^2)),
    integral_const_mul,integral_const_mul,integral_const_mul] at hcomp
  simp only [Pi.add_apply] at hcomp
  have hcompK := mul_le_mul_of_nonneg_left hcomp hK.le
  have hcoerce := henergy A B
  have hG0 : 0 ≤ ∫ x, gradientEnergy A B x := integral_nonneg fun x =>
    Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsmallG := mul_le_mul_of_nonneg_right hsmall hG0
  nlinarith

lemma exists_small_error {K : ℝ} (hK : 0 < K) : ∃ δ : ℝ, 0 < δ ∧ 16*K*δ^2 ≤ 1/2 := by
  refine ⟨(Real.sqrt (32*K))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), ?_⟩
  have hs := Real.sq_sqrt (show 0 ≤ 32*K by positivity)
  rw [inv_pow,hs]
  field_simp
  norm_num

end TamingCompatibility.MatrixEnergy

end

end OAI
