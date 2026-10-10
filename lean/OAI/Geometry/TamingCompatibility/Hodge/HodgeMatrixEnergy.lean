import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitaryFrame
import OAI.Geometry.TamingCompatibility.Elliptic.LocalGarding

namespace OAI

section
section

section
noncomputable section
open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
abbrev W := EuclideanSpace ℝ (Fin 6)
abbrev Field := Fin 6 → S

def value (f : Field) (x : V) : W := WithLp.toLp 2 (fun j => f j x)
def derivative (f : Field) (i : Fin 4) (x : V) : W :=
  value (fun j => coordinateDeriv i (f j)) x
def gradient (f : Field) (x : V) : ℝ := ∑ i : Fin 4, ‖derivative f i x‖^2

lemma value_norm (f : Field) (x : V) : ‖value f x‖^2 = ∑ j, (f j x)^2 :=
  EuclideanSpace.real_norm_sq_eq _
lemma value_continuous (f : Field) : Continuous (value f) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℝ)).comp (continuous_pi (fun j => (f j).continuous))
lemma value_integrable (f : Field) : Integrable (fun x => ‖value f x‖^2) := by
  simp_rw [value_norm]
  exact integrable_finsetSum _ (fun j _ => schwartz_sq_integrable (f j))
lemma gradient_integrable (f : Field) : Integrable (gradient f) :=
  integrable_finsetSum _ (fun i _ => value_integrable (fun j => coordinateDeriv i (f j)))
lemma gradient_nonneg (f : Field) (x : V) : 0 ≤ gradient f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
def system (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) (x : V) : Q := (∑ i, a i x (derivative f i x)) + b x (value f x)
def constantSystem (c : Fin 4 → W →L[ℝ] Q) (f : Field) (x : V) : Q :=
  ∑ i, c i (derivative f i x)

lemma principalError_bound (a : Fin 4 → V → W →L[ℝ] Q)
    (f : Field) (x : V) {δ : ℝ} (ha : ∀ i, ‖a i x‖ ≤ δ) :
    ‖∑ i, a i x (derivative f i x)‖^2 ≤ 4*δ^2*gradient f x := by
  refine (norm_sum_four_sq_le _).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [gradient,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := (a i x).le_opNorm (derivative f i x)
  have hm := mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (derivative f i x))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2
lemma lowerError_bound (b : V → W →L[ℝ] Q) (f : Field) (x : V) {C : ℝ}
    (hb : ‖b x‖ ≤ C) : ‖b x (value f x)‖^2 ≤ C^2*‖value f x‖^2 := by
  have h := (b x).le_opNorm (value f x)
  have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (value f x))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h.trans hm) 2

lemma system_integrable (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) {δ C : ℝ} (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) :
    Integrable (fun x => ‖system a b f x‖^2) := by
  have hcont : Continuous (system a b f) := by
    apply Continuous.add _ (hbc.clm_apply (value_continuous f))
    apply continuous_finsetSum
    intro i _
    exact (hac i).clm_apply (value_continuous (fun j => coordinateDeriv i (f j)))
  have hdom := ((gradient_integrable f).const_mul (8*δ^2)).add
    ((value_integrable f).const_mul (2*C^2))
  refine hdom.mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have h := norm_add_sq_le (∑ i, a i x (derivative f i x)) (b x (value f x))
  have hp := principalError_bound a f x (ha x)
  have hl := lowerError_bound b f x (hb x)
  dsimp only [system,Pi.add_apply]
  nlinarith
lemma constantSystem_integrable (c : Fin 4 → W →L[ℝ] Q) (f : Field) :
    Integrable (fun x => ‖constantSystem c f x‖^2) := by
  have h := system_integrable (fun i _ => c i) (fun _ => 0) f
    (δ := ∑ i, ‖c i‖) (C := 0) (fun _ => continuous_const) continuous_const
    (fun _ i => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    (fun _ => by simp)
  simpa only [system,zero_apply,add_zero,constantSystem] using h

lemma comparison_pointwise (c : Fin 4 → W →L[ℝ] Q)
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (f : Field) (x : V) {δ C : ℝ} (ha : ∀ i, ‖a i x-c i‖ ≤ δ) (hb : ‖b x‖ ≤ C) :
    ‖constantSystem c f x‖^2 ≤ 2*‖system a b f x‖^2 +
      16*δ^2*gradient f x + 4*C^2*‖value f x‖^2 := by
  let E : Q := ∑ i, (a i x-c i) (derivative f i x)
  let L : Q := b x (value f x)
  have he : constantSystem c f x = system a b f x + -(E+L) := by
    simp only [constantSystem,system,E,L,sub_apply,Finset.sum_sub_distrib]
    abel
  have h0 := norm_add_sq_le (system a b f x) (-(E+L))
  rw [← he,norm_neg] at h0
  have h1 := norm_add_sq_le E L
  have hE := principalError_bound (fun i y => a i y-c i) f x ha
  have hL := lowerError_bound b f x hb
  change ‖E‖^2 ≤ _ at hE
  change ‖L‖^2 ≤ _ at hL
  nlinarith

theorem garding (c : Fin 4 → W →L[ℝ] Q) {K δ C : ℝ} (hK : 0 < K)
    (hsmall : 16*K*δ^2 ≤ 1/2)
    (henergy : ∀ f : Field, (∫ x, gradient f x) ≤ K * (∫ x, ‖constantSystem c f x‖^2))
    (a : Fin 4 → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (hac : ∀ i, Continuous (a i)) (hbc : Continuous b)
    (ha : ∀ x i, ‖a i x-c i‖ ≤ δ) (hb : ∀ x, ‖b x‖ ≤ C) (f : Field) :
    (∫ x, gradient f x) ≤ 4*K*(∫ x, ‖system a b f x‖^2) +
      8*K*C^2*(∫ x, ‖value f x‖^2) := by
  have ha' (x : V) (i : Fin 4) : ‖a i x‖ ≤ δ + ∑ j, ‖c j‖ := by
    calc
      ‖a i x‖ ≤ ‖a i x-c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
      _ ≤ δ + ∑ j, ‖c j‖ := add_le_add (ha x i)
        (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  have hS := system_integrable a b f hac hbc ha' hb
  have hG := gradient_integrable f
  have hF := value_integrable f
  have hcomp := integral_mono (constantSystem_integrable c f)
    (((hS.const_mul 2).add (hG.const_mul (16*δ^2))).add (hF.const_mul (4*C^2)))
    (fun x => comparison_pointwise c a b f x (ha x) (hb x))
  dsimp only [Pi.add_apply] at hcomp
  erw [integral_add ((hS.const_mul 2).add (hG.const_mul (16*δ^2))) (hF.const_mul (4*C^2)),
    integral_add (hS.const_mul 2) (hG.const_mul (16*δ^2)),
    integral_const_mul,integral_const_mul,integral_const_mul] at hcomp
  have hcompK := mul_le_mul_of_nonneg_left hcomp hK.le
  have hcoerce := henergy f
  have hG0 : 0 ≤ ∫ x, gradient f x := integral_nonneg (gradient_nonneg f)
  have hsmallG := mul_le_mul_of_nonneg_right hsmall hG0
  nlinarith
end TamingCompatibility.HodgeMatrixEnergy

end
end

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.HodgeNormalSymbol
open EuclideanEnergy
abbrev W := EuclideanSpace ℝ (Fin 6)
abbrev Q := EuclideanSpace ℝ (Fin 8)

def symbol (ξ : V) (a : W) : Q := WithLp.toLp 2
  ![(UnitaryFrame.interior ξ a) 0,(UnitaryFrame.interior ξ a) 1,
    (UnitaryFrame.interior ξ a) 2,(UnitaryFrame.interior ξ a) 3,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 0,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 1,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 2,
    (UnitaryFrame.interior ξ (UnitaryFrame.star a)) 3]

lemma symbol_add (ξ : V) (a b : W) : symbol ξ (a+b) = symbol ξ a+symbol ξ b := by
  ext i
  fin_cases i <;> simp [symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring
lemma symbol_smul (ξ : V) (c : ℝ) (a : W) : symbol ξ (c • a) = c • symbol ξ a := by
  ext i
  fin_cases i <;> simp [symbol,UnitaryFrame.interior,UnitaryFrame.star] <;> ring

def normalSymbol (ξ : V) : W →L[ℝ] Q :=
  LinearMap.toContinuousLinearMap {
    toFun := symbol ξ
    map_add' := symbol_add ξ
    map_smul' := symbol_smul ξ }

lemma normalSymbol_apply (ξ : V) (a : W) : normalSymbol ξ a = symbol ξ a := rfl
lemma normalSymbol_inner (ξ : V) (a b : W) :
    ⟪normalSymbol ξ a,normalSymbol ξ b⟫ = ⟪ξ,ξ⟫*⟪a,b⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star,Fin.sum_univ_succ]
  ring

lemma normalSymbol_polarized (ξ η : V) (a b : W) :
    ⟪normalSymbol ξ a,normalSymbol η b⟫ + ⟪normalSymbol η a,normalSymbol ξ b⟫ =
      2*⟪ξ,η⟫*⟪a,b⟫ := by
  simp only [PiLp.inner_apply]
  simp [normalSymbol_apply,symbol,UnitaryFrame.interior,UnitaryFrame.star,Fin.sum_univ_succ]
  ring

theorem normalSymbol_adjoint_polarized (ξ η : V) :
    (normalSymbol ξ).adjoint ∘L normalSymbol η +
      (normalSymbol η).adjoint ∘L normalSymbol ξ =
      (2*⟪ξ,η⟫) • ContinuousLinearMap.id ℝ W := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_left ℝ
  intro b
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.smul_apply,
    ContinuousLinearMap.id_apply,inner_smul_right,inner_add_right]
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  exact normalSymbol_polarized ξ η b a
end TamingCompatibility.HodgeNormalSymbol

end
end

end
end

end OAI
