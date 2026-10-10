import Mathlib
import OAI.Computability.MinUncut.Estimates.Convolution
import OAI.Computability.MinUncut.Analysis.GaussianSmallBall

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def evaluationProof (a : A) : FoldedProof A where
  answer P := P a
  folded _ := rfl

def codeVector (z : Code m n) : Point m n → ℝ :=
  fun x => (Real.sqrt (n^m:ℕ))⁻¹ * BinaryFourier.sign (z.val x)

lemma codeVector_norm (hn : 0<n) (z : Code m n) : ‖vector (codeVector z)‖=1 := by
  have hn' : (0:ℝ)<(n^m:ℕ) := by positivity
  have he : ‖vector (codeVector z)‖^2=1 := by
    simp only [EuclideanSpace.real_norm_sq_eq,vector,codeVector,mul_pow,sign_sq,mul_one,
      Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,inv_pow]
    rw [Real.sq_sqrt hn'.le,mul_inv_cancel₀ hn'.ne']
  nlinarith [norm_nonneg (vector (codeVector z))]

lemma score_codeVector (z : Code m n) (c : Point m n → ℝ) :
    score (codeVector z) c=(Real.sqrt (n^m:ℕ))⁻¹ * ∑ x, c x*BinaryFourier.sign (z.val x) := by
  simp only [score,codeVector,mul_assoc,← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

def labelFunctional (a : A) (x : Point m n) : Module.Dual F₂ (FaceArray A m n) where
  toFun B := ∑ i : Fin m, B ⟨i,face x i⟩ a
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

omit [Fintype A] in
lemma character_label (a : A) (x : Point m n) (B : FaceArray A m n) :
    character (labelFunctional a x) B=BinaryFourier.sign ((labelCode B a).val x) := rfl

lemma labelFunctional_degree (a : A) (x : Point m n) : degree (labelFunctional a x) ≤ m := by
  classical
  have hs : mask (labelFunctional a x) ⊆ Finset.univ.image (fun i : Fin m => (⟨i,face x i⟩ : Row m n)) := by
    intro r hr
    by_contra h
    have hneq : ∀ i : Fin m, (⟨i,face x i⟩ : Row m n)≠r := by
      intro i hi
      exact h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
    have hz : frequency (labelFunctional a x) r=0 := by
      ext b
      simp only [frequency,LinearMap.comp_apply,labelFunctional,LinearMap.coe_mk,AddHom.coe_mk,
        LinearMap.single_apply]
      change (∑ i : Fin m, (Pi.single r b : FaceArray A m n) ⟨i,face x i⟩ a)=0
      apply Finset.sum_eq_zero
      intro i _
      rw [Pi.single_eq_of_ne (hneq i)]
      rfl
    exact (Finset.mem_filter.mp hr).2 hz
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (by simp))

lemma character_noise_distance {R W : Type*} [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
    (a : ℝ) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    (𝔼 C, density a B C*(character α B-character α C)^2)=2*(1-(1-a)^degree α) := by
  have he (C : R → W) : density a B C*(character α B-character α C)^2=
      2*density a B C-2*character α B*(density a B C*character α C) := by
    have hb := character_sq α B
    have hc := character_sq α C
    nlinarith only [congrArg (fun t => density a B C*t) hb,congrArg (fun t => density a B C*t) hc]
  simp_rw [he,Finset.expect_sub_distrib,← Finset.mul_expect,density_mean,mul_one]
  change 2-2*character α B*noise a (character α) B=_
  rw [noise_character]
  have hb := character_sq α B
  nlinarith only [congrArg (fun t => (1-a)^degree α*t) hb]

lemma character_noise_distance_le {R W : Type*} [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
    {ρ : ℝ} (hρ1 : ρ≤1) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    (𝔼 C, density ρ B C*(character α B-character α C)^2)≤2*(degree α:ℝ)*ρ := by
  rw [character_noise_distance]
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -ρ) (degree α)
  simp only [mul_neg,← sub_eq_add_neg] at h
  linarith

end MinUncut.Inner

end
end

end OAI
