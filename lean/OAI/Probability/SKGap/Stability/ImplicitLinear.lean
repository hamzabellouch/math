import Mathlib
import OAI.Probability.SKGap.Localization.ResidualRecipe

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma lower_norm_of_quadratic (M : E →L[ℝ] E) {c : ℝ}
    (h : ∀v,c*‖v‖^2 ≤ ⟪v, M v⟫) (v : E) : c*‖v‖≤‖M v‖ := by
  by_cases hv : ‖v‖=0
  · simp [hv]
  have hn : 0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have H:=(h v).trans (real_inner_le_norm v (M v))
  nlinarith

lemma quadratic_perturbation (M S : E →L[ℝ] E) {c e : ℝ}
    (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) (v : E) :
    (c-e)*‖v‖^2 ≤ ⟪v, M v⟫ := by
  have hI:=abs_real_inner_le_norm v ((M-S) v)
  have hO:=(M-S).le_opNorm v
  have hm:=mul_le_mul_of_nonneg_right hMS (norm_nonneg v)
  have hh:=mul_le_mul_of_nonneg_left (hO.trans hm) (norm_nonneg v)
  have he : ⟪v, (M-S) v⟫=⟪v, M v⟫-⟪v, S v⟫ := by simp only [sub_apply,inner_sub_right]
  rw [he] at hI
  have H := (neg_abs_le (⟪v, M v⟫-⟪v, S v⟫)).trans (le_refl _)
  nlinarith [hS v]

lemma injective_of_lower_norm (M : E →L[ℝ] E) {c : ℝ} (hc : 0<c)
    (h : ∀v,c*‖v‖≤‖M v‖) : Function.Injective M := by
  intro x y hxy
  have H:=h (x-y)
  have he : M (x-y)=0 := by simp [hxy]
  rw [he,norm_zero] at H
  have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [FiniteDimensional ℝ E]

theorem exists_bounded_inverse (M S : E →L[ℝ] E) {c e : ℝ}
    (hce : e<c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫) (hMS : ‖M-S‖≤e) :
    ∃ N : E →L[ℝ] E,M*N=1 ∧ N*M=1 ∧ ‖N‖≤(c-e)⁻¹ := by
  have hc : 0<c-e := sub_pos.mpr hce
  have hlow : ∀v,(c-e)*‖v‖≤‖M v‖ :=
    lower_norm_of_quadratic M (quadratic_perturbation M S hS hMS)
  have hinj := injective_of_lower_norm M hc hlow
  let L : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective M.toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩
  let N : E →L[ℝ] E := L.symm.toLinearMap.toContinuousLinearMap
  have hMN : M*N=1 := by
    ext x; exact L.apply_symm_apply x
  have hNM : N*M=1 := by
    ext x; exact L.symm_apply_apply x
  refine ⟨N,hMN,hNM,N.opNorm_le_bound (inv_nonneg.mpr hc.le) ?_⟩
  intro x
  have H:=hlow (N x)
  have hx : M (N x)=x := by change (M*N) x=x; rw [hMN]; rfl
  rw [hx] at H
  exact (le_div_iff₀ hc).2 (by nlinarith) |>.trans_eq (by ring)

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
variable {R : Type*} [Ring R]

lemma jacobson_left (X Y N : R) (hN : (1+Y*X)*N=1) :
    (1+X*Y)*(1-X*N*Y)=1 := by
  calc
    _ = 1+X*(1-(1+Y*X)*N)*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

lemma jacobson_right (X Y N : R) (hN : N*(1+Y*X)=1) :
    (1-X*N*Y)*(1+X*Y)=1 := by
  calc
    _ = 1+X*(1-N*(1+Y*X))*Y := by noncomm_ring
    _ = 1 := by rw [hN]; simp

end SKGap.ImplicitLinear

namespace SKGap.ImplicitLinear
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unnormalized_inverse (X L S : E →L[ℝ] E) {c e : ℝ}
    (hce : e<c) (hS : ∀v,c*‖v‖^2 ≤ ⟪v, S v⟫)
    (hMS : ‖(1+X*L*X)-S‖≤e) :
    ∃ B : E →L[ℝ] E,(1+X*X*L)*B=1 ∧ B*(1+X*X*L)=1 ∧
      ‖B‖≤1+‖X‖^2*(c-e)⁻¹*‖L‖ := by
  obtain ⟨N,hN,hN',hNb⟩ := exists_bounded_inverse (1+X*L*X) S hce hS hMS
  let B:=1-X*N*(X*L)
  refine ⟨B,?_,?_,?_⟩
  · simpa only [B,mul_assoc] using jacobson_left X (X*L) N hN
  · simpa only [B,mul_assoc] using jacobson_right X (X*L) N hN'
  · calc
      ‖B‖ ≤ ‖(1 : E →L[ℝ] E)‖+‖X*N*(X*L)‖ := norm_sub_le _ _
      _ ≤ 1+‖X‖*‖N‖*(‖X‖*‖L‖) := by
        apply add_le_add (ContinuousLinearMap.norm_id_le)
        exact (norm_mul_le _ _).trans (mul_le_mul (norm_mul_le _ _) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ ≤ 1+‖X‖*(c-e)⁻¹*(‖X‖*‖L‖) := by
        gcongr
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma unique_solution_of_inverse (M B : E →L[ℝ] E) (hMB : M*B=1) (hBM : B*M=1)
    (b : E) : ∃!w,M w=b := by
  refine ⟨B b,?_,?_⟩
  · change (M*B) b=b; rw [hMB]; rfl
  · intro w hw
    have := congrArg (fun f : E →L[ℝ] E=>f w) hBM
    simpa only [mul_apply_eq_comp,hw,one_apply_eq_self] using this.symm

end SKGap.ImplicitLinear

end
end

section

noncomputable section
namespace SKGap.ImplicitSystem
open SKGap.ImplicitLinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rank (u v : E) : E →L[ℝ] E := (innerSL ℝ v).smulRight u

@[simp] lemma rank_apply (u v w : E) : rank u v w=inner ℝ v w • u := rfl

lemma rank_add_right (u v w : E) : rank u (v+w)=rank u v+rank u w := by
  ext x; simp only [rank_apply,inner_add_left,add_smul,add_apply]

lemma rank_add_left (u v w : E) : rank (u+v) w=rank u w+rank v w := by
  ext x; simp only [rank_apply,smul_add,add_apply]

lemma rank_sub_left (u v w : E) : rank (u-v) w=rank u w-rank v w := by
  ext x; simp only [rank_apply,smul_sub,sub_apply]

lemma rank_smul_left (a : ℝ) (u v : E) : rank (a • u) v=a • rank u v := by
  ext x; simp only [rank_apply,smul_apply]; module

lemma rank_norm_le (u v : E) : ‖rank u v‖≤‖u‖*‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  simp only [rank_apply,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (‖v‖*‖x‖)*‖u‖ := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (norm_nonneg _)
    _ = _ := by ring

lemma rank_perturbation (v ell m : E) :
    rank v ell+(2:ℝ) • rank m m=rank (v-(2:ℝ) • m) ell+(2:ℝ) • rank m (ell+m) := by
  rw [rank_sub_left,rank_smul_left,rank_add_right,smul_add]
  module

lemma rank_perturbation_bound (v ell m : E) :
    ‖rank v ell+(2:ℝ) • rank m m‖≤‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖ := by
  rw [rank_perturbation]
  calc
    _ ≤ ‖rank (v-(2:ℝ) • m) ell‖+‖(2:ℝ) • rank m (ell+m)‖ := norm_add_le _ _
    _ ≤ ‖v-(2:ℝ) • m‖*‖ell‖+2*(‖m‖*‖ell+m‖) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (rank_norm_le _ _) (mul_le_mul_of_nonneg_left (rank_norm_le _ _) (by norm_num))
    _ = _ := by ring

def L₂ (j χ r : ℝ) (J : E →L[ℝ] E) (v ell : E) : E →L[ℝ] E :=
  -J+(j*χ) • 1+(j*r) • rank v ell

def stableMatrix (j b r : ℝ) (X J : E →L[ℝ] E) (m : E) : E →L[ℝ] E :=
  1+(j*b) • (X*X)-X*J*X-(2*j*r) • (X*rank m m*X)

lemma normalized_difference (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    (1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m=
      (j*(χ-b)) • (X*X)+(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X) := by
  simp only [L₂,stableMatrix,mul_add,add_mul,mul_neg,neg_mul,mul_smul_comm,
    smul_mul_assoc,mul_one,smul_add,smul_smul]
  module

lemma normalized_difference_bound (j χ b r : ℝ) (X J : E →L[ℝ] E) (v ell m : E) :
    ‖(1+X*L₂ j χ r J v ell*X)-stableMatrix j b r X J m‖≤
      |j| * |χ-b| * ‖X‖^2+|j*r| * ‖X‖^2*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖) := by
  rw [normalized_difference]
  calc
    _ ≤ ‖(j*(χ-b)) • (X*X)‖+‖(j*r) • (X*(rank v ell+(2:ℝ) • rank m m)*X)‖ := norm_add_le _ _
    _ ≤ |j| * |χ-b| * (‖X‖*‖X‖)+|j*r| * (‖X‖*(‖v-(2:ℝ) • m‖*‖ell‖+2*‖m‖*‖ell+m‖)*‖X‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_mul_le X X) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (rank_perturbation_bound v ell m) (norm_nonneg _)))
          (norm_nonneg _))
    _ = _ := by ring

def Equations (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w y : E) (c : ℝ) : Prop :=
  w=A (u+y-(j*c) • t) ∧ y=J w-(j*χ) • w-(j*c) • m ∧ c=r*inner ℝ ell w+p

lemma eliminated_equation (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w : E) :
    Equations j χ r p A J u m t ell w
      (J w-(j*χ) • w-(j*(r*inner ℝ ell w+p)) • m) (r*inner ℝ ell w+p) ↔
      (1+A*L₂ j χ r J (m+t) ell) w=A (u-(j*p) • (m+t)) := by
  simp only [Equations,and_true,L₂,add_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg]
  constructor <;> intro h <;> linear_combination (norm := module) h

variable [FiniteDimensional ℝ E]

theorem unique_implicit_solution (j χ b r p : ℝ) (X J : E →L[ℝ] E)
    (u m t ell q : E) {δ : ℝ} (hδ : 0<δ)
    (hStable : ∀v,δ*‖v‖^2 ≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| * |χ-b| * ‖X‖^2+|j*r| * ‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2) :
    ∃! z : E×E×ℝ,Equations j χ r p (X*X) J u m t ell z.1 z.2.1 z.2.2 := by
  have hPert := (normalized_difference_bound j χ b r X J (m+t) ell q).trans hSmall
  obtain ⟨B,hMB,hBM,hB⟩ := unnormalized_inverse X (L₂ j χ r J (m+t) ell)
    (stableMatrix j b r X J q) (by linarith : δ/2<δ) hStable hPert
  obtain ⟨w,hw,huniq⟩:=unique_solution_of_inverse (1+X*X*L₂ j χ r J (m+t) ell) B hMB hBM
    ((X*X) (u-(j*p) • (m+t)))
  let c:=r*inner ℝ ell w+p
  let y:=J w-(j*χ) • w-(j*c) • m
  have hEq : Equations j χ r p (X*X) J u m t ell w y c := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w).mpr
    simpa only [mul_assoc] using hw
  refine ⟨(w,y,c),hEq,?_⟩
  rintro ⟨w',y',c'⟩ h'
  rcases h' with ⟨hw',hy',hc'⟩
  have hwe : (1+(X*X)*L₂ j χ r J (m+t) ell) w'=(X*X) (u-(j*p) • (m+t)) := by
    apply (eliminated_equation j χ r p (X*X) J u m t ell w').mp
    refine ⟨?_,rfl,rfl⟩
    simpa only [←hc',←hy'] using hw'
  have hww : w'=w := huniq w' (by simpa only [mul_assoc] using hwe)
  have hcc : c'=c := by simpa only [hww] using hc'
  have hyy : y'=y := by simpa only [hww,hcc] using hy'
  simp only [hww,hyy,hcc]

end SKGap.ImplicitSystem

end
end

end OAI
