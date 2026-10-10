import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitCoefficient
import OAI.Probability.SKGap.Stability.ImplicitFrobenius

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma L₂_norm_le (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E) :
    ‖L₂ j χ r J v ell‖≤‖J‖+|j| *|χ|+|j| *|r| *‖v‖*‖ell‖ := by
  unfold L₂
  calc
    _ ≤ ‖-J+(j*χ) • (1:E→L[ℝ]E)‖+‖(j*r) • rank v ell‖ := norm_add_le _ _
    _ ≤ (‖J‖+|j| *|χ|)+|j| *|r| *(‖v‖*‖ell‖) := by
      apply add_le_add
      · apply (norm_add_le _ _).trans
        simp only [norm_neg,norm_smul,Real.norm_eq_abs,abs_mul]
        exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le)
      · rw [norm_smul,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left (rank_norm_le v ell) (by positivity)
    _ = _ := by ring

lemma L₂_normalized_bound (j χ r : ℝ) (J : E→L[ℝ]E) (v ell : E)
    {d V Q A L : ℝ} (hr : 0≤r) (hd : 0≤d) (hscale : r*d^2=1)
    (hV : 0≤V) (hQ : 0≤Q) (hv : ‖v‖≤V*d) (hell : ‖ell‖≤Q*d)
    (hχ : |χ|≤A) (hJ : ‖J‖≤L) :
    ‖L₂ j χ r J v ell‖≤L+|j| *A+|j| *V*Q := by
  apply (L₂_norm_le j χ r J v ell).trans
  rw [abs_of_nonneg hr]
  have hmul:=mul_le_mul hv hell (norm_nonneg ell) (mul_nonneg hV hd)
  calc
    _ ≤ L+|j| *A+|j| *r*((V*d)*(Q*d)) := by
      rw [mul_assoc (|j| *r)]
      exact add_le_add (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hmul (by positivity))
    _ = L+|j| *A+|j| *V*Q*(r*d^2) := by ring
    _ ≤ _ := by
      simpa only [mul_one] using add_le_add (le_refl (L+|j| *A))
        (mul_le_mul_of_nonneg_left hscale.le (mul_nonneg (mul_nonneg (abs_nonneg j) hV) hQ))

variable [FiniteDimensional ℝ E]

theorem implicit_uniform_size (j χ b r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell q w y : E) (c : ℝ)
    {δ d A L Q U P : ℝ} (hδ : 0<δ) (hd : 0<d) (hr : 0≤r) (hscale : r*d^2=1)
    (hA : 0≤A) (hL : 0≤L) (hQ : 0≤Q) (hU : 0≤U) (hP : 0≤P)
    (hX : ‖X‖^2≤A) (hJ : ‖J‖≤L) (hχ : |χ|≤A)
    (hu : ‖u‖≤U) (hm : ‖m‖≤d) (ht : ‖t‖≤d) (hell : ‖ell‖≤Q*d) (hp : d*|p|≤P)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2+|j*r| *‖X‖^2*
      (‖m+t-(2:ℝ) • q‖*‖ell‖+2*‖q‖*‖ell+q‖)≤δ/2)
    (hEq : Equations j χ r p (X*X) J u m t ell w y c) :
    let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
    ‖w‖≤W ∧ d*|c|≤Q*W+P ∧ ‖y‖≤(L+|j| *A)*W+|j| *(Q*W+P) := by
  dsimp only
  let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q))*A*(U+2*|j| *P)
  have hv : ‖m+t‖≤2*d := (norm_add_le _ _).trans (by linarith)
  have hL₂ : ‖L₂ j χ r J (m+t) ell‖≤L+|j| *A+2*|j| *Q := by
    convert L₂_normalized_bound j χ r J (m+t) ell hr hd.le hscale (by norm_num : (0:ℝ)≤2) hQ hv hell hχ hJ using 1; ring
  have hRHS : ‖u‖+|j| *|p| *(‖m‖+‖t‖)≤U+2*|j| *P := by
    calc
      _ ≤ U+|j| *|p| *(2*d) := add_le_add hu (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = U+2*|j| *(d*|p|) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (by positivity))
  have hinv : 0≤(δ/2)⁻¹ := by positivity
  have hK : 0≤1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by positivity
  have hKK : 1+‖X‖^2*(δ/2)⁻¹*‖L₂ j χ r J (m+t) ell‖≤
      1+A*(δ/2)⁻¹*(L+|j| *A+2*|j| *Q) := by
    exact add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_right hX hinv) hL₂ (norm_nonneg _) (by positivity))
  obtain ⟨hw,hc,hy⟩:=implicit_size_bounds j χ b r p X J u m t ell q w y c hδ hStable hSmall hEq
  have hw' : ‖w‖≤W := hw.trans (by
    simpa only [W,mul_comm] using mul_le_mul hRHS
      (mul_le_mul_of_nonneg_right hKK (sq_nonneg _) |>.trans (mul_le_mul_of_nonneg_left hX hK))
      (by positivity)
      (add_nonneg hU (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg j)) hP)))
  have hc' : d*|c|≤Q*W+P := by
    have hh:=implicit_scalar_size r p ell w
    rw [←hEq.2.2,abs_of_nonneg hr] at hh
    have hb:=mul_le_mul hell hw' (norm_nonneg w) (mul_nonneg hQ hd.le)
    calc
      _ ≤ d*(r*((Q*d)*W)+|p|) := mul_le_mul_of_nonneg_left
        (hh.trans (add_le_add (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hr) le_rfl)) hd.le
      _ = Q*W*(r*d^2)+d*|p| := by ring
      _ = Q*W+d*|p| := by rw [hscale]; ring
      _ ≤ _ := add_le_add le_rfl hp
  refine ⟨hw',hc',?_⟩
  rw [hEq.2.1]
  apply (implicit_field_size J j χ c w m).trans
  rw [abs_mul]
  have h₁:=mul_le_mul (add_le_add hJ (mul_le_mul_of_nonneg_left hχ (abs_nonneg _))) hw'
    (norm_nonneg w) (by positivity : 0≤L+|j| *A)
  have h₂ : |j| *|c| *‖m‖≤|j| *(Q*W+P) := by
    calc
      _ ≤ |j| *|c| *d := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = |j| *(d*|c|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc' (abs_nonneg _)
  exact add_le_add h₁ h₂
end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

lemma implicit_field_difference (s j χ χ' r p p' : ℝ) (A A' J : E→L[ℝ]E)
    (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    s • (y-y')=J (s • (w-w'))-(j*χ') • (s • (w-w'))-
      (j*(s*(χ-χ'))) • w-(j*c) • (s • (m-m'))-(j*(s*(c-c'))) • m' := by
  rw [h.2.1,h'.2.1]
  simp only [map_sub,map_smul]
  module

theorem implicit_scalar_columns (s : ι→ℝ) (r p : ℝ) (ell w : E) (c : ℝ)
    (p' c' : ι→ℝ) (ell' w' : ι→E)
    (hc : c=r*inner ℝ ell w+p) (hc' : ∀i,c' i=r*inner ℝ (ell' i) (w' i)+p' i)
    {d R P Q : ℝ} (hr : 0≤r) (hd : 0<d) (hscale : r*d^2=1)
    (hR : 0≤R) (hD : columnNorm (fun i=>s i • (ell-ell' i))≤R*d)
    (hP : d*columnNorm (fun i=>s i*(p-p' i))≤P)
    (hQ : 0≤Q) (hL : ∀i,‖ell' i‖≤Q*d) :
    d*columnNorm (fun i=>s i*(c-c' i))≤R*‖w‖+P+Q*columnNorm (fun i=>s i • (w-w' i)) := by
  have he : (fun i=>s i*(c-c' i))=(fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)+
      r*inner ℝ (ell' i) (s i • (w-w' i))) := by
    funext i
    rw [hc,hc' i]
    exact implicit_scalar_difference (s i) r p (p' i) ell (ell' i) w (w' i)
  rw [he]
  exact normalized_scalar_difference _ _ _ _ w hr hd hscale hR hD hP hQ hL

theorem implicit_field_columns (s : ι→ℝ) (j χ r p : ℝ) (A J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ) (χ' p' c' : ι→ℝ)
    (A' : ι→E→L[ℝ]E) (u' m' ell' w' y' : ι→E)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (A' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {L H d Rχ Rm C M Dc : ℝ} (hL : 0≤L) (hH : 0≤H) (hd : 0<d)
    (hRχ : 0≤Rχ) (hRm : 0≤Rm) (hC : 0≤C) (hM : 0≤M)
    (hJ : ‖J‖≤L) (hχ : ∀i,|χ' i|≤H)
    (hDχ : columnNorm (fun i=>s i*(χ-χ' i))≤Rχ)
    (hDm : columnNorm (fun i=>s i • (m-m' i))≤Rm*d)
    (hc : d*|c|≤C) (hm : ∀i,‖m' i‖≤M*d)
    (hdc : d*columnNorm (fun i=>s i*(c-c' i))≤Dc) :
    columnNorm (fun i=>s i • (y-y' i))≤
      (L+|j| *H)*columnNorm (fun i=>s i • (w-w' i))+|j| *‖w‖*Rχ+|j| *C*Rm+|j| *M*Dc := by
  let Dw:=fun i=>s i • (w-w' i)
  let Dχ:=fun i=>s i*(χ-χ' i)
  let Dm:=fun i=>s i • (m-m' i)
  let Dc':=fun i=>s i*(c-c' i)
  have ha : columnNorm (fun i=>J (Dw i))≤L*columnNorm Dw :=
    columnNorm_operator (fun _=>J) Dw hL (fun _=>hJ)
  have hb : columnNorm (fun i=>(j*χ' i) • Dw i)≤(|j| *H)*columnNorm Dw := by
    apply columnNorm_compare _ _ (by positivity)
    intro i
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hχ i) (abs_nonneg j)) (norm_nonneg _)
  have he : columnNorm (fun i=>(j*Dχ i) • w)≤|j| *‖w‖*Rχ := by
    have eq : (fun i=>(j*Dχ i) • w)=j • (fun i=>Dχ i • w) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    exact (mul_le_mul_of_nonneg_left (columnNorm_vector_scalar (fun _=>w) Dχ (norm_nonneg w) (fun _=>le_rfl)) (abs_nonneg j)).trans
      (by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul hDχ
          (le_refl (|j| *‖w‖)) (mul_nonneg (abs_nonneg j) (norm_nonneg w)) hRχ)
  have hf : columnNorm (fun i=>(j*c) • Dm i)≤|j| *C*Rm := by
    change columnNorm ((j*c) • Dm)≤_
    rw [columnNorm_smul,abs_mul]
    calc
      _ ≤ |j| *|c| *(Rm*d) := mul_le_mul_of_nonneg_left hDm (by positivity)
      _ = (|j| *Rm)*(d*|c|) := by ring
      _ ≤ (|j| *Rm)*C := by
        simpa only [mul_comm] using mul_le_mul hc (le_refl (|j| *Rm))
          (mul_nonneg (abs_nonneg j) hRm) hC
      _ = _ := by ring
  have hg : columnNorm (fun i=>(j*Dc' i) • m' i)≤|j| *M*Dc := by
    have eq : (fun i=>(j*Dc' i) • m' i)=j • (fun i=>Dc' i • m' i) := by ext i; simp [mul_smul]
    rw [eq,columnNorm_smul]
    calc
      _ ≤ |j| *((M*d)*columnNorm Dc') := mul_le_mul_of_nonneg_left
        (columnNorm_vector_scalar m' Dc' (by positivity) hm) (abs_nonneg j)
      _ = (|j| *M)*(d*columnNorm Dc') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdc (by positivity)
  have eq : (fun i=>s i • (y-y' i))=(fun i=>J (Dw i))+(fun i=>-((j*χ' i) • Dw i))-
      (fun i=>(j*Dχ i) • w)-(fun i=>(j*c) • Dm i)-(fun i=>(j*Dc' i) • m' i) := by
    funext i
    simpa only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply,Dw,Dχ,Dm,Dc',sub_eq_add_neg] using
      implicit_field_difference (s i) j χ (χ' i) r p (p' i) A (A' i) J u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i)
  rw [eq]
  have ht:=columnNorm_add_sub_sub_sub (fun i=>J (Dw i)) (fun i=>-((j*χ' i) • Dw i))
    (fun i=>(j*Dχ i) • w) (fun i=>(j*c) • Dm i) (fun i=>(j*Dc' i) • m' i)
  change columnNorm _≤_ at ht
  have hn : columnNorm (fun i=>-((j*χ' i) • Dw i))=columnNorm (fun i=>(j*χ' i) • Dw i) := columnNorm_neg _
  rw [hn] at ht
  exact ht.trans (by nlinarith only [ha,hb,he,hf,hg])
end SKGap.ImplicitSystem

end
end

end OAI
