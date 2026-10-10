import Mathlib
import OAI.Probability.SKGap.Localization.FrobeniusSq
import OAI.Probability.SKGap.Stability.ImplicitLinear

namespace OAI

section

noncomputable section
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma equations_balance (j χ r p : ℝ) (A J : E →L[ℝ] E) (u m t ell w y : E) (c : ℝ)
    (h : Equations j χ r p A J u m t ell w y c) :
    w=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
  rcases h with ⟨hw,hy,hc⟩
  calc
    w=A (u+y-(j*c) • t) := hw
    _=A (u+J w-(j*χ) • w-(j*c) • (m+t)) := by
      rw [hy]
      congr 1
      module

theorem implicit_difference_equation (j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (w-w')=
      (A-A') (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (u-u')-(j*(χ-χ')) • A' w-(j*c) • A' (m-m')-
      (j*(r*inner ℝ (ell-ell') w+(p-p'))) • A' (m'+t) := by
  have hw:=equations_balance j χ r p A J u m t ell w y c h
  have hw':=equations_balance j χ' r p' A' J u' m' t ell' w' y' c' h'
  have hc:=h.2.2
  have hc':=h'.2.2
  simp only [L₂,add_apply,sub_apply,smul_apply,neg_apply,one_apply_eq_self,
    mul_apply_eq_comp,rank_apply,map_add,map_sub,map_smul,map_neg,inner_sub_left] at hw hw' ⊢
  rw [hc] at hw ⊢
  rw [hc'] at hw'
  linear_combination (norm := module) hw-hw'

theorem implicit_scaled_difference (s j χ χ' r p p' : ℝ)
    (A A' J : E →L[ℝ] E) (u u' m m' t ell ell' w w' y y' : E) (c c' : ℝ)
    (h : Equations j χ r p A J u m t ell w y c)
    (h' : Equations j χ' r p' A' J u' m' t ell' w' y' c') :
    (1+A'*L₂ j χ' r J (m'+t) ell') (s • (w-w'))=
      (s • (A-A')) (u+J w-(j*χ) • w-(j*c) • (m+t))+
      A' (s • (u-u'))-(j*(s*(χ-χ'))) • A' w-(j*c) • A' (s • (m-m'))-
      (j*(r*inner ℝ (s • (ell-ell')) w+s*(p-p'))) • A' (m'+t) := by
  have H:=congrArg (fun x:E=>s • x)
    (implicit_difference_equation j χ χ' r p p' A A' J u u' m m' t ell ell' w w' y y' c c' h h')
  simp only [map_smul,smul_apply,real_inner_smul_left] at H ⊢
  linear_combination (norm := module) H

lemma implicit_scalar_difference (s r p p' : ℝ) (ell ell' w w' : E) :
    s*(r*inner ℝ ell w+p-(r*inner ℝ ell' w'+p'))=
      r*inner ℝ (s • (ell-ell')) w+s*(p-p')+
        r*inner ℝ ell' (s • (w-w')) := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right]
  ring

end SKGap.ImplicitSystem

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def columnNorm (V : ι→E) : ℝ := ‖(WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))‖
omit [InnerProductSpace ℝ E] in
lemma columnNorm_nonneg (V : ι→E) : 0≤columnNorm V := norm_nonneg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sq (V : ι→E) : columnNorm V^2=∑i,‖V i‖^2 := by
  exact PiLp.norm_sq_eq_of_L2 (fun _ : ι=>E) (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_add (U V : ι→E) : columnNorm (U+V)≤columnNorm U+columnNorm V :=
  norm_add_le (WithLp.toLp 2 U : PiLp 2 (fun _ : ι=>E)) (WithLp.toLp 2 V)
omit [InnerProductSpace ℝ E] in
lemma columnNorm_neg (V : ι→E) : columnNorm (-V)=columnNorm V := norm_neg _
omit [InnerProductSpace ℝ E] in
lemma columnNorm_sub (U V : ι→E) : columnNorm (U-V)≤columnNorm U+columnNorm V := by
  simpa only [sub_eq_add_neg,columnNorm_neg] using columnNorm_add U (-V)
lemma columnNorm_smul (a : ℝ) (V : ι→E) : columnNorm (a • V)=|a| *columnNorm V :=
  norm_smul a (WithLp.toLp 2 V : PiLp 2 (fun _ : ι=>E))
omit [InnerProductSpace ℝ E] in
lemma columnNorm_bound {U V : ι→E} {C : ℝ} (hC : 0≤C)
    (h : ∀i,‖U i‖≤C*‖V i‖) : columnNorm U≤C*columnNorm V := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (U i)) (h i) 2
lemma columnNorm_operator (A : ι→E→L[ℝ]E) (V : ι→E) {C : ℝ}
    (hC : 0≤C) (hA : ∀i,‖A i‖≤C) :
    columnNorm (fun i=>A i (V i))≤C*columnNorm V := by
  apply columnNorm_bound hC
  intro i; exact ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
lemma columnNorm_vector_scalar (V : ι→E) (a : ι→ℝ) {C : ℝ}
    (hC : 0≤C) (hV : ∀i,‖V i‖≤C) :
    columnNorm (fun i=>a i • V i)≤C*columnNorm a := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (columnNorm_nonneg _))
  simp only [←sq,columnNorm_sq,norm_smul,Real.norm_eq_abs,mul_pow,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    have h:=pow_le_pow_left₀ (norm_nonneg (V i)) (hV i) 2
    nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg |a i|)]

omit [InnerProductSpace ℝ E] in
lemma columnNorm_add_sub_sub_sub (a b c d e : ι→E) :
    columnNorm (a+b-c-d-e)≤columnNorm a+columnNorm b+columnNorm c+columnNorm d+columnNorm e := by
  have h₁:=columnNorm_add a b
  have h₂:=columnNorm_sub (a+b) c
  have h₃:=columnNorm_sub (a+b-c) d
  have h₄:=columnNorm_sub (a+b-c-d) e
  linarith

variable [FiniteDimensional ℝ E]

lemma column_inverse_estimate (X L S : ι→E→L[ℝ]E) (U V : ι→E)
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X i‖≤X₀) (hL : ∀i,‖L i‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (S i v))
    (hPert : ∀i,‖(1+X i*L i*X i)-S i‖≤δ/2)
    (hEq : ∀i,(1+X i*X i*L i) (U i)=V i) :
    columnNorm U≤(1+X₀^2*(δ/2)⁻¹*L₀)*columnNorm V := by
  apply columnNorm_bound (by positivity)
  intro i
  obtain ⟨B,hMB,hBM,hB⟩:=SKGap.ImplicitLinear.unnormalized_inverse (X i) (L i) (S i)
    (by linarith : δ/2<δ) (hS i) (hPert i)
  have he : U i=B (V i) := by
    rw [←hEq i]
    change U i=(B*(1+X i*X i*L i)) (U i)
    rw [hBM]; rfl
  rw [he]
  apply (B.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply hB.trans
  have hX2 : ‖X i‖^2≤X₀^2 := (sq_le_sq₀ (norm_nonneg _) hX₀).mpr (hX i)
  have hinv : 0≤(δ-δ/2)⁻¹ := inv_nonneg.mpr (by linarith)
  calc
    _ ≤ 1+X₀^2*(δ-δ/2)⁻¹*L₀ := add_le_add le_rfl
      (mul_le_mul (mul_le_mul_of_nonneg_right hX2 hinv) (hL i) (norm_nonneg _) (by positivity))
    _ = _ := by congr 2; ring

theorem implicit_columns_bound (j χ r p : ℝ) (X J : E→L[ℝ]E)
    (u m t ell w y : E) (c : ℝ)
    (s χ' p' c' : ι→ℝ) (X' : ι→E→L[ℝ]E) (u' m' ell' w' y' q' : ι→E) (b' : ι→ℝ)
    (h : Equations j χ r p (X*X) J u m t ell w y c)
    (h' : ∀i,Equations j (χ' i) r (p' i) (X' i*X' i) J (u' i) (m' i) t (ell' i) (w' i) (y' i) (c' i))
    {δ X₀ L₀ : ℝ} (hδ : 0<δ) (hX₀ : 0≤X₀) (hL₀ : 0≤L₀)
    (hX : ∀i,‖X' i‖≤X₀) (hL : ∀i,‖L₂ j (χ' i) r J (m' i+t) (ell' i)‖≤L₀)
    (hS : ∀i v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j (b' i) r (X' i) J (q' i) v))
    (hSmall : ∀i,|j| *|χ' i-b' i| *‖X' i‖^2+|j*r| *‖X' i‖^2*
      (‖m' i+t-(2:ℝ) • q' i‖*‖ell' i‖+2*‖q' i‖*‖ell' i+q' i‖)≤δ/2) :
    let A:=X*X
    let A':=fun i=>X' i*X' i
    let B:=u+J w-(j*χ) • w-(j*c) • (m+t)
    let z:=fun i=>r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i)
    columnNorm (fun i=>s i • (w-w' i))≤(1+X₀^2*(δ/2)⁻¹*L₀)*
      (columnNorm (fun i=>(s i • (A-A' i)) B)+
        columnNorm (fun i=>A' i (s i • (u-u' i)))+
        columnNorm (fun i=>(j*(s i*(χ-χ' i))) • A' i w)+
        columnNorm (fun i=>(j*c) • A' i (s i • (m-m' i)))+
        columnNorm (fun i=>(j*z i) • A' i (m' i+t))) := by
  dsimp only
  let V:=fun i=>(s i • (X*X-X' i*X' i)) (u+J w-(j*χ) • w-(j*c) • (m+t))+
    (X' i*X' i) (s i • (u-u' i))-(j*(s i*(χ-χ' i))) • (X' i*X' i) w-
    (j*c) • (X' i*X' i) (s i • (m-m' i))-
    (j*(r*inner ℝ (s i • (ell-ell' i)) w+s i*(p-p' i))) • (X' i*X' i) (m' i+t)
  have hlow:=column_inverse_estimate X' (fun i=>L₂ j (χ' i) r J (m' i+t) (ell' i))
    (fun i=>stableMatrix j (b' i) r (X' i) J (q' i)) (fun i=>s i • (w-w' i)) V
    hδ hX₀ hL₀ hX hL hS
    (fun i=>(normalized_difference_bound j (χ' i) (b' i) r (X' i) J (m' i+t) (ell' i) (q' i)).trans (hSmall i))
    (fun i=>implicit_scaled_difference (s i) j χ (χ' i) r p (p' i) (X*X) (X' i*X' i) J
      u (u' i) m (m' i) t ell (ell' i) w (w' i) y (y' i) c (c' i) h (h' i))
  apply hlow.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact columnNorm_add_sub_sub_sub _ _ _ _ _

end SKGap.ImplicitSystem
namespace SKGapCutoff.Recipe
lemma columnNorm_matrix {dimension : ℕ} (D : Interaction dimension) :
    SKGap.ImplicitSystem.columnNorm (fun k=>(WithLp.toLp 2 (fun i=>D i k) : EuclideanSpace ℝ (Fin dimension)))=‖D‖ := by
  apply (sq_eq_sq₀ (SKGap.ImplicitSystem.columnNorm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.ImplicitSystem.columnNorm_sq,SKGap.frobenius_sq]
  simp only [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_comm
end SKGapCutoff.Recipe

end
end

end OAI
