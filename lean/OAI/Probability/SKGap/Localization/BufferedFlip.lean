import Mathlib
import OAI.Probability.SKGap.Localization.LiteralMargin
import OAI.Probability.SKGap.Stability.LiteralStableEvent

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

lemma vector_column_opNorm (M : Interaction n) (k : Fin n) :
    vectorNorm (fun i=>M i k)≤SKGap.opNorm M := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [←pow_two]
  rw [vectorNorm_sq]
  exact SKGap.SourceError.matrix_column_square_le M k

lemma vector_flip_opNorm (F : VectorFields n) (x : Spin n) (k : Fin n) :
    vectorNorm (F (flip x k)-F x)≤2*SKGap.opNorm (derivativeMatrix F x) := by
  have H:=congrArg norm (halfDiff_column F x k)
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2),norm_sub_rev] at H
  have hcol:=vector_column_opNorm (derivativeMatrix F x) k
  change (1/2:ℝ)*vectorNorm (F (flip x k)-F x)=vectorNorm (fun i=>derivativeMatrix F x i k) at H
  linarith

lemma vector_flip_buffer (F : VectorFields n) (x : Spin n) {B ρ : ℝ}
    (hD : SKGap.opNorm (derivativeMatrix F x)≤B)
    (hsmall : 2*B≤ρ*Real.sqrt (n:ℝ))
    (hF : vectorNorm (F x)≤ρ*Real.sqrt (n:ℝ)) (k : Fin n) :
    vectorNorm (F (flip x k))≤(2*ρ)*Real.sqrt (n:ℝ) := by
  have H : vectorNorm (F (flip x k))≤vectorNorm (F x)+vectorNorm (F (flip x k)-F x) := by
    calc
      _ = vectorNorm (F x+(F (flip x k)-F x)) := by congr 1;ext i;simp
      _ ≤ _ := SKGap.vectorNorm_add_le _ _
  exact H.trans ((add_le_add hF ((vector_flip_opNorm F x k).trans
    ((mul_le_mul_of_nonneg_left hD (by norm_num)).trans hsmall))).trans_eq (by ring))

lemma residualCutoff_flip_buffer (hn : 0<n) {j ρ B : ℝ} (hρ : 0<ρ)
    (J : Interaction n) (h : Fin n→ℝ) (l : ℕ) (x : Spin n)
    (hcut : residualCutoff ρ j J h l x≠0)
    (hD₀ : SKGap.opNorm (derivativeMatrix (Primary.residual j J h l) x)≤B)
    (hD₁ : SKGap.opNorm (derivativeMatrix (Primary.residual j J h (l+1)) x)≤B)
    (hsmall : 2*B≤ρ*Real.sqrt (n:ℝ)) :
    ∀k,vectorNorm (Primary.residual j J h l (flip x k))≤(2*ρ)*Real.sqrt (n:ℝ) ∧
      vectorNorm (Primary.residual j J h (l+1) (flip x k))≤(2*ρ)*Real.sqrt (n:ℝ) := by
  obtain ⟨h0,h1⟩:=residualCutoff_support hn hρ J h l x hcut
  intro k
  exact ⟨vector_flip_buffer _ x hD₀ hsmall h0 k,vector_flip_buffer _ x hD₁ hsmall h1 k⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma auxiliary_derivative (j q : ℝ) (b : Spin n→ℝ) (x : Spin n) :
    derivativeVector (fun y=>j*(1-b y-q)) x= -j • derivativeVector b x := by
  ext i
  simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,halfDiff]
  ring

lemma primary_literal_derivative_diagnostics (hn : 0<n) {j K B : ℝ}
    (hK : 0≤K) (hB : 0≤B) (J : Interaction n) (h : Fin n→ℝ)
    (hop : SKGap.opNorm J≤K) (k : ℕ)
    (hformal : ∀x l,l<k+3→ShapeBound (formalField j J h x l) B)
    (r : Fin n→ℝ) (x : Spin n) :
    let C:=localPrimaryBudget j K B (k+3)
    let T:=(1+|j|)*C
    let a:=fun v=>j*(1-Primary.onsager j J h (k+1) v-SKGap.overlap r)
    SKGap.opNorm (derivativeMatrix (fld j J h (k+1)) x)+‖derivativeVector a x‖≤T ∧
    SKGap.opNorm (derivativeMatrix (mag j J h (k+1)) x)≤T ∧
    ‖derivativeMatrix (fld j J h (k+1)) x-(primaryTree j J h x (k+1)).fieldMatrix j J‖≤C ∧
    ‖derivativeMatrix (mag j J h (k+1)) x-(primaryTree j J h x (k+1)).sourceMatrix j J‖≤C ∧
    (∑i,∑v,(derivativeMatrix (fld j J h (k+1)) x i v)^4)≤(2*C)^4 ∧
    (∑i,(derivativeMatrix (fld j J h (k+1)) x i i)^2)≤T^2 := by
  dsimp only
  let C:=localPrimaryBudget j K B (k+3)
  have hC : 0≤C:=localPrimaryBudget_nonneg hK hB _
  have hT : C≤(1+|j|)*C := by nlinarith [abs_nonneg j]
  have hh:=primary_differentiation J h x hn hK hB hop (k+1)
    (fun l hl=>hformal x l (by omega))
  have hb:=(localPrimaryBudget_bounds (j:=j) hK hB (k+3) ⟨k+1,by omega⟩).1
  have hz : ShapeBound (derivativeMatrix (fld j J h (k+1)) x) C := hh.2.2.2.mono hb
  have ha := onsager_derivative_bound (j:=j) J h x hn hK hB hop (k+3)
    (hformal x) (show k+1≤k+3 by omega)
  refine ⟨?_,(hh.2.2.1.trans hb).trans hT,?_,?_,?_,?_⟩
  · rw [auxiliary_derivative,norm_smul,Real.norm_eq_abs,abs_neg]
    exact (add_le_add hz.1 (mul_le_mul_of_nonneg_left ha (abs_nonneg j))).trans_eq (by dsimp [C];ring)
  · rw [(primaryTree_matrices j J h x (k+1)).2]
    exact hh.1.trans hb
  · rw [(primaryTree_matrices j J h x (k+1)).1]
    exact hh.2.1.trans hb
  · exact (fourth_sum_le hC hz).trans (by nlinarith [pow_nonneg hC 4])
  · have H:=pow_le_pow_left₀ (norm_nonneg _) (hz.2.1.trans hT) 2
    change (SKGap.diagonalSeminorm (derivativeMatrix (fld j J h (k+1)) x))^2≤((1+|j|)*C)^2 at H
    simpa only [SKGap.diagonalSeminorm_sq] using H

end SKGapCutoff.Recipe

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein

theorem stable_selected_initial_diagnostics {j K B A ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤A) (hc : 0<c)
    (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hbuffer : (K+4*j)*(2*ρ)<r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃V≥0,∃S≥0,∃F≥0,∀n : ℕ,0<n→∀(J : Interaction n) (h : Fin n→ℝ),
      J.IsSymm→SKGap.opNorm J≤K→¬SKGap.rootBad j A ε c r₀ J h→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→
      2*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n:ℝ)→
      ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀v,SKGap.tapField j J h v=0→v=r) ∧
      ∀e:Fin n→ℝ,vectorNorm e≤1→∃w y : VectorFields n,∃c₀:Spin n→ℝ,
        ∀x:Spin n,residualCutoff ρ j J h k x≠0→
          let a:=fun v=>j*(1-Primary.onsager j J h (k+1) v-SKGap.overlap r)
          LiteralEquations J j f (fld j J h (k+1)) (mag j J h (k+1)) w y a c₀ r e x ∧
          LiteralInitialDiagnostics
            (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h (k+1)) (mag j J h (k+1)) a c₀ r e)
            w y (primaryTree j J h x (k+1)) x V S F (Real.exp (R/2)) := by
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  let C:=localPrimaryBudget j K B (k+3)
  let T:=(1+|j|)*C
  have hη : 0≤η:=by dsimp [η];positivity
  have hC : 0≤C:=localPrimaryBudget_nonneg hK hB _
  have hT : 0≤T:=by dsimp [T];positivity
  obtain ⟨V,hV,S,hS,F,hF,hdiag⟩:=literal_initial_diagnostics j R η c T K (2*C) C f hj hc hη hT
    (mul_nonneg (by norm_num) hC) himplicit
  refine ⟨V,hV,S,hS,F,hF,?_⟩
  intro n hn J h hJ hop hbad hformal hdim
  have hact : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v := fun v=>
    (vectorNorm_matrix_mul J v).trans (mul_le_mul_of_nonneg_right hop (vectorNorm_nonneg v))
  obtain ⟨r,hr,hu,hstable⟩:=stable_primary_buffer hn hj hK hA hc hr₀
    (mul_nonneg (by norm_num) hρ.le) hε hAR hbuffer hR hsmall J hJ h hact hbad
  refine ⟨r,hr,hu,?_⟩
  intro e he
  let a:Spin n→ℝ:=fun v=>j*(1-Primary.onsager j J h (k+1) v-SKGap.overlap r)
  obtain ⟨w,y,c₀,heq,hd⟩:=hdiag n hn J (fld j J h (k+1)) (mag j J h (k+1)) a r e hJ hop he
  refine ⟨w,y,c₀,?_⟩
  intro x hcut
  have hD₀ : SKGap.opNorm (derivativeMatrix (Primary.residual j J h k) x)≤
      residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1) :=
    (residual_derivative_bound hn hK hB J h hop k
      (fun v l hl=>hformal v l (by omega)) x).trans
      (le_add_of_nonneg_right (residualDerivativeBudget_nonneg hK hB _))
  have hD₁ : SKGap.opNorm (derivativeMatrix (Primary.residual j J h (k+1)) x)≤
      residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1) :=
    (residual_derivative_bound hn hK hB J h hop (k+1)
      (fun v l hl=>hformal v l (by omega)) x).trans
      (le_add_of_nonneg_left (residualDerivativeBudget_nonneg hK hB _))
  have hf:=residualCutoff_flip_buffer hn hρ J h k x hcut hD₀ hD₁ hdim
  obtain ⟨h0,h1⟩:=residualCutoff_support hn hρ J h k x hcut
  have hρ2 : ρ*Real.sqrt (n:ℝ)≤(2*ρ)*Real.sqrt (n:ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  have H:=hstable k x (h0.trans hρ2) (h1.trans hρ2)
  have Hf (v:Fin n):=hstable k (flip x v) (hf v).1 (hf v).2
  have hb:=primary_literal_derivative_diagnostics hn hK hB J h hop k hformal r x
  change LiteralEquations J j f (fld j J h (k+1)) (mag j J h (k+1)) w y a c₀ r e x ∧ _
  exact ⟨heq x H,hd x (primaryTree j J h x (k+1)) H Hf hb.1 hb.2.1
    (primaryState_mag_bounded j J h (k+1) x) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2⟩

end SKGapCutoff.Recipe

end
end
end

end OAI
