import Mathlib
import OAI.Probability.SKGap.Localization.LocalWeakBase
import OAI.Probability.SKGap.Localization.BufferedFlip

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
variable {n : ℕ}

lemma vector_flip_additive (F : VectorFields n) (x : Spin n) (k : Fin n) {B : ℝ}
    (hD : SKGap.opNorm (derivativeMatrix F x)≤B) :
    vectorNorm (F (flip x k))≤vectorNorm (F x)+2*B := by
  have H : vectorNorm (F (flip x k))≤vectorNorm (F x)+vectorNorm (F (flip x k)-F x) := by
    calc
      _ = vectorNorm (F x+(F (flip x k)-F x)) := by congr 1;ext i;simp
      _ ≤ _ := SKGap.vectorNorm_add_le _ _
  have H' := (vector_flip_opNorm F x k).trans
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ)≤2))
  linarith

lemma vector_neighborhood_twice_buffer (F : VectorFields n) (E : Set (Spin n))
    {B ρ : ℝ} (hB : 0≤B) (hD : ∀x,SKGap.opNorm (derivativeMatrix F x)≤B)
    (hsmall : 4*B≤ρ*Real.sqrt (n:ℝ))
    (hF : ∀x∈E,vectorNorm (F x)≤ρ*Real.sqrt (n:ℝ)) (x : Spin n)
    (hx : x∈flipNeighborhood E) :
    vectorNorm (F x)≤(2*ρ)*Real.sqrt (n:ℝ) ∧
      ∀k,vectorNorm (F (flip x k))≤(2*ρ)*Real.sqrt (n:ℝ) := by
  have hbase : vectorNorm (F x)≤ρ*Real.sqrt (n:ℝ)+2*B := by
    rcases hx with hx|⟨k,hk⟩
    · exact (hF x hx).trans (le_add_of_nonneg_right (by positivity))
    · have H:=vector_flip_additive F (flip x k) k (hD (flip x k))
      simp only [flip_flip] at H
      have H' := hF _ hk
      linarith
  refine ⟨by linarith,?_⟩
  intro k
  have H:=vector_flip_additive F x k (hD x)
  linarith

theorem buffered_selected_initial_diagnostics {j K B A ε c r₀ R ρ : ℝ}
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
      4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n:ℝ)→
      ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀v,SKGap.tapField j J h v=0→v=r) ∧
      ∀e:Fin n→ℝ,vectorNorm e≤1→∃w y : VectorFields n,∃c₀:Spin n→ℝ,
        ∀x:Spin n,x∈flipNeighborhood {v | residualCutoff ρ j J h k v≠0}→
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
  intro x hx
  let BB:=residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1)
  have hBB : 0≤BB:=add_nonneg (residualDerivativeBudget_nonneg hK hB _)
    (residualDerivativeBudget_nonneg hK hB _)
  have hD₀ (v : Spin n) : SKGap.opNorm (derivativeMatrix (Primary.residual j J h k) v)≤BB :=
    (residual_derivative_bound hn hK hB J h hop k
      (fun v l hl=>hformal v l (by omega)) v).trans
      (le_add_of_nonneg_right (residualDerivativeBudget_nonneg hK hB _))
  have hD₁ (v : Spin n) : SKGap.opNorm (derivativeMatrix (Primary.residual j J h (k+1)) v)≤BB :=
    (residual_derivative_bound hn hK hB J h hop (k+1)
      (fun v l hl=>hformal v l (by omega)) v).trans
      (le_add_of_nonneg_left (residualDerivativeBudget_nonneg hK hB _))
  have H0:=vector_neighborhood_twice_buffer (Primary.residual j J h k)
    {v | residualCutoff ρ j J h k v≠0} hBB hD₀ hdim
    (fun v hv=>(residualCutoff_support hn hρ J h k v hv).1) x hx
  have H1:=vector_neighborhood_twice_buffer (Primary.residual j J h (k+1))
    {v | residualCutoff ρ j J h k v≠0} hBB hD₁ hdim
    (fun v hv=>(residualCutoff_support hn hρ J h k v hv).2) x hx
  have H:=hstable k x H0.1 H1.1
  have Hf (v:Fin n):=hstable k (flip x v) (H0.2 v) (H1.2 v)
  have hb:=primary_literal_derivative_diagnostics hn hK hB J h hop k hformal r x
  change LiteralEquations J j f (fld j J h (k+1)) (mag j J h (k+1)) w y a c₀ r e x ∧ _
  exact ⟨heq x H,hd x (primaryTree j J h x (k+1)) H Hf hb.1 hb.2.1
    (primaryState_mag_bounded j J h (k+1) x) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def literalCoefficientBudget (f : KernelExpr) (j R B : ℝ) : ℝ :=
  1+|initialRegularBudget f j R B|+f.mass*Real.exp (R/2)+
    (1+|j| *|B|)*phiExpr.mass*Real.exp (R/2)

lemma literalInitial_coefficientClass (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |d*c x|≤B) (hcf : ∀k,|d*c (flip x k)|≤B) (N : ℕ) :
    (literalInitial J j d f z m a c r e).CoefficientClass N x
      (literalCoefficientBudget f j R B) := by
  let D:=literalInitial J j d f z m a c r e
  let K:=literalCoefficientBudget f j R B
  have hreg:=literalInitial_regular J j d f z m a c r e x hB ha haf hc hcf
  have h1 : 1≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R B)]
  have hR : initialRegularBudget f j R B≤K := by
    have h0:=le_abs_self (initialRegularBudget f j R B)
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith
  have hF : f.mass*Real.exp (R/2)≤K := by
    have h3 : 0≤(1+|j| *|B|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R B)]
  have hP : phiExpr.mass*Real.exp (R/2)≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤|j| *|B| *(phiExpr.mass*Real.exp (R/2)):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  have hJP : |j| *B*(phiExpr.mass*Real.exp (R/2))≤K := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K,literalCoefficientBudget];rw [abs_of_nonneg hB]
    nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  refine ⟨h1,?_,?_,?_,?_⟩
  · intro q hq b
    simpa only [D,literalInitial] using (hreg.1 b).mono hR
  · intro q hq b
    simpa only [D,literalInitial] using hreg.2.mono hR
  · intro q hq b i k t ht
    cases b
    · exact (initialKernel_segment_value f D.H D.θ x r R ha haf i k t ht).trans hF
    · change |(-j)*(_)*initialKernel phiExpr (r i) _|≤K
      rw [abs_mul,abs_mul,abs_neg]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left
        (parameter_segment_value D.H D.θ x true hc hcf i k t ht) (abs_nonneg _))
        (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf i k t ht)
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB)).trans hJP
  · intro q hq b i k t ht
    exact (initialKernel_segment_value phiExpr D.H D.θ x r R ha haf i k t ht).trans hP

lemma literalInitial_seed_bound (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (hn : 0<n) (he : vectorNorm e≤1) :
    (∑b,vectorNorm ((literalInitial J j (Real.sqrt (n:ℝ)) f z m a c r e).seed b))≤2 := by
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hb : vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))≤1 := by
    have hv:=vectorNorm_tanh r
    have hscale : (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))=
        (Real.sqrt (n:ℝ))⁻¹ • (fun i=>Real.tanh (r i)):=by ext i;simp [div_eq_mul_inv,mul_comm]
    rw [hscale,vectorNorm_smul,abs_of_nonneg (inv_nonneg.mpr hd.le)]
    calc
      _ ≤ (Real.sqrt (n:ℝ))⁻¹*Real.sqrt (n:ℝ) := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hd.le)
      _ = 1 := inv_mul_cancel₀ hd.ne'
  simp only [Fintype.sum_bool,literalInitial,Bool.false_eq_true,↓reduceIte]
  change vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt (n:ℝ))+vectorNorm e≤2
  linarith
end SKGapCutoff.Recipe

end
end

end OAI
