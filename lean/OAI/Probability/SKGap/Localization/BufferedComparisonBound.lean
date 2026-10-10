import Mathlib
import OAI.Probability.SKGap.Stability.ImplicitComparison
import OAI.Probability.SKGap.Stability.StableLiteralComparison

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_comparison_weak {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0<c)
    (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ)<r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h e : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃w y : ∀b,VectorFields (n b),∃c₀ : ∀b,Observables (n b),
        (∀b x,residualCutoff ρ j (J b) (h b) k x≠0→
          LiteralEquations (J b) j f (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
            (w b) (y b) (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b)))
            (c₀ b) (r b) (e b) x) ∧
        LocalUniformWeak (fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}) P
          (fun b=>literalTerminal j (J b) (h b) k (w b) (c₀ b)) ∧
        LocalUniformWeak (fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}) P
          (fun b x=>j*c₀ b x*(∑i,residual j (J b) (h b) (k+1) x i*
            (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A,hA',hh⟩:=stable_literal_comparison_weak hj hK hB hc hη himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  have hact (b) (v : Fin (n b)→ℝ) : vectorNorm ((J b).mulVec v)≤K*vectorNorm v :=
    (vectorNorm_matrix_mul _ v).trans (mul_le_mul_of_nonneg_right (hevent b).1 (vectorNorm_nonneg v))
  choose r hr hu hs using fun b=>stable_primary_buffer (hn b) hj hK hA hc hr₀
    (mul_nonneg (by norm_num) hρ.le) hε hAR hbuffer hR hsmall (J b) (hJ b) (h b) (hact b) (hbad b)
  let E:=fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}
  have hstable : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
      LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
        (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R η c x := by
    intro b x hx
    let BB:=residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1)
    have hBB : 0≤BB:=add_nonneg (residualDerivativeBudget_nonneg hK hB _)
      (residualDerivativeBudget_nonneg hK hB _)
    have hD₀ (v : Spin (n b)) : SKGap.opNorm (derivativeMatrix (residual j (J b) (h b) k) v)≤BB :=
      (residual_derivative_bound (hn b) hK hB (J b) (h b) (hevent b).1 k
        (fun v l hl=>(hevent b).2.1 (h b) v l (by omega)) v).trans
        (le_add_of_nonneg_right (residualDerivativeBudget_nonneg hK hB _))
    have hD₁ (v : Spin (n b)) : SKGap.opNorm (derivativeMatrix (residual j (J b) (h b) (k+1)) v)≤BB :=
      (residual_derivative_bound (hn b) hK hB (J b) (h b) (hevent b).1 (k+1)
        (fun v l hl=>(hevent b).2.1 (h b) v l (by omega)) v).trans
        (le_add_of_nonneg_left (residualDerivativeBudget_nonneg hK hB _))
    have H0:=vector_neighborhood_twice_buffer (residual j (J b) (h b) k) (E b) hBB hD₀ (hdim b)
      (fun v hv=>(residualCutoff_support (hn b) hρ (J b) (h b) k v hv).1)
    have H1:=vector_neighborhood_twice_buffer (residual j (J b) (h b) (k+1)) (E b) hBB hD₁ (hdim b)
      (fun v hv=>(residualCutoff_support (hn b) hρ (J b) (h b) k v hv).2)
    rcases hx with hx|⟨i,hx⟩
    · exact hs b k x (H0 x hx).1 (H1 x hx).1
    · have h0:=(H0 (flip x i) hx).2 i
      have h1:=(H1 (flip x i) hx).2 i
      simp only [flip_flip] at h0 h1
      exact hs b k x h0 h1
  obtain ⟨w,y,c₀,heq,hw⟩:=hh W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  exact ⟨r,fun b=>⟨hr b,hu b⟩,w,y,c₀,heq,hw⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein Matrix
variable {n : ℕ}

 theorem literal_comparison_identity (hn : 0<n) (j : ℝ) (J : Interaction n)
    (hJ : J.IsSymm) (h r e : Fin n→ℝ) (k : ℕ) (f : KernelExpr)
    (w y : VectorFields n) (c : Observables n) (x : Spin n)
    (hr : SKGap.tapField j J h r=0)
    (heq : LiteralEquations J j f (fld j J h (k+1)) (mag j J h (k+1)) w y
      (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) c r e x) :
    literalTerminal j J h k w c x=
      (∑i,((fld j J h (k+1) x i-r i-
        j*(1-onsager j J h (k+1) x-SKGap.overlap r)*Real.tanh (fld j J h (k+1) x i))*
          f.eval (fld j J h (k+1) x i) (r i) (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i-
        j*(1-onsager j J h (k+1) x-SKGap.overlap r)*
          f.dz.eval (fld j J h (k+1) x i) (r i) (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i))+
      j*(1-SKGap.overlap r-siteMean (fun v i=>phi (fld j J h (k+1) v i) (r i)
        (j*(1-onsager j J h (k+1) v-SKGap.overlap r))) x)*
        (∑i,(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))*w x i)-
      j*c x*(∑i,residual j J h (k+1) x i*(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))) := by
  let z:=fld j J h (k+1)
  let m:=mag j J h (k+1)
  let a:=fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  have ht := (literalEquations_recipe J j 1 f z m w y a c r e one_ne_zero x).mp heq
  have hw := fun i=>congrFun ht.1 i
  simp only [literalInitial_source J j 1 f z m y a c r e one_ne_zero x] at hw
  have hy := ht.2.1.trans (literalInitial_field J j 1 f z m w y a c r e x ht.1 ht.2.2)
  have hc : (n:ℝ)*c x=∑i,(f.dz.eval (z x i) (r i) (a x)*e i+
      phiZ (z x i) (r i) (a x)*(y x i-j*c x*Real.tanh (r i))) := by
    calc
      _ = (n:ℝ)*siteMean ((literalInitial J j 1 f z m a c r e).implicitPartial y) x := by rw [←ht.2.2]
      _ = _ := ?_
    rw [siteMean,mul_div_cancel₀ _ hn0]
    apply Finset.sum_congr rfl
    intro i _
    exact literalInitial_partial J j 1 f z m y a c r e one_ne_zero x i
  have hroot (i) : r i-h i-J.mulVec (fun q=>Real.tanh (r q)) i+
      j*(1-SKGap.overlap r)*Real.tanh (r i)=0 := by
    have hh:=congrFun hr i
    simp only [SKGap.tapField,SKGap.onsager,SKGap.magnetization,Pi.zero_apply] at hh
    simpa only [mulVec,dotProduct] using (by linear_combination hh :
      r i-h i-(∑q,J i q*Real.tanh (r q))+j*(1-SKGap.overlap r)*Real.tanh (r i)=0)
  have hb : (∑i,(Real.tanh (z x i))^2)=(n:ℝ)*(1-onsager j J h (k+2) x) := by
    simp only [onsager,siteMean,mag_succ,z,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    field_simp
    ring
  have hq : (∑i,(Real.tanh (r i))^2)=(n:ℝ)*SKGap.overlap r := by
    simp only [SKGap.overlap,SKGap.magnetization,mul_div_cancel₀ _ hn0]
  have hh:=implicit_comparison J hJ (z x) r h (m x) (w x) (y x)
    (fun i=>f.eval (z x i) (r i) (a x)*e i)
    (fun i=>f.dz.eval (z x i) (r i) (a x)*e i)
    j (onsager j J h (k+2) x) (onsager j J h (k+1) x) (SKGap.overlap r)
    (siteMean (fun v i=>phi (z v i) (r i) (a v)) x) (c x)
    hroot hb hq hw (fun i=>congrFun hy i) hc
  have hmag : mag j J h (k+2) x=(fun i=>Real.tanh (z x i)):=funext fun i=>mag_succ ..
  simpa only [literalTerminal,Primary.residual,hmag,mag_succ,z,m,a,mul_assoc] using hh

end SKGapCutoff.Recipe

end
end

end OAI
