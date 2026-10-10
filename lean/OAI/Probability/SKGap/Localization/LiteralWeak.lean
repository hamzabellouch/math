import Mathlib
import OAI.Probability.SKGap.Localization.BufferedComparisonBound

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein
universe u
variable {n : ℕ}

def literalSourceBracket (j : ℝ) (J : Interaction n) (h r e : Fin n→ℝ)
    (k : ℕ) (f : KernelExpr) : Observables n := fun x=>
  ∑i,((fld j J h (k+1) x i-r i-j*(1-onsager j J h (k+1) x-SKGap.overlap r)*
    Real.tanh (fld j J h (k+1) x i))*f.eval (fld j J h (k+1) x i) (r i)
      (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i-
    j*(1-onsager j J h (k+1) x-SKGap.overlap r)*f.dz.eval (fld j J h (k+1) x i) (r i)
      (j*(1-onsager j J h (k+1) x-SKGap.overlap r))*e i)

def literalMiddle (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (w : VectorFields n) : Observables n := fun x=>
  j*(1-SKGap.overlap r-siteMean (fun v i=>phi (fld j J h (k+1) v i) (r i)
    (j*(1-onsager j J h (k+1) v-SKGap.overlap r))) x)*
    (∑i,(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))*w x i)

variable {Ω : Type u} {N : Ω→ℕ}
theorem literal_source_middle_weak (j : ℝ) (J : ∀b,Interaction (N b))
    (h r e : ∀b,Fin (N b)→ℝ) (k : ℕ) (f : KernelExpr)
    (w y : ∀b,VectorFields (N b)) (c : ∀b,Observables (N b))
    (E : ∀b,Set (Spin (N b))) (P : ∀b,Observables (N b))
    (hn : ∀b,0<N b) (hJ : ∀b,(J b).IsSymm)
    (hroot : ∀b,SKGap.tapField j (J b) (h b) (r b)=0)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b)
      (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x)
    (hT : LocalUniformWeak E P (fun b=>literalTerminal j (J b) (h b) k (w b) (c b)))
    (hR : LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
      (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))))) :
    LocalUniformWeak E P (fun b x=>literalSourceBracket j (J b) (h b) (r b) (e b) k f x+
      literalMiddle j (J b) (h b) (r b) k (w b) x) := by
  apply (hT.add hR).congr_on
  intro b x hx
  rw [literal_comparison_identity (hn b) j (J b) (hJ b) (h b) (r b) (e b) k f
    (w b) (y b) (c b) x (hroot b) (heq b x hx)]
  dsimp only [literalSourceBracket,literalMiddle]
  ring

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_source_weak {j K B Aroot ε c r₀ R ρ : ℝ}
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
          (fun b x=>literalSourceBracket j (J b) (h b) (r b) (e b) k f x+
            literalMiddle j (J b) (h b) (r b) k (w b) x) := by
  obtain ⟨A,hA',hh⟩:=buffered_root_comparison_weak hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  obtain ⟨r,hr,w,y,c₀,heq,hT,hrem⟩:=hh W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  exact ⟨r,hr,w,y,c₀,heq,literal_source_middle_weak j J h r e k f w y c₀ _ P hn hJ
    (fun b=>(hr b).1) heq hT hrem⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma tested_susceptibility_absorption (P C L M : Observables n)
    (hP : ∀x,0≤P x) {K D : ℝ} (hK : 0≤K) (hD : 0≤D)
    (hM : ∀x,C x≠0→|M x|≤|L x|/2)
    (hweak : |∑x,P x*((C x)^2*L x)*(L x+M x)|≤K*starNorm P (fun x=>(C x)^2*L x))
    (hstar : starSquared P (fun x=>(C x)^2*L x)≤(∑x,P x*(C x*L x)^2)+D) :
    (∑x,P x*(C x*L x)^2)≤4*K^2+D := by
  let S:=∑x,P x*(C x*L x)^2
  have hS : 0≤S := Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  have hsum : S/2≤∑x,P x*((C x)^2*L x)*(L x+M x) := by
    rw [show S/2=∑x,P x*(C x*L x)^2/2 by simp only [S,Finset.sum_div]]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx:C x=0
    · simp [hx]
    have habs : |L x*M x|≤(L x)^2/2 := by
      rw [abs_mul]
      have H:=mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg (L x))
      simpa only [←mul_div_assoc,←sq,sq_abs] using H
    have hh := (neg_abs_le (L x*M x)).trans' (neg_le_neg habs)
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (hP x) (sq_nonneg (C x)))
    nlinarith only [hh']
  have htest : S/2≤K*Real.sqrt (S+D) :=
    (hsum.trans (le_abs_self _)).trans (hweak.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstar) hK))
  have hsqrt : (Real.sqrt (S+D))^2=S+D := Real.sq_sqrt (add_nonneg hS hD)
  have H:=sq_nonneg (Real.sqrt (S+D)-2*K)
  change S≤4*K^2+D
  nlinarith only [htest,H,hsqrt]

end SKGapCutoff.Static

end
end

end OAI
