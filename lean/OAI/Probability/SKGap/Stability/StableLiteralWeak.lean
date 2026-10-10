import Mathlib
import OAI.Probability.SKGap.Localization.LiteralLocalWeak

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

lemma LiteralInitialDiagnostics.monoCoefficient {n : ℕ}
    {D : OrdinaryData n Unit Bool Bool} {w y : VectorFields n}
    {t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)} {x : Spin n} {V S F A A' : ℝ}
    (H : LiteralInitialDiagnostics D w y t x V S F A) (hA : A≤A') :
    LiteralInitialDiagnostics D w y t x V S F A' :=
  {H with coefficient_bound:=fun i=>(H.coefficient_bound i).trans hA}

lemma literalResidualBudget_exp (j : ℝ) (f : KernelExpr) (R B : ℝ) (p : ℕ) :
    Real.exp (R/2)≤literalResidualBudget j f R B p := by
  have h0:=le_abs_self (literalCoefficientBudget f j R B)
  have hF : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
  have hJ : 0≤|j| *|B| *Real.exp (R/2):=by positivity
  have hh : Real.exp (R/2)≤literalCoefficientBudget f j R B := by
    simp only [literalCoefficientBudget,phiExpr,KernelExpr.mass]
    nlinarith [abs_nonneg (initialRegularBudget f j R B)]
  exact (show Real.exp (R/2)≤2+|literalCoefficientBudget f j R B| by linarith).trans
    (residualCoefficientBudget_ge j (by positivity) p 0)

theorem stable_literal_local_weak {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (1+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*w b x i) := by
  let Cp:=localPrimaryBudget j K B (k+3)
  let T:=(1+|j|)*Cp
  have hCp : 0≤Cp:=localPrimaryBudget_nonneg hK hB _
  have hT : 0≤T:=by dsimp [T];positivity
  obtain ⟨V,hV,S,hS,F,hF,Bc,hBc,Vc,hVc,hsol⟩:=
    literal_complete_diagnostics j R ρ δ T K (2*Cp) Cp f hj hδ hρ hT
      (mul_nonneg (by norm_num) hCp) hsmall
  let A:=literalResidualBudget j f R Bc (k+1)
  have hA : 1≤A:=
    (show 1≤2+|literalCoefficientBudget f j R Bc| by linarith [abs_nonneg (literalCoefficientBudget f j R Bc)]).trans
      (residualCoefficientBudget_ge j (by positivity) (k+1) 0)
  refine ⟨A,hA,?_⟩
  intro W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  let a:=fun b v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))
  choose w y c heq hc hDc hdiag using fun b=>hsol (n b) (hn b) (J b)
    (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1)) (a b) (r b) (e b)
    (hJ b) (hevent b).1 (he b)
  have hs (b) (x : Spin (n b)) (hx : x∈flipNeighborhood (E b)) :=
    hstable b x (Or.inl hx)
  have hsf (b) (x : Spin (n b)) (hx : x∈flipNeighborhood (E b)) (i : Fin (n b)) :=
    hstable b (flip x i) (Or.inr ⟨i,by simpa only [flip_flip] using hx⟩)
  have hb (b) (x : Spin (n b)):=primary_literal_derivative_diagnostics (hn b) hK hB (J b) (h b)
    (hevent b).1 k (fun v q hq=>(hevent b).2.1 (h b) v q hq) (r b) x
  have heqE : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b) (a b) (c b) (r b) (e b) x := by
    intro b x hx;exact heq b x (hs b x (Or.inl hx))
  refine ⟨w,y,c,heqE,?_⟩
  apply literal_local_weak_residual j J h ⟨k+1,by omega⟩ f a c r e w y E hn he
    hK hB hBc hT hVc hV hS hF hW hC
    (fun b=>(hevent b).1) (fun b x q hq=>(hevent b).2.1 (h b) x q hq)
  · intro b x hx;exact (hstable b x hx).a_bound
  · intro b x hx;exact hc b x (hstable b x hx)
  · intro b x hx
    have hh:=(hb b x).1
    exact (le_add_of_nonneg_left (show 0≤SKGap.opNorm (derivativeMatrix (fld j (J b) (h b) (k+1)) x) from norm_nonneg _)).trans hh
  · intro b x hx;exact hDc b x (hs b x hx) (hsf b x hx) (hb b x).1 (hb b x).2.1
  · exact heqE
  · intro b x hx
    exact (hdiag b x (primaryTree j (J b) (h b) x (k+1)) (hs b x hx) (hsf b x hx)
      (hb b x).1 (hb b x).2.1 (primaryState_mag_bounded j (J b) (h b) (k+1) x)
      (hb b x).2.2.1 (hb b x).2.2.2.1 (hb b x).2.2.2.2.1 (hb b x).2.2.2.2.2).monoCoefficient
        (literalResidualBudget_exp j f R Bc (k+1))
  · exact hP
  · exact hp
  · exact hm
  · exact hJ
  · intro b x hx
    exact (literal_closed_word_event (J b) j _ _ (a b) (r b) x (hn b) hj hδ hρ hsmall
      (hs b x hx) (hevent b)).1
  · intro b x hx
    exact (literal_closed_word_event (J b) j _ _ (a b) (r b) x (hn b) hj hδ hρ hsmall
      (hs b x hx) (hevent b)).2

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_literal_weak {j K B Aroot ε c r₀ R ρ : ℝ}
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
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (1+2*(k+1)) (J b))→
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
          (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*w b x i) := by
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A,hA',hh⟩:=stable_literal_local_weak hj hK hB hc hη himplicit k f
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

end OAI
