import Mathlib
import OAI.Probability.SKGap.Localization.SusceptibilityTest
import OAI.Probability.SKGap.Localization.LiteralWeak

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma literal_source_phi (j : ℝ) (J : Interaction n) (h r e : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    literalSourceBracket j J h r e k (KernelExpr.atom 0 0 false) x=
      ∑i,(Real.tanh (fld j J h (k+1) x i)-Real.tanh (r i))*e i := by
  simp only [literalSourceBracket,←phiZ_kernel,KernelExpr.eval,moment_base]
  have hh:=implicit_phi_source (fld j J h (k+1) x) r
    (j*(1-onsager j J h (k+1) x-SKGap.overlap r)) e
  simpa only [mul_assoc] using hh

lemma literal_source_phiR (hn : 0<n) (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    literalSourceBracket j J h r (fun _=>1/Real.sqrt (n:ℝ)) k
      (KernelExpr.dr (KernelExpr.atom 0 0 false)) x =
    literalSusceptibility (fld j J h (k+1))
      (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r x := by
  have hh:=implicit_phiR_source (fld j J h (k+1) x) r
    (j*(1-onsager j J h (k+1) x-SKGap.overlap r))
  have hh' : literalSourceBracket j J h r (fun _=>1/Real.sqrt (n:ℝ)) k
      (KernelExpr.dr (KernelExpr.atom 0 0 false)) x=
      (∑i,(phi (fld j J h (k+1) x i) (r i)
        (j*(1-onsager j J h (k+1) x-SKGap.overlap r))-SKGapCutoff.scalarVariance (r i)))/Real.sqrt (n:ℝ) := by
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [literalSourceBracket,phiR,phiRZ]
    ring
  rw [hh']
  have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  have hs0 : Real.sqrt (n:ℝ)≠0:=ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hs : (Real.sqrt (n:ℝ))^2=(n:ℝ):=Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [literalSusceptibility,siteMean,SKGap.overlap,SKGap.magnetization,
    SKGapCutoff.scalarVariance,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp
  rw [hs]
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

theorem buffered_root_susceptibility_bound {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0<c)
    (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ)<r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (habsorb : (|j| *|literalSizeBudget j c R K
        (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
      ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2)
    (k : ℕ) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃D≥0,∀b,
        ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*
          literalSusceptibility (fld j (J b) (h b) (k+1))
            (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) x)^2≤D := by
  let f:=KernelExpr.dr (KernelExpr.atom 0 0 false)
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A,hA',hh⟩:=buffered_root_source_weak hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit k f
  refine ⟨A,hA',?_⟩
  intro W C hW hC Ω n J h P hn hJ hevent hbad hdim hP hp hm
  let e:=fun b=>fun _ : Fin (n b)=>1/Real.sqrt (n b:ℝ)
  have he : ∀b,vectorNorm (e b)≤1 := by
    intro b
    dsimp [e]
    rw [vectorNorm_const,abs_of_nonneg (by positivity)]
    have hs : Real.sqrt (n b:ℝ)≠0:=ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn b)))
    exact le_of_eq (by field_simp)
  obtain ⟨r,hr,w,y,c₀,heq,hweak⟩:=hh W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  let E:=fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}
  let L:=fun b=>literalSusceptibility (fld j (J b) (h b) (k+1))
    (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b)
  let M:=fun b=>literalMiddle j (J b) (h b) (r b) k (w b)
  have hstable : ∀b x,x∈E b→
      LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
        (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R η c x := by
    intro b x hx
    have hact (v : Fin (n b)→ℝ) : vectorNorm ((J b).mulVec v)≤K*vectorNorm v :=
      (vectorNorm_matrix_mul _ v).trans (mul_le_mul_of_nonneg_right (hevent b).1 (vectorNorm_nonneg v))
    obtain ⟨r',hr',hu',hs⟩:=stable_primary_buffer (hn b) hj hK hA hc hr₀
      (mul_nonneg (by norm_num) hρ.le) hε hAR hbuffer hR hsmall (J b) (hJ b) (h b) hact (hbad b)
    have heqroot : r'=r b:=(hr b).2 r' hr'
    rw [heqroot] at hs
    obtain ⟨h0,h1⟩:=residualCutoff_support (hn b) hρ (J b) (h b) k x hx
    have hρ2 : ρ*Real.sqrt (n b:ℝ)≤(2*ρ)*Real.sqrt (n b:ℝ) := by nlinarith [mul_nonneg hρ.le (Real.sqrt_nonneg (n b:ℝ))]
    exact hs k x (h0.trans hρ2) (h1.trans hρ2)
  have hmiddle : ∀b x,x∈E b→|M b x|≤|L b x|/2 := by
    intro b x hx
    have H:=literal_middle_error (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b)
      (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c₀ b) (r b) (e b) x
      (hn b) hc hη himplicit (hevent b).1 (he b) (hstable b x hx) (heq b x hx)
    change |M b x|≤(|j| *|literalSizeBudget j c R K f|)*η*|L b x| at H
    have H':=(mul_le_mul_of_nonneg_right habsorb (abs_nonneg (L b x)))
    exact H.trans (H'.trans_eq (by ring))
  have hweakL : LocalUniformWeak E P (fun b x=>L b x+M b x) := by
    apply hweak.congr
    intro b x
    rw [literal_source_phiR (hn b)]
  obtain ⟨D,hD,hstar⟩:=literalSusceptibility_cutoff_test j K B ρ hK hB hρ k
  obtain ⟨Q,hQ,hQbound⟩:=hweakL
  refine ⟨r,hr,4*Q^2+D,by positivity,?_⟩
  intro b
  apply tested_susceptibility_absorption (P b) (residualCutoff ρ j (J b) (h b) k) (L b) (M b)
    (hP b) hQ hD (hmiddle b)
  · apply hQbound b
    intro x hx
    have hc0 : residualCutoff ρ j (J b) (h b) k x=0 := by simpa only [E,Set.mem_ofPred_eq,not_not] using hx
    simp [hc0]
  · exact hstar (n b) (hn b) (J b) (h b) (r b) (P b) (hP b) (hp b)
      (hevent b).1 (fun x l hl=>(hevent b).2.1 (h b) x l hl)

end SKGapCutoff.Recipe

end
end

end OAI
