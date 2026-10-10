import Mathlib
import OAI.Probability.SKGap.Terminal.StableLiteralTerminal
import OAI.Probability.SKGap.Localization.LocalFixedRecipe

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u
theorem stable_literal_comparison_targets {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        ((∀p≤k+1,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*y b x i) ∧
        LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)/Real.sqrt (n b:ℝ))) ∧
        LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) (k+1) x i) (r b i)
          (j*(1-onsager j (J b) (h b) (k+1) x-SKGap.overlap (r b))))) ∧
        LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) (k+1) x) ∧
        LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) ∧
        LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
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
  apply literal_local_weak_comparison_targets j J h ⟨k+1,by omega⟩ f a c r e w y E hn he
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
open Primary Static SKGap.Stein
universe u
theorem stable_literal_comparison_weak {j K B R ρ δ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (k : ℕ) (f : KernelExpr) :
    ∃A≥1,∀W C : ℝ,0≤W→0≤C→∀(Ω : Type u) (n : Ω→ℕ)
      (J : ∀b,Interaction (n b)) (h r e : ∀b,Fin (n b)→ℝ)
      (E : ∀b,Set (Spin (n b))) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (δ/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→
        LiteralStableAt (J b) j (fld j (J b) (h b) (k+1)) (mag j (J b) (h b) (k+1))
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b) R ρ δ x)→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃w y : ∀b,VectorFields (n b),∃c : ∀b,Observables (n b),
        (∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) (k+1))
          (mag j (J b) (h b) (k+1)) (w b) (y b)
          (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c b) (r b) (e b) x) ∧
        LocalUniformWeak E P (fun b=>literalTerminal j (J b) (h b) k (w b) (c b)) ∧
        LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) (k+1) x i*
          (Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i)))) := by
  obtain ⟨A,hA,hh⟩:=stable_literal_comparison_targets hj hK hB hδ hρ hsmall k f
  refine ⟨A,hA,?_⟩
  intro W C hW hC Ω n J h r e E P hn hJ he hevent hstable hP hp hm
  obtain ⟨w,y,c,heq,⟨hw,hy,hmag,hχ,ho,hc⟩,hrem⟩:=hh W C hW hC Ω n J h r e E P
    hn hJ he hevent hstable hP hp hm
  exact ⟨w,y,c,heq,literal_terminal_weak j J h r e k f
    (fun b v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) c w y E P hn hJ hP
    heq hw hy hmag hχ ho hc,hrem⟩

end SKGapCutoff.Recipe

end
end

end OAI
