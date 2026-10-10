import Mathlib
import OAI.Probability.SKGap.Localization.LiteralValues

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
variable {n : ℕ}

lemma tested_l2_to_star (P G H : Observables n) (hP : ∀x,0≤P x)
    {D : ℝ} (hD : 0≤D) (hH : (∑x,P x*(H x)^2)≤D) :
    |∑x,P x*G x*H x|≤Real.sqrt D*starNorm P G := by
  have hG : 0≤∑x,P x*(G x)^2:=Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _)
  have hS : (∑x,P x*(G x)^2)≤ starSquared P G :=
    le_add_of_nonneg_right (varianceEnergy_nonneg P hP G)
  have H':=(weighted_cauchy_sq P G H hP).trans
    (mul_le_mul hS hH (Finset.sum_nonneg fun x _=>mul_nonneg (hP x) (sq_nonneg _))
      (starSquared_nonneg P hP G))
  have H'' := Real.sqrt_le_sqrt H'
  rw [Real.sqrt_sq_eq_abs,mul_comm (starSquared P G) D,Real.sqrt_mul hD] at H''
  exact H''

lemma local_source_extract (P C F M G : Observables n) (hP : ∀x,0≤P x)
    {Q L D : ℝ} (hQ : 0≤Q) (hL : 0≤L) (hD : 0≤D)
    (hC : ∀x,|C x|≤1) (hdC : ∀x,∑i,(halfDiff i C x)^2≤L^2)
    (hM : (∑x,P x*(C x*M x)^2)≤D)
    (hw : ∀U,(∀x,C x=0→U x=0)→
      |∑x,P x*U x*(F x+M x)|≤Q*starNorm P U) :
    |∑x,P x*(C x*G x)*F x|≤(Q*Real.sqrt (3+2*L^2)+Real.sqrt D)*starNorm P G := by
  have hh:=hw (fun x=>C x*G x) (by intro x hx;simp [hx])
  have hc:=star_multiplier P hP C G (by norm_num : (0:ℝ)≤1) hL hC hdC
  norm_num only [one_pow,mul_one] at hc
  have hm:=tested_l2_to_star P G (fun x=>C x*M x) hP hD hM
  have he : (∑x,P x*(C x*G x)*F x)=
      (∑x,P x*(C x*G x)*(F x+M x))-(∑x,P x*G x*(C x*M x)) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro x _;ring
  rw [he]
  exact ((abs_sub _ _).trans (add_le_add
    (hh.trans (mul_le_mul_of_nonneg_left hc hQ)) hm)).trans_eq (by ring)

end SKGapCutoff.Static

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

lemma StartedMatrixEvent.mono_budget {j R A₀ A A' c B W C : ℝ} {M N : ℕ}
    {J : Interaction n} (H : StartedMatrixEvent j R A₀ A c B W C M N J) (hA : A'≤A) :
    StartedMatrixEvent j R A₀ A' c B W C M N J := by
  refine ⟨H.1,H.2.1,?_⟩
  intro a ha hc
  have h:=(H.2.2 a ha hc)
  have hb : ∀w : List (SKGap.WordLetter (Fin n)),closedWordBounded A' w→closedWordBounded A w := by
    intro w hw l hl
    have hh:=hw l hl
    cases l with
    | diag p=>exact fun i=>(hh i).trans hA
    | noise=>trivial
    | inverse=>trivial
  exact ⟨fun w hw hi hwa=>h.1 w hw hi (hb w hwa),fun w hw hi hwa=>h.2 w hw hi (hb w hwa)⟩

lemma residualCutoff_uniform_gradient (j K B ρ : ℝ) (hK : 0≤K) (hB : 0≤B)
    (hρ : 0<ρ) (k : ℕ) :
    ∃L≥0,∀n:ℕ,0<n→∀(J:Interaction n) (h:Fin n→ℝ),SKGap.opNorm J≤K→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→
      ∀x,∑i,(halfDiff i (residualCutoff ρ j J h k) x)^2≤L^2 := by
  obtain ⟨Q,hQ⟩:=residualScalarCutoff_lipschitz
  let U:=residualDerivativeBudget j K B k
  let V:=residualDerivativeBudget j K B (k+1)
  let A:=2*(Q:ℝ)/ρ^2*((4*U+2*U^2)+(4*V+2*V^2))
  have hU : 0≤U:=residualDerivativeBudget_nonneg hK hB _
  have hV : 0≤V:=residualDerivativeBudget_nonneg hK hB _
  have hA : 0≤A:=by dsimp [A];positivity
  refine ⟨A,hA,?_⟩
  intro n hn J h hop hformal x
  have hd:=residualCutoff_gradient hn hρ hQ J h k x hU hV
    (residual_derivative_bound hn hK hB J h hop k (fun v l hl=>hformal v l (by omega)) x)
    (residual_derivative_bound hn hK hB J h hop (k+1) (fun v l hl=>hformal v l (by omega)) x)
  have hs : (1:ℝ)≤Real.sqrt (n:ℝ) := by
    rw [←Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have H:=hd.trans (div_le_self hA hs)
  simpa only [norm_derivativeVector_sq] using pow_le_pow_left₀ (norm_nonneg _) H 2

end SKGapCutoff.Recipe

end
end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_direction_weak {j K B Aroot ε c r₀ R ρ : ℝ}
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
      (J : ∀b,Interaction (n b)) (h e : ∀b,Fin (n b)→ℝ) (P : ∀b,Observables (n b)),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b,vectorNorm (e b)≤1)→
      (∀b,StartedMatrixEvent j K (Real.exp (R/2)) A (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b,4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      (∀b x,0≤P b x)→(∀b,∑x,P b x=1)→
      (∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
          ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      ∃D≥0,∀b (G : Observables (n b)),
        |∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*G x)*
          (∑i,(Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))*e b i)|≤D*starNorm (P b) G := by
  let f:=KernelExpr.atom 0 0 false
  let η:=(1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)
  have hη : 0≤η:=by dsimp [η];positivity
  obtain ⟨A₁,hA₁,hhs⟩:=buffered_root_susceptibility_bound hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit habsorb k
  obtain ⟨A₂,hA₂,hh⟩:=buffered_root_source_weak hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit k f
  refine ⟨max A₁ A₂,hA₁.trans (le_max_left _ _),?_⟩
  intro W C hW hC Ω n J h e P hn hJ he hevent hbad hdim hP hp hm
  have he₁:=fun b=>(hevent b).mono_budget (le_max_left A₁ A₂)
  have he₂:=fun b=>(hevent b).mono_budget (le_max_right A₁ A₂)
  obtain ⟨r₁,hr₁,D,hD,hL⟩:=hhs W C hW hC Ω n J h P hn hJ he₁ hbad hdim hP hp hm
  obtain ⟨r,hr,w,y,c₀,heq,hweak⟩:=hh W C hW hC Ω n J h e P hn hJ he he₂ hbad hdim hP hp hm
  have heqr : r₁=r:=funext fun b=>(hr b).2 (r₁ b) (hr₁ b).1
  rw [heqr] at hL
  let E:=fun b=>{x | residualCutoff ρ j (J b) (h b) k x≠0}
  let L:=fun b=>literalSusceptibility (fld j (J b) (h b) (k+1))
    (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (r b)
  let M:=fun b=>literalMiddle j (J b) (h b) (r b) k (w b)
  let F:=fun b x=>∑i,(Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))*e b i
  let S:=(|j| *|literalSizeBudget j c R K f|)*η
  have hS : 0≤S:=by dsimp [S];positivity
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
  have hmiddle : ∀b x,x∈E b→|M b x|≤S*|L b x| := by
    intro b x hx
    exact literal_middle_error (J b) j f (fld j (J b) (h b) (k+1))
      (mag j (J b) (h b) (k+1)) (w b) (y b)
      (fun v=>j*(1-onsager j (J b) (h b) (k+1) v-SKGap.overlap (r b))) (c₀ b) (r b) (e b) x
      (hn b) hc hη himplicit (hevent b).1 (he b) (hstable b x hx) (heq b x hx)
  have hM : ∀b,(∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*M b x)^2)≤S^2*D := by
    intro b
    calc
      _ ≤ S^2*(∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*L b x)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro x _
        by_cases hx:residualCutoff ρ j (J b) (h b) k x=0
        · simp [hx]
        have H:=hmiddle b x hx
        have H':=mul_le_mul_of_nonneg_left H (abs_nonneg (residualCutoff ρ j (J b) (h b) k x))
        have H'' : |residualCutoff ρ j (J b) (h b) k x*M b x|≤
            S*|residualCutoff ρ j (J b) (h b) k x*L b x| := by
          simpa only [abs_mul,mul_left_comm] using H'
        have H2:=pow_le_pow_left₀ (abs_nonneg _) H'' 2
        simp only [sq_abs,mul_pow] at H2
        have H3:=mul_le_mul_of_nonneg_left H2 (hP b x)
        nlinarith only [H3]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hL b) (sq_nonneg S)
  have hweakF : LocalUniformWeak E P (fun b x=>F b x+M b x) := by
    apply hweak.congr
    intro b x
    rw [literal_source_phi]
  obtain ⟨Q,hQ,hQbound⟩:=hweakF
  obtain ⟨T,hT,hd⟩:=residualCutoff_uniform_gradient j K B ρ hK hB hρ k
  refine ⟨r,hr,Q*Real.sqrt (3+2*T^2)+Real.sqrt (S^2*D),by positivity,?_⟩
  intro b G
  apply local_source_extract (P b) (residualCutoff ρ j (J b) (h b) k) (F b) (M b) G
    (hP b) hQ hT (mul_nonneg (sq_nonneg S) hD) _
    (hd (n b) (hn b) (J b) (h b) (hevent b).1 ((hevent b).2.1 (h b))) (hM b)
  · intro U hU
    apply hQbound b U
    intro x hx
    exact hU x (by simpa only [E,Set.mem_ofPred_eq,not_not] using hx)
  · intro x
    rw [abs_of_nonneg (residualCutoff_bounds ρ j (J b) (h b) k x).1]
    exact (residualCutoff_bounds ρ j (J b) (h b) k x).2

end SKGapCutoff.Recipe

end
end

end OAI
