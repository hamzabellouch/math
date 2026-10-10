import Mathlib
import OAI.Probability.SKGap.Localization.SelectionDeficit

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_root_posterior_direction {j K B Aroot ε c r₀ R ρ : ℝ}
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
    : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
      2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
      ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
      (h e : ∀b,Fin (n b)→ℝ),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
      (∀b,vectorNorm (e b)≤1)→
      (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      ∃r : ∀b,Fin (n b)→ℝ,(∀b,SKGap.tapField j (J b) (h b) (r b)=0 ∧
        ∀v,SKGap.tapField j (J b) (h b) v=0→v=r b) ∧
      UniformWeak (fun b=>fieldGibbs (J b) (h b))
        (fun b x=>∑i,(spin x i-Real.tanh (r b i))*e b i) := by
  classical
  choose A hA hs using fun k=>buffered_root_direction_weak.{u} hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit habsorb k
  refine ⟨A,hA,?_⟩
  intro m δ hδ hm hδm W C hW hC Ω n J h e hn hJ hdiag he hstarted hevent hbad hdim
  have hm0 : 0 < m := by
    by_contra hh
    have hz:m=0:=by omega
    subst m
    norm_num at hm
  have hd0 : 0<2*m-1:=by omega
  let P:=fun b=>fieldGibbs (J b) (h b)
  have hP : ∀b x,0≤P b x:=fun b x=>(fieldGibbs_pos _ _ _).le
  have hp : ∀b,∑x,P b x=1:=fun b=>sum_fieldGibbs _ _
  have hmean : ∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i :=
    fun b=>conditionalMean_primary j (J b) (hJ b) (hdiag b) (h b)
  obtain ⟨r,hr,D,hD,hdir⟩:=hs 0 W C hW hC Ω n J h e P hn hJ he
    (fun b=>hstarted b 0 hd0) hbad (fun b=>hdim b 0 hd0) hP hp hmean
  refine ⟨r,hr,?_⟩
  let F:=fun k b x=>∑i,(mag j (J b) (h b) (k+2) x i-Real.tanh (r b i))*e b i
  apply uniform_cutoff_partition (C:=fun k b=>residualCutoff ρ j (J b) (h b) k)
    (F:=F) (2*m-1) hP
  · intro k hk
    exact residualCutoff_uniform hρ hK hB hn (fun b=>(hevent b).1)
      (fun b x l hl=>(hevent b).2.1 (h b) x l hl) k (by omega)
  · intro k hk
    have hh:=(gibbs_constant_residuals (h:=h) (e:=e) (2*m) hK hB hW hC hn hJ hdiag hevent he (k+2) (by omega)).1
    apply hh.congr
    intro b x
    dsimp [F]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro k hk
    obtain ⟨r',hr',D',hD',hh⟩:=hs k W C hW hC Ω n J h e P hn hJ he
      (fun b=>hstarted b k hk) hbad (fun b=>hdim b k hk) hP hp hmean
    have heqr : r'=r:=funext fun b=>(hr b).2 (r' b) (hr' b).1
    rw [heqr] at hh
    refine ⟨D',hD',fun b G=>?_⟩
    have hh':=hh b G
    change |∑x,P b x*G x*(residualCutoff ρ j (J b) (h b) k x*F k b x)|≤_
    have heq : (∑x,P b x*G x*(residualCutoff ρ j (J b) (h b) k x*F k b x))=
        ∑x,P b x*(residualCutoff ρ j (J b) (h b) k x*G x)*
          (∑i,(Real.tanh (fld j (J b) (h b) (k+1) x i)-Real.tanh (r b i))*e b i) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [F,mag_succ]
      ring
    rwa [heq]
  · obtain ⟨Q,hQ,hq⟩:=gibbs_residual_selection_deficit (h:=h) m hρ hδ hm hδm hK hB hW hC hn hJ hdiag hevent
    exact ⟨Q,hQ,fun b G=>hq b (r b) (e b) (he b) G⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma posterior_vectorNorm_le_of_unit_dot {n : ℕ} (v : Fin n→ℝ) {B : ℝ} (hB : 0≤B)
    (h : ∀e : Fin n→ℝ,vectorNorm e≤1→|∑i,v i*e i|≤B) : vectorNorm v≤B := by
  by_cases hv:vectorNorm v=0
  · simpa [hv] using hB
  have hp:0<vectorNorm v:=lt_of_le_of_ne (vectorNorm_nonneg _) (Ne.symm hv)
  let e:=fun i=>(vectorNorm v)⁻¹*v i
  have he:vectorNorm e=1 := by
    change SKGap.vectorNorm (fun i=>(vectorNorm v)⁻¹*v i)=1
    rw [SKGap.vectorNorm_smul,abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ hv
  have hh:=h e he.le
  have hd:(∑i,v i*e i)=vectorNorm v := by
    calc
      _ = (vectorNorm v)⁻¹*(∑i,(v i)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl;intro i _;dsimp [e];ring
      _ = (vectorNorm v)⁻¹*(vectorNorm v)^2 := by rw [vectorNorm_sq]
      _ = _ := by field_simp
  simpa only [hd,abs_of_nonneg (vectorNorm_nonneg _)] using hh

def centeredSpinCovariance (P G : Observables n) : Fin n→ℝ :=
  fun i=>∑x,P x*(G x-∑y,P y*G y)*spin x i

lemma centeredSpinCovariance_eq (P G : Observables n) (i : Fin n) :
    centeredSpinCovariance P G i=(∑x,P x*G x*spin x i)-
      (∑x,P x*G x)*(∑x,P x*spin x i) := by
  dsimp [centeredSpinCovariance]
  rw [show (∑x,P x*G x)*(∑x,P x*spin x i)=
    ∑x,(∑y,P y*G y)*(P x*spin x i) by rw [Finset.mul_sum]]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma weak_direction_center (P G : Observables n) (hp : ∑x,P x=1)
    (r e : Fin n→ℝ) {D : ℝ}
    (hw : ∀U,|∑x,P x*U x*(∑i,(spin x i-Real.tanh (r i))*e i)|≤D*starNorm P U) :
    |∑i,centeredSpinCovariance P G i*e i|≤
      D*Real.sqrt ((∑x,P x*(G x-∑y,P y*G y)^2)+varianceEnergy P G) := by
  let U:=fun x=>G x-∑y,P y*G y
  have hzero : (∑x,P x*U x)=0 := by
    dsimp [U]
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hp,one_mul,sub_self]
  have he : varianceEnergy P U=varianceEnergy P G := by
    unfold varianceEnergy
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hd : halfDiff i U x=halfDiff i G x:=by dsimp [halfDiff,U];ring
    rw [hd]
  have hid : (∑x,P x*U x*(∑i,(spin x i-Real.tanh (r i))*e i))=
      ∑i,centeredSpinCovariance P G i*e i := by
    simp only [sub_mul,Finset.sum_sub_distrib,mul_sub]
    rw [←Finset.sum_mul,hzero,zero_mul,sub_zero]
    simp only [Finset.mul_sum,centeredSpinCovariance,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    dsimp [U]
    ring
  have hh:=hw U
  rw [hid] at hh
  simpa only [starNorm,starSquared,he,U] using hh

end SKGapCutoff.Static

end
end

end OAI
