import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCutoff
import OAI.NumberTheory.DirichletL.Descent.FirstWholeTail

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_physical_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool S common divisor : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈S,0<v₁ i+v₂ i) → Disjoint pool S →
      ∀ (f : Ideal O),f≠0 → ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U∈pool.powerset,‖C₁ U‖≤G₁) → (∀ U∈pool.powerset,‖C₂ U‖≤G₂) →
      ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2 →
      (∀ N∈pool.powerset,C₁ N≠0 →
        ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta)) →
      (∀ Q∈pool.powerset,C₂ Q≠0 →
        ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta)) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common)
      let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂
        C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,hfull⟩ := full_first_supported_remainder order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hinj hcop hg hchar pool S common divisor v₁ v₂ ε₁ ε₂ hv hpool f hf0
    C₁ C₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ hC₁ hC₂ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂
    U₁ U₂ active slow T
  have hA (ε : ι→Bool) : 0<‖eisEmbedding (aLabel p S ε)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hU₁ : 0<U₁ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))
  have hU₂ : 0<U₂ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))
  have hlog₁ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₁ N≠0) : columnLog p 1 N≤Real.log U₁ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₁ N hN hn
  have hlog₂ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₂ N≠0) : columnLog p 1 N≤Real.log U₂ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₂ N hN hn
  have hb := hfull p hp hinj hcop hg hchar pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂ hpool C₁ C₂ W
    G₁ G₂ 1 1 (Z^M) (Z^tau) (Real.log U₁) (Real.log U₂) hG₁ hG₂ zero_lt_one zero_lt_one
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _).le hC₁ hC₂ hlog₁ hlog₂
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) (primeSubsetGenerator_ne_zero _ _) T
    (fun N hN Q hQ hNQ hn hq h hout=>by
      simpa only [primeSubsetGenerator_norm_eq_productNorm, Finset.union_comm] using
        first_physical_cutoff_raw_tail p hp S Q N v₁ v₂ ε₁ ε₂ hv hNQ.symm
          (hpool.mono_left (Finset.mem_powerset.mp hQ)) (hpool.mono_left (Finset.mem_powerset.mp hN))
          common divisor f hf0 h Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj
          (hcol₂ Q hQ hq) (hcol₁ N hN hn) hout)
  simpa only [Real.exp_log hU₁,Real.exp_log hU₂,one_mul,primeSubsetGenerator_norm_eq_productNorm]
    using hb

end
end SevenEighths.InverseMoment

end OAI
