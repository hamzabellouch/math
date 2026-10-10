import OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

theorem uniform_subset_shell {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,ShellBound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ ShellBound p.1 p.2 C ε:=
    paired_all_active_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD T Z hT hZ hlo hhi
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD T Z hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem paired_entrance_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L)
      (lo hi:ι→ℝ), (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((∑i,logWindow (lo i) (hi i))/Real.log Z) := by
  obtain ⟨C,hC,hbound⟩:=uniform_subset_shell (ι:=ι) ε hε
  refine ⟨C,hC,?_⟩
  intro J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  apply (hbound J L s v Ds hD T Z hT hZ hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hs:=subset_allowance J s lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v lo hi hvlo hvhi Z hZ
  linarith

theorem numerical_allowance (Z H:ℝ) (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

theorem paired_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤C*Z^δ := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:2*B*ε≤δ:=by
    have hh:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=paired_entrance_allowance (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD T Z hT hZ hTZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=hbound J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  rw [numerical_allowance Z _ hZ,Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le] at hh
  have hpow:T^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  apply hh.trans
  calc
    C*(2^(2*ε)*T^(2*ε))*E=(C*2^(2*ε)*E)*T^(2*ε):=by ring
    _≤(C*2^(2*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hpow (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI
