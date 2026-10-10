import OAI.NumberTheory.DirichletL.Moments.PairedEligibleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def Bound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂))

theorem uniform_subset_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,Bound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ Bound p.1 p.2 C ε:=
    actual_paired_source_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by linarith) _)) (by positivity))

theorem actual_source_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Data J) (v:Data L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀E₁ E₂ T Z:ℝ,
      0≤E₁ → 0≤E₂ → 1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*Z^δ*(Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  let ε:ℝ:=δ/(3*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:3*B*ε≤δ:=by
    have hh:ε*(3*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=uniform_subset_energy (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(3*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hTZ hlo hhi hleft hright
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hs:=subset_allowance J s.toSource lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v.toSource lo hi hvlo hvhi Z hZ
  have hnum:Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)≤E:=by
    dsimp [E]
    rw [←numerical_allowance Z _ hZ]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hh:=hbound J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans
  rw [Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le]
  have hp:T^(3*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  calc
    C*(2^(3*ε)*T^(3*ε))*E=(C*2^(3*ε)*E)*T^(3*ε):=by ring
    _≤(C*2^(3*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hp (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformEligibleEnergy

end

end OAI
