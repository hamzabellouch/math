import OAI.NumberTheory.DirichletL.Moments.EligibleEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

lemma reciprocal_sums {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) :
    (∑a∈s.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
      (∑b∈v.active D,1/Real.sqrt (formalReductionFactor D b v.P))=
    ∑a∈s.active D,∑b∈v.active D,
      1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hf:0≤formalReductionFactor D a s.P:=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  rw [Real.sqrt_mul hf]
  ring

theorem actual_paired_source_shell {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  obtain ⟨C₁,hC₁,hl⟩:=actual_source_root_from_children (ι:=ι) N hι ε hε
  obtain ⟨C₂,hC₂,hr⟩:=actual_source_root_from_children (ι:=κ) N hκ ε hε
  obtain ⟨C₃,hC₃,hshell⟩:=paired_all_active_shell (ι:=ι) (κ:=κ) N hι hκ ε hε
  refine ⟨C₁*C₂*C₃,by positivity,?_⟩
  intro s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  let W:ℝ:=Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)
  let θ:ℝ:=(s.toSource.allowance Z+v.toSource.allowance Z)/2
  let F:Ideal O→ℝ:=fun D=>∑a∈s.toSource.active D,∑b∈v.toSource.active D,
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)
  have hW:0≤W:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hF (D:Ideal O):0≤F D:=Finset.sum_nonneg (fun a _=>Finset.sum_nonneg
    (fun b _=>div_nonneg zero_le_one (Real.sqrt_nonneg _)))
  have ht:0<T:=zero_lt_one.trans_le hT
  have hp (D:Ideal O) (hd:D∈Ds):Real.sqrt (s.energy D)*Real.sqrt (v.energy D)≤
      (C₁*C₂)*(2*T)^ε*W*F D:=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have hpow:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
    have hmul:=mul_le_mul (hl s D (hD D hd) E₁ hE₁ (hleft D hd))
      (hr v D (hD D hd) E₂ hE₂ (hright D hd)) (Real.sqrt_nonneg _) (by positivity)
    apply hmul.trans
    calc
      _=(C₁*C₂)*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)^2*W*
          ((∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
           (∑b∈v.toSource.active D,1/Real.sqrt (formalReductionFactor D b v.P))):=by dsimp [W];ring
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^ε*W*F D:=by
        rw [Real.sq_sqrt hpow,reciprocal_sums]
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le (hhi D hd).le hε.le) (by positivity)) hW) (hF D)
  calc
    _≤∑D∈Ds,(C₁*C₂)*(2*T)^ε*W*F D:=Finset.sum_le_sum hp
    _=((C₁*C₂)*(2*T)^ε*W)*(∑D∈Ds,F D):=(Finset.mul_sum ..).symm
    _≤((C₁*C₂)*(2*T)^ε*W)*(C₃*(2*T)^(2*ε)*Z^θ):=
      mul_le_mul_of_nonneg_left (hshell s.toSource v.toSource Ds hD T Z hT hZ hlo hhi) (by positivity)
    _=(C₁*C₂*C₃)*(2*T)^(3*ε)*Z^θ*W:=by
      have hpow:(2*T)^ε*(2*T)^(2*ε)=(2*T)^(3*ε):=by
        rw [←Real.rpow_add (by positivity:0<2*T)];congr 1;ring
      calc
        _=(C₁*C₂*C₃)*((2*T)^ε*(2*T)^(2*ε))*Z^θ*W:=by ring
        _=_:=by rw [hpow]

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI
