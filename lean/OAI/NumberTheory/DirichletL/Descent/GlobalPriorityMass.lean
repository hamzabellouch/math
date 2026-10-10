import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityBranches
import OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassPrefactor

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseSecondPrincipalCaller InversePrincipalEnergy FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_weighted_branch (ε:ℝ)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(original:Finset (Source ι Jo))(extra:CubeCoordinates ι→Finset ι)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(w:Source ι Jo→ℂ)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀x∈original,‖w x‖≤1)→0≤B→
      ∀U:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→Source ι Jo→ℝ,
      (∀r core J,J∈slots.powerset→∀x∈original,0≤U r core J x)→
      (∀r core J,J∈slots.powerset→∀x∈original,U r core J x≤B)→
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,‖globalPriorityOuter p hg negative Ψ m r core w x‖*
          ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*U r core J x≤
      Cb*(4:ℝ)^slots.card*B*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  let Cr:ℝ:=Fintype.card (RayCharacter×RayCharacter)
  let Cc:ℝ:=Fintype.card FirstCoreIndex
  refine ⟨(32*512)*Cr*Cc*coefficientBound*Cm^2,by
    have hr:0<Cr:=by dsimp [Cr];exact_mod_cast Fintype.card_pos
    have hc:0<Cc:=by dsimp [Cc];exact_mod_cast Fintype.card_pos
    have:=coefficientBound_pos;positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop Jo original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB U hU0 hU
  let N:=fun x:Source ι Jo=>(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε)
  have hn(x:Source ι Jo):0≤N x:=Real.rpow_nonneg (primeProductNorm_pos p hp _).le _
  have hm(J:Finset σ)(hJ:J∈slots.powerset)(x:Source ι Jo):
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤Cm^2*N x:=by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (wholeExtractedSupport (fun x=>extra x.cube) negative x)
    have he:((primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^ε)^2=N x:=by
      dsimp [N]
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have hw'(r:RayCharacter×RayCharacter)(core:FirstCoreIndex)(x:Source ι Jo)(hx:x∈original):
      ‖globalPriorityOuter p hg negative Ψ m r core w x‖≤coefficientBound:=by
    rw [globalPriorityOuter,norm_mul]
    have ht:=priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) r core x.quotientSupport (by simp) (hΨ _)
    exact (mul_le_mul (hw x hx) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,coefficientBound*(Cm^2*N x)*B:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro core hc
      apply Finset.sum_le_sum
      intro J hJ
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul (mul_le_mul (hw' r core x hx) (hm J hJ x) (sq_nonneg _) coefficientBound_pos.le)
        (hU r core J hJ x hx) (hU0 r core J hJ x hx) (mul_nonneg coefficientBound_pos.le (mul_nonneg (sq_nonneg Cm) (hn x)))
    _= _:=by
      have hsum:(∑x∈original,coefficientBound*(Cm^2*N x)*B)=
          coefficientBound*Cm^2*B*∑x∈original,N x:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros;ring
      rw [hsum]
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [←he]
      dsimp only [Cr,Cc,N]
      ring
end SevenEighths.InverseMoment

end

end OAI
