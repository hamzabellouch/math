import OAI.NumberTheory.DirichletL.Descent.WholePriorityBranches

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O"=>ActualEisensteinCubic.O

theorem whole_priority_weighted_branch (ε:ℝ) (hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → 0≤B →
      ∀U:(RayCharacter×RayCharacter)→Finset ι→FirstCoreIndex→Finset σ→ℝ,
      (∀r D core J,J∈slots.powerset → 0≤U r D core J) →
      (∀r D core J,J∈slots.powerset → U r D core J≤B) →
      (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative Ψ m D core‖*
          ∑J∈slots.powerset,‖primeMark J lists a
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*U r D core J ≤
      Cb*(4:ℝ)^slots.card*B*
        (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  refine ⟨((32*512:ℝ)^2*512)*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hcop pool b C extra negative Ψ m slots lists a selector B hslots ha hΨ hB U hU0 hU
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hU r D core J hJ) (hU0 r D core J hJ) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hB))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*B*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [A]
      ring

end SevenEighths.InverseMoment

end

end OAI
