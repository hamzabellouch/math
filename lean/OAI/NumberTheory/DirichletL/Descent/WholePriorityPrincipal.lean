import OAI.NumberTheory.DirichletL.Descent.SecondVariablePrincipal
import OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority
import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityPrincipalEnergy
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
    (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (X t Y:ℝ)
    (R:Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        (let H:=firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) a)
          (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
         let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
         let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit)*∏i∈D,p i
         let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit
         ‖truncatedSecondZero p hg pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalCutoff p d (R D G E) G E)‖+
         ‖principalRestoration p hg hinj hp pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalMask p d (R D G E) G E)‖)

theorem whole_priority_principal_bound (ε:ℝ) (hε:0<ε) :
    ∃ (s:Finset (ℕ×ℕ)) (Cp:ℝ),0<Cp ∧
    ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (lo hi:ℝ)
      (_hlo:0<lo) (_hs:Function.support om⊆Set.Icc lo hi)
      (M t X Y:ℝ) (R:Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Y → (∀D G E,0≤R D G E) →
      wholePriorityPrincipalEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector om W X t Y R ≤
        Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
          Y*(X*Real.exp M)^(1+ε)*
          (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)) := by
  obtain ⟨s,Cp,hCp,hprinc⟩ := firstCore_variable_principal_energy ε hε
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨s,((32*512:ℝ)^2*512)*Cp*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop pool b C extra negative Ψ m d slots lists a selector om W lo hi hlo hs
    M t X Y R hslots ha hΨ hd hhi hX hY hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Y*(X*Real.exp M)^(1+ε)
  have hP:0≤P:=by dsimp [P];positivity
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
  unfold wholePriorityPrincipalEnergy
  dsimp only
  have hinner (r:RayCharacter×RayCharacter) (D:Finset ι) (core:FirstCoreIndex) (J:Finset σ)
      (hJ:J∈slots.powerset) := hprinc p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) a
    (residual_lists_pairwise slots J lists A D hslots) (residual_coeff_bound slots J lists a A D ha)
    pool D b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (fun i _=>residual_lists_avoid lists A D i) negative (if negative then r.1 else r.2) Ψ hΨ
    m (∏i∈C,p i) d hd core om W lo hi hlo hs M t X Y (R D) hhi hX hY (hR D)
  change _≤_
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hinner r D core J hJ) (by positivity) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hP))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

end SevenEighths.InverseMoment

end

end OAI
