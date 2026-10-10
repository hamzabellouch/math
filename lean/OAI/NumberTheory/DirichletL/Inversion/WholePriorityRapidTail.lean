import OAI.NumberTheory.DirichletL.Descent.SecondRapidTail
import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalTail
import OAI.NumberTheory.DirichletL.Descent.PrincipalSelectorMass

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRapidTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseMoment InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O

theorem marked_rapid_tail (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀u,‖Ψ u‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      ∀ (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (negative : Bool) (height X M Y Z : ℝ)
      (R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀G∈F.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (markedRadial p slots lists a ∅ (principalWindow om lo hi hlo hs negative height) X) W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_rapid_correlated_tail Lcap tau (saving+Lcap) hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound (1/2) (by norm_num)
  refine ⟨s,Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha
    om W lo hi hlo hs negative height X M Y Z R hX hhi hZ hY hL hy hyi hl hR
  let L:=X*Real.exp M
  have hLpos : 0<L := mul_pos hX (Real.exp_pos _)
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hv := principalWindow_upper om lo hi hlo hs M hhi negative height
  have hm := hmark p hp hcop slots lists a hslots ha ∅
    (principalWindow om lo hi hlo hs negative height) X M hX hv
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hm
  have ht := htail p hp hg hinj hc F Ψ hΨ m c d hd _ W Z
    (Cm*L^(1/2:ℝ)*SchwartzMap.seminorm ℝ 0 0 om) Y L R hZ (by positivity) hY hL hy hyi hl hm
    (markedRadial_support p slots lists a ∅ _ X M hX hv) hR
  have hp : (L^(1/2:ℝ))^2=L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLpos.le]
    norm_num
  have habsorb : L*Z^(-(saving+Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*Z^(-(saving+Lcap)) := mul_le_mul_of_nonneg_right hl (by positivity)
      _=Z^(-saving) := by rw [←Real.rpow_add hz];congr 1;ring
  apply ht.trans
  calc
    _=(Ct*Cm^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        (L*Z^(-(saving+Lcap))) := by rw [mul_pow,mul_pow,hp];ring
    _≤_ := by
      exact mul_le_mul_of_nonneg_left habsorb (by positivity)

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityTailEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ)
    (R : Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        ‖secondSourceTail p hp hg hinj pool
          (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
          ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit)*∏i∈D,p i)
          ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit) d
          (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
            (principalWindow om lo hi hlo hs negative t) X) W Y
          (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R D G E))‖

theorem whole_priority_tail_weighted (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Z^(-saving)*(∑D∈pool.powerset,‖selector D‖*primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := marked_rapid_tail Lcap tau saving hLcap htau
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power (1/2) (by norm_num)
  refine ⟨s,((32*512:ℝ)^2*512)*Ct*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Ct*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hP : 0≤P := by dsimp [P];positivity
  have hn (D : Finset ι) : 0≤primeProductNorm p (A∪D) := (primeProductNorm_pos p hp _).le
  have hm (J : Finset σ) (hJ : J∈slots.powerset) (D : Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*primeProductNorm p (A∪D) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (A∪D)
    have he : ((primeProductNorm p (A∪D))^(1/2:ℝ))^2=primeProductNorm p (A∪D) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (hn D)]
      norm_num
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^(1/2:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      _=_ := by rw [mul_pow,he]
  unfold wholePriorityTailEnergy
  dsimp only
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      by_cases hsel : selector D=0
      · simp only [hsel,norm_zero,mul_zero,zero_mul,le_refl]
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro core hcore
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc
          _≤∑J∈slots.powerset,Cm^2*primeProductNorm p (A∪D)*P := by
            apply Finset.sum_le_sum
            intro J hJ
            have ht := htail p hp hcop hg hinj hc pool
              (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
              (fun z=>(firstCoreTwist_norm_le negative _ Ψ core z).trans (hΨ z))
              ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit)*∏i∈D,p i)
              ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
                b.leftBit b.rightBit) d hd (slots\J) (fun i=>lists i\(A∪D)) a
              (residual_lists_pairwise slots J lists A D hslots)
              (residual_coeff_bound slots J lists a A D ha) om W lo hi hlo hs negative t X M Y Z (R D)
              hX hhi hZ hY hL hy hyi hl (hR D hD hsel)
            exact mul_le_mul (hm J hJ D) ht (norm_nonneg _) (mul_nonneg (sq_nonneg _) (hn D))
          _=_ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*primeProductNorm p (A∪D)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _))
        (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (hn D)) hP))
    _=((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*primeProductNorm p (A∪D)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (hn D))
    _=_ := by
      have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

theorem whole_priority_tail_bound (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*(B^2*primeProductNorm p C)*T^2*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_weighted Lcap tau saving hLcap htau
  refine ⟨s,128*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hn := first_whole_extracted_norm p hp b hb C extra he negative B hB hb₁ hb₂
  have hmass := first_selector_weighted_mass p hp hinj pool
    (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)) selector
    (B^2*primeProductNorm p C) T S 1 (mul_nonneg (sq_nonneg _) (primeProductNorm_pos p hp C).le)
    hT hS (by norm_num) hn hsel hsupp
  simp only [Real.rpow_one] at hmass
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left hmass
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Z^(-saving) by positivity)
  convert hh using 1
  ring

theorem whole_priority_tail_rapid (Lcap tau saving : ℝ) (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
      (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (selector : Finset ι→ℂ) (om W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
      (hs : Function.support om⊆Set.Icc lo hi) (M t X Y Z : ℝ)
      (R : Finset ι→Finset ι→Finset ι→ℝ) (B T S : ℝ),
      b.Admissible → extra⊆b.support → 0≤B → 0<T → 0≤S →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B →
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B →
      (∀D∈pool.powerset,‖selector D‖≤S) →
      (∀D∈pool.powerset,selector D≠0 → primeProductNorm p D≤T) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀D∈pool.powerset,selector D≠0 → ∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p d G E.val (X*Real.exp M) Y (Z^tau)≤R D G E.val) →
      B^2*primeProductNorm p C≤Z^Lcap → T≤Z^Lcap →
      wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a
        selector om W lo hi hlo hs X t Y R ≤
      Ct*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
        S*Z^(-saving) := by
  obtain ⟨s,Ct,hCt,htail⟩ := whole_priority_tail_bound Lcap tau (saving+3*Lcap) hLcap htau
  refine ⟨s,Ct,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR hEcap hTcap
  have ht := htail p hp hg hinj hcop hc pool b C extra negative Ψ m d slots lists a selector
    om W lo hi hlo hs M t X Y Z R B T S hb he hB hT hS hb₁ hb₂ hsel hsupp
    hslots ha hΨ hd hhi hX hZ hY hL hy hyi hl hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have habsorb : (B^2*primeProductNorm p C)*T^2*Z^(-(saving+3*Lcap))≤Z^(-saving) := by
    calc
      _≤Z^Lcap*(Z^Lcap)^2*Z^(-(saving+3*Lcap)) := by gcongr
      _=Z^(-saving) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  apply ht.trans
  have hh := mul_le_mul_of_nonneg_left habsorb
    (show 0≤Ct*(4:ℝ)^slots.card*
      (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*S by positivity)
  convert hh using 1
  ring

def wholeFreshError (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (R : Finset ι→Finset ι→ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) : ℂ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let H:=markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
    (principalWindow om lo hi hlo hs negative t) X
  let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit)*∏i∈D,p i
  let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
  firstFreshSecondPoisson p hp hg hinj pool D b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (fun i=>lists i\(A∪D)) a) om X (∏i∈C,p i) d core t Y -
  truncatedSecondSource p hp hg hinj pool Ψ₀ m₀ c₀ d H rowMajorant Y
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))

lemma wholeFreshError_eq_tail (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra D : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (R : Finset ι→Finset ι→ℝ)
    (r : RayCharacter×RayCharacter) (core : FirstCoreIndex) :
    wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
      om lo hi hlo hs X t Y R r core =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    secondSourceTail p hp hg hinj pool (firstCoreTwist negative (if negative then r.1 else r.2) Ψ core)
      ((m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)*∏i∈D,p i)
      ((∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) d
      (markedRadial p (slots\J) (fun i=>lists i\(A∪D)) a ∅
        (principalWindow om lo hi hlo hs negative t) X) rowMajorant Y
      (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E)) := by
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have he := first_fresh_radial_truncated p hp hg hinj hc pool D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m (slots\J) (fun i=>lists i\(A∪D)) a
    (fun i _=>residual_lists_avoid lists A D i) om lo hi hlo hs X t Y hX hY
    (∏i∈C,p i) d core
    (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))
  dsimp only at he
  unfold wholeFreshError
  dsimp only
  rw [he,add_sub_cancel_left]

theorem wholePriorityTailEnergy_eq_original_errors
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support om⊆Set.Icc lo hi) (X t Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (R : Finset ι→Finset ι→Finset ι→ℝ) :
    wholePriorityTailEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector
      om rowMajorant lo hi hlo hs X t Y R =
    let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
    (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
          ‖wholeFreshError p hp hg hinj pool b C extra D negative Ψ m d slots J lists a
            om lo hi hlo hs X t Y (R D) r core‖ := by
  simp_rw [wholeFreshError_eq_tail p hp hg hinj hc pool b C extra _ negative Ψ m d slots _
    lists a om lo hi hlo hs X t Y hX hY]
  rfl

end SevenEighths.InverseWholePriorityRapidTail

end

end OAI
