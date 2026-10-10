import OAI.NumberTheory.DirichletL.Descent.FirstToSecond
import OAI.NumberTheory.DirichletL.Descent.PrincipalChild

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]

omit [DecidableEq ι] in

theorem input_diagonal (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * star (H U) * H U =
      ((‖secondInputCoefficient p hg Ψ m c d H U‖^2 : ℝ) : ℂ) := by
  have he : secondInputCoefficient p hg Ψ m c d H U =
      secondInputCoefficient p hg Ψ m c d (fun _=>1) U * H U := by
    simp only [secondInputCoefficient,mul_one]
  have hh : star (H U)*H U=((‖H U‖^2 : ℝ):ℂ) := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [he,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,hh]

omit [DecidableEq ι] in
theorem input_norm_product (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * ‖H U‖^2 =
      ‖secondInputCoefficient p hg Ψ m c d H U‖^2 := by
  simp only [secondInputCoefficient,mul_one,norm_mul,mul_pow]

omit [DecidableEq ι] in

theorem zero_congr_input (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis)
    (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (K : Finset ι→Finset ι→Finset Eis) :
    truncatedSecondZero p hg F Ψ m c d H₁ W Y K=
      truncatedSecondZero p hg F Ψ m c d H₂ W Y K := by
  simp only [truncatedSecondZero,input_diagonal,he]

include hp in

theorem restoration_congr_input
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis) (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (θ : Finset ι→Finset ι→Eis→ℂ) :
    principalRestoration p hg hinj hp F Ψ m c d H₁ W Y θ=
      principalRestoration p hg hinj hp F Ψ m c d H₂ W Y θ := by
  unfold principalRestoration
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro k
  congr 1
  simp only [restorationTerm_eq,←Complex.ofReal_mul,input_norm_product,he]

include hp in

theorem firstCoreInputRow_principal_test
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t : ℝ) (hX : 0<X) (c d : Eis) (r : FirstCoreIndex) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m (primeMark slots lists coeff)
      (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z =
    inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
      ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X)
      (if negative then -z else z) := by
  rw [firstCoreInputRow_fixed_pool p hg hinj]
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro U hU
  rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]

include hp in

theorem firstFreshSecondPoisson_markedRadial
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ₀ m₀ c₀ d H₀ G U V *
          maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  intro H₀ Ψ₀ m₀ c₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  have he (z : Eis) : inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z=
      inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z := by
    unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
    apply Finset.sum_congr rfl
    intro U hU
    rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
  calc
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z‖^2 : ℝ) := by
      rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
        (primeMark slots lists coeff) om X c d r t Y hY]
      exact (inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H
        rowMajorant Y hY).symm
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z‖^2 : ℝ) := by simp_rw [he]
    _ = _ := inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀
      rowMajorant Y hY

theorem residual_lists_pairwise (slots J : Finset σ) (lists : σ→Finset ι) (A D : Finset ι)
    (h : (slots : Set σ).PairwiseDisjoint lists) :
    ((slots\J : Finset σ) : Set σ).PairwiseDisjoint (fun i=>lists i\(A∪D)) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe,Finset.mem_sdiff] at hi hj
  exact (h hi.1 hj.1 hij).mono
    Finset.sdiff_subset Finset.sdiff_subset

omit [DecidableEq σ] in
theorem residual_lists_avoid (lists : σ→Finset ι) (A D : Finset ι) (i : σ) :
    Disjoint (lists i\(A∪D)) D := by
  apply Finset.disjoint_left.mpr
  intro k hk hkd
  exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_union_right A hkd)

theorem residual_coeff_bound (slots J : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (A D : Finset ι)
    (h : ∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) :
    ∀ i∈slots\J,∀ k∈lists i\(A∪D),‖coeff i k‖≤1 := by
  intro i hi k hk
  exact h i (Finset.mem_sdiff.mp hi).1 k (Finset.mem_sdiff.mp hk).1

end Arithmetic

theorem firstCore_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := physical_child_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d hd V W X M Y R
    hX hY hR (principalWindow_upper om a b ha hs M hb negative t)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

theorem priority_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots J : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) coeff)
        (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := firstCore_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots J lists coeff hslots hcoeff F D B A v ε₁ ε₂
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR
  exact hbound p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) coeff
    (residual_lists_pairwise slots J lists A D hslots)
    (residual_coeff_bound slots J lists coeff A D hcoeff) F D B v ε₁ ε₂
    (fun i _=>residual_lists_avoid lists A D i) negative χ Ψ hΨ m c d hd r om W a b ha hs
    M t X Y R hb hX hY hR

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
