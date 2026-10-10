import OAI.NumberTheory.PrimeGaps.PatternMoments

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem weightedBlock_average_limit {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin (n+1) → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M)
    (k : Setoid (Fin (n+1)) → ℝ) :
    Tendsto (fun X : ℕ => (average X (weightedBlock X (blockLength lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin (n+1)),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin (n+1)))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ)))))) := by
  simpa only [average_weightedBlock,Complex.ofReal_sum,Complex.ofReal_mul] using
    unmarked_labeled_expansion_limit hlam a ha F rho hrho hrho1 hbudget hF hFs M hM hbound
      (fun r => (k r:ℂ))

theorem average_const {X : ℕ} (hX : X≠0) (c : ℝ) : average X (fun _ => c)=c := by
  unfold average
  simp only [Finset.sum_const,Nat.card_Ioc,nsmul_eq_mul]
  rw [show 2*X-X=X by omega]
  simp [hX]

@[simp] theorem weightedBlock_zero (X h a m : ℕ)
    (F : (Fin 0 → ℝ) → ℝ) (k : Setoid (Fin 0) → ℝ) :
    weightedBlock X h a F k m=k ⊥*F 0 := by
  unfold weightedBlock
  simp only [divisorSum_fin_zero]
  have he (b : Fin 0 → Fin h) : Setoid.ker b=⊥ := by
    apply Setoid.ext
    intro i
    exact Fin.elim0 i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul]

theorem weightedBlock_average_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X (weightedBlock X (blockLength lam X) (a X) F k))
      atTop (𝓝 c) := by
  cases n with
  | zero =>
    refine ⟨k ⊥*F 0,?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    have he : weightedBlock X (blockLength lam X) (a X) F k=(fun _ => k ⊥*F 0) :=
      funext (fun m => weightedBlock_zero X _ _ m F k)
    rw [he,average_const (by omega : X≠0)]
  | succ n =>
    have hc : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin (n+1)) ℝ).toHomeomorph.isClosedEmbedding).comp_left
        Complex.ofReal_zero
    have hs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+1)) => (F v.ofLp:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hFs.comp (EuclideanSpace.equiv (Fin (n+1)) ℝ).contDiff)
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    have hM0 : 0≤M := (norm_nonneg (F 0)).trans (hM 0)
    have hh := weightedBlock_average_limit hlam a ha F rho hrho hrho1 hbudget hc hs M hM0
      (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k
    exact ⟨_,Complex.continuous_re.continuousAt.tendsto.comp hh⟩

theorem HasBudget.tensor {n p : ℕ} {F : (Fin n → ℝ) → ℝ} {G : (Fin p → ℝ) → ℝ}
    {a b : ℝ} (hF : HasBudget F a) (hG : HasBudget G b) :
    HasBudget (tensorProfile F G) (a+b) := by
  intro v hv hsum
  unfold tensorProfile
  rw [Fin.sum_univ_add] at hsum
  by_cases hf : a<∑ i : Fin n,v (i.castAdd p)
  · rw [hF _ (fun i => hv (i.castAdd p)) hf,zero_mul]
  · rw [hG _ (fun i => hv (i.natAdd n)) (by linarith),mul_zero]

theorem weightedBlock_fourth_converges {n K : ℕ} {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho4 : 4*rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    ∃ c : ℝ,Tendsto (fun X : ℕ => average X
      (fun m => weightedBlock X (blockLength lam X) (a X) F k m^4)) atTop (𝓝 c) := by
  let F2 := tensorProfile F F
  let k2 := tensorCoefficient k k
  have hc2 := tensorProfile_compact F F hF hF
  have hs2 := tensorProfile_smooth F F hFs hFs
  obtain ⟨c,hc⟩ := weightedBlock_average_converges hlam a ha (tensorProfile F2 F2)
    ((rho+rho)+(rho+rho)) (by positivity) (by linarith)
    ((hbudget.tensor hbudget).tensor (hbudget.tensor hbudget))
    (tensorProfile_compact F2 F2 hc2 hc2) (tensorProfile_smooth F2 F2 hs2 hs2)
    (tensorCoefficient k2 k2)
  refine ⟨c,?_⟩
  convert hc using 1
  ext X
  congr 1
  funext m
  rw [←weightedBlock_mul,←weightedBlock_mul]
  ring

theorem fourth_power_sum_le {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ i∈S,f i)^4≤(S.card:ℝ)^3*∑ i∈S,f i^4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=f)
  have h2 := sq_sum_le_card_mul_sum_sq (s:=S) (f:=fun i => f i^2)
  have h3 := mul_self_le_mul_self (sq_nonneg (∑ i∈S,f i)) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (S.card:ℝ))
  simp only [←pow_mul] at h3 h4
  nlinarith only [h3,h4]

noncomputable def subsetCoefficient (n : ℕ) (r : Setoid (Fin n)) : ℝ :=
  if r=⊥ then (n.factorial:ℝ)⁻¹ else 0

noncomputable def orderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), weightedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) (subsetCoefficient j) m

theorem blockOffset_eventually {lam : ℝ} (hlam : 0<lam) :
    ∀ᶠ X : ℕ in atTop,blockLength lam X+1≤2*blockLength lam X := by
  filter_upwards [(blockLength_tendsto hlam).eventually_ge_atTop 1] with X hX
  omega

theorem finite_sum_fourth_bound {α : Type*} [Fintype α]
    (f : α → ℕ → ℕ → ℝ)
    (h : ∀ j,∃ c : ℝ,Tendsto (fun X => average X (fun m => f j X m^4)) atTop (𝓝 c)) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => (∑ j,f j X m)^4)≤M := by
  classical
  choose c hc using h
  let C := (Fintype.card α:ℝ)^3*∑ j,c j
  have ht : Tendsto (fun X => (Fintype.card α:ℝ)^3*∑ j,average X (fun m => f j X m^4))
      atTop (𝓝 C) := (tendsto_finsetSum Finset.univ (fun j _ => hc j)).const_mul _
  refine ⟨|C|+1,by positivity,?_⟩
  filter_upwards [(tendsto_order.mp ht).2 (|C|+1) (by linarith [le_abs_self C])] with X hX
  apply le_trans ?_ hX.le
  calc
    _ ≤ average X (fun m => (Fintype.card α:ℝ)^3*∑ j,f j X m^4) :=
      average_mono _ _ (fun m _ => by
        simpa only [Finset.card_univ] using
          (fourth_power_sum_le Finset.univ (fun j => f j X m)))
    _ = _ := by rw [average_const_mul,average_finset_sum]

theorem orderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => orderedWeight tau lam k f X m^4)≤M := by
  apply finite_sum_fourth_bound
  intro j
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_fourth_converges hlam (fun X => blockLength lam X+1)
    (blockOffset_eventually hlam) (cumulativeProfile tau (f j)) tau htau htau4
    (cumulativeProfile_budget tau (f j) hfj.2.2.1)
    (cumulativeProfile_compact tau (f j) hfj.2.1)
    (cumulativeProfile_smooth tau (f j) hfj.2.1 hfj.1) (subsetCoefficient j)

noncomputable def matchedPattern {n : ℕ} (e : Equiv.Perm (Fin n)) : Setoid (Fin (n+n)) :=
  Setoid.ker (permutedLabels e)

@[simp] theorem matchedPattern_left {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.castAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.castAdd n)=permutedLabels e (j.castAdd n) ↔ i=j
  simp [permutedLabels]

@[simp] theorem matchedPattern_right {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Setoid.comap (Fin.natAdd n) (matchedPattern e)=⊥ := by
  apply Setoid.ext
  intro i j
  change permutedLabels e (i.natAdd n)=permutedLabels e (j.natAdd n) ↔ i=j
  simp [permutedLabels]

theorem matchedPattern_injective {n : ℕ} : Function.Injective (@matchedPattern n) := by
  intro e f hef
  apply Equiv.ext
  intro i
  have he : (matchedPattern e) ((e i).castAdd n) (i.natAdd n) := by
    change permutedLabels e ((e i).castAdd n)=permutedLabels e (i.natAdd n)
    simp [permutedLabels]
  rw [hef] at he
  change permutedLabels f ((e i).castAdd n)=permutedLabels f (i.natAdd n) at he
  simpa [permutedLabels] using he

theorem matchedPattern_quotient_card {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Fintype.card (Quotient (matchedPattern e))=n := by
  have hs : Function.Surjective (permutedLabels e) := by
    intro j
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  have eqv : Quotient (matchedPattern e) ≃ Fin n :=
    Setoid.quotientKerEquivOfSurjective (permutedLabels e) hs
  exact (Fintype.card_congr eqv).trans (Fintype.card_fin n)

theorem ker_eq_bot_iff_injective {α β : Type*} (f : α → β) :
    Setoid.ker f=⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    change (Setoid.ker f) x y at hxy
    rw [h] at hxy
    exact hxy
  · intro h
    apply Setoid.ext
    intro x y
    exact h.eq_iff

theorem numericPattern_left_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.castAdd n) r=⊥) :
    Function.Injective (fun i : Fin m => numericPattern r (i.castAdd n)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin m => numericPattern r (i.castAdd n))=
      Setoid.comap (Fin.castAdd n) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem numericPattern_right_injective {m n : ℕ} (r : Setoid (Fin (m+n)))
    (h : Setoid.comap (Fin.natAdd m) r=⊥) :
    Function.Injective (fun i : Fin n => numericPattern r (i.natAdd m)) := by
  apply (ker_eq_bot_iff_injective _).mp
  have he : Setoid.ker (fun i : Fin n => numericPattern r (i.natAdd m))=
      Setoid.comap (Fin.natAdd m) (Setoid.ker (numericPattern r)) := rfl
  rw [he,numericPattern_ker,h]

theorem injective_ranges_card {m n : ℕ} {α : Type*} (a : Fin m → α) (b : Fin n → α)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : Set.range a=Set.range b) : m=n := by
  have e : Fin m ≃ Fin n := (Equiv.ofInjective a ha).trans
    ((Set.equivOfEq hab).trans (Equiv.ofInjective b hb).symm)
  simpa using Fintype.card_congr e

theorem matching_pattern_eq {n : ℕ} (r : Setoid (Fin (n+n)))
    (hleft : Setoid.comap (Fin.castAdd n) r=⊥)
    (hright : Setoid.comap (Fin.natAdd n) r=⊥)
    (hrange : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))=
      Set.range (fun i : Fin n => numericPattern r (i.natAdd n))) :
    ∃ e : Equiv.Perm (Fin n),r=matchedPattern e := by
  let a := fun i : Fin n => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd n)
  have ha : Function.Injective a := numericPattern_left_injective r hleft
  have hb : Function.Injective b := numericPattern_right_injective r hright
  obtain ⟨e,he⟩ := injective_same_range_perm a b hb hrange
  refine ⟨e,?_⟩
  rw [←numericPattern_ker r]
  have hf : numericPattern r=a ∘ permutedLabels e := by
    funext i
    cases i using Fin.addCases with
    | left i => simp [a,permutedLabels]
    | right i => simpa [b,permutedLabels] using congrFun he i
  rw [hf,ker_comp_injective _ _ ha]
  rfl

theorem matchedPattern_family {n : ℕ} (e : Equiv.Perm (Fin n)) :
    equalityPatternFamily (matchedPattern e)=fiberSubsetFamily (permutedLabels e) Finset.univ := by
  classical
  have hi : Finset.univ.image (permutedLabels e)=Finset.univ := by
    ext j
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    exact ⟨j.castAdd n,by simp [permutedLabels]⟩
  rw [←hi]
  unfold equalityPatternFamily shiftFamily
  ext S
  simp only [mem_fiberSubsetFamily_image]
  have he (i j : Fin (n+n)) :
      (numericPattern (matchedPattern e) i:ℤ)=(numericPattern (matchedPattern e) j:ℤ) ↔
        permutedLabels e i=permutedLabels e j := by
    change (Setoid.ker (fun x => (numericPattern (matchedPattern e) x:ℤ))) i j ↔
      (matchedPattern e) i j
    rw [numericPattern_int_ker]
  simp_rw [he]

theorem sum_matched_patterns {n : ℕ} (c : ℂ) (A : Setoid (Fin (n+n)) → ℂ)
    (hzero : ∀ r,r∉Set.range (@matchedPattern n) → A r=0)
    (hvalue : ∀ e : Equiv.Perm (Fin n),A (matchedPattern e)=c) :
    (∑ r,A r)=(n.factorial:ℂ)*c := by
  classical
  calc
    _ = ∑ r∈Finset.univ.image (@matchedPattern n),A r := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      apply hzero r
      rintro ⟨e,rfl⟩
      exact hr (Finset.mem_image_of_mem _ (Finset.mem_univ e))
    _ = ∑ e : Equiv.Perm (Fin n),A (matchedPattern e) :=
      Finset.sum_image (fun _ _ _ _ h => matchedPattern_injective h)
    _ = _ := by simp [hvalue,Fintype.card_perm]

theorem realEuclidean_compact {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : HasCompactSupport F) :
    HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  (hF.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
    Complex.ofReal_zero

theorem realEuclidean_smooth {n : ℕ} (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hF.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)

noncomputable def cumulativePatternKernel {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (r : Setoid (Fin n)) : ℂ :=
  kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
    (fun v => (cumulativeProfile tau f v.ofLp:ℂ))
    (realEuclidean_compact _ (cumulativeProfile_compact tau f hf))
    (realEuclidean_smooth _ (cumulativeProfile_smooth tau f hf hs))) (equalityPatternFamily r)

theorem cumulative_pair_unmatched {m n : ℕ} {tau : ℝ}
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau)
    (r : Setoid (Fin (m+n)))
    (hl : Setoid.comap (Fin.castAdd n) r=⊥) (hr : Setoid.comap (Fin.natAdd m) r=⊥)
    (hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
      Set.range (fun i : Fin n => numericPattern r (i.natAdd m))) :
    cumulativePatternKernel (tau+tau) (tensorProfile f g)
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r=0 := by
  let a := fun i : Fin m => numericPattern r (i.castAdd n)
  let b := fun i : Fin n => numericPattern r (i.natAdd m)
  have ha := numericPattern_left_injective r hl
  have hb := numericPattern_right_injective r hr
  have he : Fin.append a b=numericPattern r := by
    funext i
    cases i using Fin.addCases <;> simp [a,b]
  have hfamily : equalityPatternFamily r=
      fiberSubsetFamily (Fin.append a b) (Finset.univ.image (Fin.append a b)) := by
    unfold equalityPatternFamily shiftFamily
    ext S
    simp only [mem_fiberSubsetFamily_image,he,Int.natCast_inj]
  unfold cumulativePatternKernel
  rw [hfamily]
  convert cumulative_tensor_unmatched_kernel_zero f g hf hg hfs hgs hsf hsg a b ha hb hne
    (realEuclidean_compact _ (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg)))
    (realEuclidean_smooth _ (cumulativeProfile_smooth _ _
      (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))) using 1
  congr 2
  ext x
  simp

theorem cumulative_pair_matched {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f)
    (e : Equiv.Perm (Fin n)) :
    cumulativePatternKernel (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) (matchedPattern e)=
      (l2Mass f:ℂ) := by
  unfold cumulativePatternKernel
  rw [matchedPattern_family]
  exact cumulative_tensor_permuted_kernel e f hf hfs hsf hsym _ _

theorem cumulative_square_pattern_sum {n : ℕ} {tau : ℝ} (lam : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    (∑ r : Setoid (Fin (n+n)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r))=
      (alpha lam n*l2Mass f:ℂ) := by
  classical
  let A := fun r : Setoid (Fin (n+n)) =>
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f f)
          (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs) r)
  have hz : ∀ r,r∉Set.range (@matchedPattern n) → A r=0 := by
    intro r hr
    by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
    · by_cases hr' : Setoid.comap (Fin.natAdd n) r=⊥
      · have hne : Set.range (fun i : Fin n => numericPattern r (i.castAdd n))≠
            Set.range (fun i : Fin n => numericPattern r (i.natAdd n)) := by
          intro he
          obtain ⟨e,rfl⟩ := matching_pattern_eq r hl hr' he
          exact hr ⟨e,rfl⟩
        simp only [A,cumulative_pair_unmatched f f hf hf hfs hfs hsf hsf r hl hr' hne,mul_zero]
      · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hr',mul_zero,Complex.ofReal_zero,zero_mul]
    · simp only [A,tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]
  have hv : ∀ e : Equiv.Perm (Fin n), A (matchedPattern e)=
      ((n.factorial:ℂ)⁻¹)^2*((lam:ℂ)^n*(l2Mass f:ℂ)) := by
    intro e
    simp only [A,tensorCoefficient,matchedPattern_left,matchedPattern_right,subsetCoefficient,
      ↓reduceIte,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,
      matchedPattern_quotient_card,cumulative_pair_matched f hf hfs hsf hsym e,pow_two]
  have hh := sum_matched_patterns _ A hz hv
  change (∑ r,A r)=_
  rw [hh]
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast n.factorial_ne_zero
  simp only [alpha,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
  field_simp

theorem cumulative_cross_pattern_sum {m n : ℕ} (hmn : m≠n) {tau : ℝ} (lam : ℝ)
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex m tau) (hsg : tsupport g⊆positiveSimplex n tau) :
    (∑ r : Setoid (Fin (m+n)),
      (tensorCoefficient (subsetCoefficient m) (subsetCoefficient n) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hl : Setoid.comap (Fin.castAdd n) r=⊥
  · by_cases hr : Setoid.comap (Fin.natAdd m) r=⊥
    · have hne : Set.range (fun i : Fin m => numericPattern r (i.castAdd n))≠
          Set.range (fun i : Fin n => numericPattern r (i.natAdd m)) := by
        intro he
        exact hmn (injective_ranges_card _ _ (numericPattern_left_injective r hl)
          (numericPattern_right_injective r hr) he)
      rw [cumulative_pair_unmatched f g hf hg hfs hgs hsf hsg r hl hr hne,mul_zero,mul_zero]
    · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hr,mul_zero,Complex.ofReal_zero,zero_mul]
  · simp only [tensorCoefficient,subsetCoefficient,ite_eq_right hl,zero_mul,Complex.ofReal_zero]

theorem weightedBlock_congr_orthant {n X : ℕ} (hX : 2≤X) (h a m : ℕ)
    (F G : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ)
    (hFG : ∀ v,(∀ i,0≤v i) → F v=G v) :
    weightedBlock X h a F k m=weightedBlock X h a G k m := by
  apply Finset.sum_congr rfl
  intro b _
  rw [divisorSum_congr_orthant hX m _ F G hFG]

theorem weightedBlock_cumulative_mul {n p X : ℕ} (hX : 2≤X) (h a m : ℕ) {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : tsupport f⊆positiveSimplex n tau) (hg : tsupport g⊆positiveSimplex p tau)
    (k : Setoid (Fin n) → ℝ) (l : Setoid (Fin p) → ℝ) :
    weightedBlock X h a (cumulativeProfile tau f) k m*
      weightedBlock X h a (cumulativeProfile tau g) l m=
    weightedBlock X h a (cumulativeProfile (tau+tau) (tensorProfile f g)) (tensorCoefficient k l) m := by
  rw [weightedBlock_mul]
  apply weightedBlock_congr_orthant hX
  intro v hv
  let v1 := fun i : Fin n => v (i.castAdd p)
  let v2 := fun i : Fin p => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by
    funext i
    cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact (cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)).symm

theorem weightedBlock_positive_limit {n K : ℕ} (hn : 0<n) {lam : ℝ} (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrho1 : rho<1) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (average X (weightedBlock X (blockLength lam X) (a X) F k):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^Fintype.card (Quotient r)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
    exact weightedBlock_average_limit hlam a ha F rho hrho hrho1 hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v) k

theorem cumulative_pair_limit {n p K : ℕ} (hnp : 0<n+p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau g) (subsetCoefficient p) m):ℂ))
      atTop (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := weightedBlock_positive_limit hnp hlam a ha
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 2
  funext m
  exact (weightedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _).symm

@[simp] theorem cumulativeProfile_fin_zero {tau : ℝ} (f : (Fin 0 → ℝ) → ℝ)
    (hsf : tsupport f⊆positiveSimplex 0 tau) (v : Fin 0 → ℝ) :
    cumulativeProfile tau f v=f 0 := by
  rw [cumulativeProfile_tail tau f hsf v (fun i => Fin.elim0 i)]
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  have he : Ici v=(Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [Set.mem_Ici,Set.mem_univ,iff_true]
    exact fun i => Fin.elim0 i
  rw [he,setIntegral_univ]
  exact integral_dirac f 0

@[simp] theorem l2Mass_fin_zero (f : (Fin 0 → ℝ) → ℝ) : l2Mass f=f 0^2 := by
  unfold l2Mass
  have he : (fun x => f x^2)=(fun _ : Fin 0 → ℝ => f 0^2) := by
    funext x
    rw [Subsingleton.elim x 0]
  rw [he,Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  simp

end LargePrimeGaps

end OAI
