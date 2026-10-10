import OAI.NumberTheory.PrimeGaps.WeightMoments

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

theorem cumulative_square_limit {n K : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m^2))
      atTop (𝓝 (alpha lam n*l2Mass f)) := by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    simp only [weightedBlock_zero,cumulativeProfile_fin_zero f hsf,
      subsetCoefficient,↓reduceIte,Nat.factorial_zero,Nat.cast_one,inv_one,one_mul]
    rw [average_const (by omega : X≠0),l2Mass_fin_zero]
    simp [alpha]
  | inr hn =>
    have hh := cumulative_pair_limit (by omega : 0<n+n) htau htau2 hlam a ha
      f f hf hf hfs hfs hsf hsf
    rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
    have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
    simpa [Function.comp_def,Complex.mul_re,←pow_two] using hh'

theorem cumulative_cross_limit {n p K : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam)
    (a : ℕ → ℕ) (ha : ∀ᶠ X : ℕ in atTop,a X≤K*blockLength lam X)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (a X) (cumulativeProfile tau g) (subsetCoefficient p) m))
      atTop (𝓝 0) := by
  have hh := cumulative_pair_limit (by omega : 0<n+p) htau htau2 hlam a ha
    f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

theorem orderedWeight_second_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => orderedWeight tau lam k f X m^2))
      atTop (𝓝 (familyW lam k f)) := by
  classical
  let H := fun (j : Fin (k+1)) X m => weightedBlock X (blockLength lam X) (blockLength lam X+1)
       (cumulativeProfile tau (f j)) (subsetCoefficient j) m
  have hp (i j : Fin (k+1)) :
      Tendsto (fun X : ℕ => average X (fun m => H i X m*H j X m)) atTop
        (𝓝 (if i=j then alpha lam i*l2Mass (f i) else 0)) := by
    have hfi := hf.2.1 i (by omega : (i:ℕ)≤k)
    have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte]
      simpa only [H,pow_two] using cumulative_square_limit htau htau2 hlam
        (fun X => blockLength lam X+1) (blockOffset_eventually hlam)
        (f i) hfi.2.1 hfi.1 hfi.2.2.1 hfi.2.2.2
    · simp only [ite_eq_right hij]
      have hne : (i:ℕ)≠(j:ℕ) := fun h => hij (Fin.ext h)
      exact cumulative_cross_limit hne htau htau2 hlam
        (fun X => blockLength lam X+1) (blockOffset_eventually hlam)
        (f i) (f j) hfi.2.1 hfj.2.1 hfi.1 hfj.1 hfi.2.2.1 hfj.2.2.1
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hp i j
  have he (X : ℕ) : average X (fun m => orderedWeight tau lam k f X m^2)=
      ∑ i : Fin (k+1),∑ j : Fin (k+1),average X (fun m => H i X m*H j X m) := by
    unfold orderedWeight
    simp only [pow_two,Finset.sum_mul_sum,average_finset_sum]
    rfl
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte] at hs
  have hv : (∑ i : Fin (k+1),alpha lam i*l2Mass (f i))=familyW lam k f := by
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => alpha lam j*l2Mass (f j)) (k+1)
  rw [hv] at hs
  exact hs.congr' (Eventually.of_forall fun X => (he X).symm)

theorem cumulativeProfile_perm_orthant {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hsupp : tsupport f⊆positiveSimplex n tau)
    (hsym : SymmetricFunction f) (e : Equiv.Perm (Fin n))
    (v : Fin n → ℝ) (hv : ∀ i,0≤v i) :
    cumulativeProfile tau f (v ∘ e)=cumulativeProfile tau f v := by
  change cumulativeProfile tau f (fun i => v (e i))=cumulativeProfile tau f v
  rw [cumulativeProfile_tail tau f hsupp _ (fun i => hv (e i)),
    cumulativeProfile_tail tau f hsupp _ hv]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq : MeasurePreserving q volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm
  have hq_apply (x : Fin n → ℝ) : q x=x ∘ e := by
    funext i
    simp [q,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have he : q ⁻¹' {x : Fin n → ℝ | ∀ i,v (e i)≤x i}={x : Fin n → ℝ | ∀ i,v i≤x i} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,hq_apply,Function.comp_apply]
    constructor
    · intro h i
      simpa using h (e.symm i)
    · intro h i
      exact h (e i)
  have hh := hq.integral_comp' (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f x)
  have hefun : (fun x => ({x : Fin n → ℝ | ∀ i,v (e i)≤x i}).indicator f (q x))=
      ({x : Fin n → ℝ | ∀ i,v i≤x i}).indicator f := by
    funext x
    have hx : (∀ i,v (e i)≤q x i) ↔ ∀ i,v i≤x i := by
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq] using
        (Set.ext_iff.mp he x)
    have hm : q x∈{x : Fin n → ℝ | ∀ i,v (e i)≤x i} ↔ x∈{x : Fin n → ℝ | ∀ i,v i≤x i} := hx
    by_cases hvx : x∈{x : Fin n → ℝ | ∀ i,v i≤x i}
    · rw [Set.indicator_of_mem (hm.mpr hvx),Set.indicator_of_mem hvx,hq_apply,hsym]
    · rw [Set.indicator_of_notMem (fun h => hvx (hm.mp h)),Set.indicator_of_notMem hvx]
  rw [hefun,integral_indicator (by measurability), integral_indicator (by measurability)] at hh
  exact hh.symm

theorem divisorSum_perm_orthant {n X m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hF : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v)
    (e : Equiv.Perm (Fin n)) (b : Fin n → ℕ) :
    divisorSum X F m (b ∘ e)=divisorSum X F m b := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_equiv (functionPerm e)
  · intro d
    simp only [Fintype.mem_piFinset,functionPerm,Equiv.coe_fn_mk,Function.comp_apply]
    exact e.surjective.forall
  · intro d hd
    change divisorCoefficient X F d=divisorCoefficient X F (d ∘ e)
    unfold divisorCoefficient
    have hp : ∀ i,0<d i := fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)
    have he : logCoordinates X (d ∘ e)=(logCoordinates X d) ∘ e := rfl
    rw [he,hF e _ (logCoordinates_nonneg hX hp)]
    congr 1
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

noncomputable def subsetEnumeration {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) : Fin n ↪ Fin h :=
  S.1.orderEmbOfFin S.2 |>.toEmbedding

theorem subsetEnumeration_image {h n : ℕ} (S : {S : Finset (Fin h) // S.card=n}) :
    Finset.univ.image (subsetEnumeration S)=S.1 := by
  classical
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro hx
    refine ⟨(S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩,?_⟩
    change ((S.1.orderIsoOfFin S.2) ((S.1.orderIsoOfFin S.2).symm ⟨x,hx⟩)).val=x
    simp

noncomputable def enumeratePerm {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    {b : Fin n → Fin h // Function.Injective b} :=
  ⟨subsetEnumeration t.1 ∘ t.2,(subsetEnumeration t.1).injective.comp t.2.injective⟩

theorem enumeratePerm_image {h n : ℕ}
    (t : {S : Finset (Fin h) // S.card=n} × Equiv.Perm (Fin n)) :
    Finset.univ.image (enumeratePerm t).val=t.1.1 := by
  classical
  rw [←subsetEnumeration_image t.1]
  ext x
  simp only [Finset.mem_image,Finset.mem_univ,true_and,enumeratePerm,Function.comp_apply]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨t.2 i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨t.2.symm i,by simpa using hi⟩

theorem enumeratePerm_bijective (h n : ℕ) :
    Function.Bijective (enumeratePerm (h:=h) (n:=n)) := by
  classical
  constructor
  · rintro ⟨S,e⟩ ⟨T,d⟩ he
    have hST : S=T := by
      apply Subtype.ext
      rw [←enumeratePerm_image (S,e),←enumeratePerm_image (T,d),he]
    subst T
    have hed : e=d := by
      apply Equiv.ext
      intro i
      apply (subsetEnumeration S).injective
      exact congrFun (congrArg Subtype.val he) i
    subst d
    rfl
  · intro b
    let S : {S : Finset (Fin h) // S.card=n} :=
      ⟨Finset.univ.image b.val,by rw [Finset.card_image_of_injective _ b.2]; simp⟩
    have he : Set.range (subsetEnumeration S)=Set.range b.val := by
      ext x
      have hh := Finset.ext_iff.mp (subsetEnumeration_image S) x
      simpa only [Finset.mem_image,Finset.mem_univ,true_and,S,Set.mem_range] using hh
    obtain ⟨e,he⟩ := injective_same_range_perm (subsetEnumeration S) b.val b.2 he
    exact ⟨(S,e),Subtype.ext he.symm⟩

noncomputable def unorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ))

theorem weightedBlock_eq_unordered {n X h a m : ℕ} (hX : 2≤X)
    (F : (Fin n → ℝ) → ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin n)) v,(∀ i,0≤v i) → F (v ∘ e)=F v) :
    weightedBlock X h a F (subsetCoefficient n) m=unorderedBlock X h a F m := by
  classical
  unfold weightedBlock
  have he : (∑ b : Fin n → Fin h, subsetCoefficient n (Setoid.ker b)*
      divisorSum X F m (fun i => a+(b i:ℕ)))=
      ∑ b : {b : Fin n → Fin h // Function.Injective b},
        (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+(b.val i:ℕ)) := by
    simp only [subsetCoefficient,Setoid.ker_eq_bot_iff,ite_mul,zero_mul]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=fun b : Fin n → Fin h => Function.Injective b)
      (Finset.univ.filter fun b : Fin n → Fin h => Function.Injective b) (by simp) _
  rw [he]
  rw [←Fintype.sum_equiv (Equiv.ofBijective enumeratePerm (enumeratePerm_bijective h n))
    (fun t => (n.factorial:ℝ)⁻¹*divisorSum X F m (fun i => a+((enumeratePerm t).val i:ℕ)))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  unfold unorderedBlock
  apply Finset.sum_congr rfl
  intro S _
  have hd (e : Equiv.Perm (Fin n)) :
      divisorSum X F m (fun i => a+((enumeratePerm (S,e)).val i:ℕ))=
      divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ)) :=
    divisorSum_perm_orthant hX F hsym e (fun i => a+(subsetEnumeration S i:ℕ))
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

noncomputable def unorderedWeight (tau lam : ℝ) (k : ℕ)
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (X m : ℕ) : ℝ :=
  ∑ j : Fin (k+1), unorderedBlock X (blockLength lam X) (blockLength lam X+1)
    (cumulativeProfile tau (f j)) m

theorem orderedWeight_eq_unordered {tau lam : ℝ} {k X : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (hX : 2≤X) (m : ℕ) : orderedWeight tau lam k f X m=unorderedWeight tau lam k f X m := by
  unfold orderedWeight unorderedWeight
  apply Finset.sum_congr rfl
  intro j _
  have hfj := hf.2.1 j (by omega : (j:ℕ)≤k)
  exact weightedBlock_eq_unordered hX _ (cumulativeProfile_perm_orthant _ hfj.2.2.1 hfj.2.2.2)

theorem unorderedWeight_second_limit {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau2 : 2*tau<1) (hlam : 0<lam) :
    Tendsto (fun X : ℕ => average X (fun m => unorderedWeight tau lam k f X m^2))
      atTop (𝓝 (familyW lam k f)) := by
  apply (orderedWeight_second_limit f hf htau htau2 hlam).congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 1
  funext m
  rw [orderedWeight_eq_unordered f hf hX m]

theorem unorderedWeight_fourth_bound {tau lam : ℝ} {k : ℕ}
    (f : (j : ℕ) → (Fin j → ℝ) → ℝ) (hf : AdmissibleFamily tau k f)
    (htau : 0≤tau) (htau4 : 4*tau<1) (hlam : 0<lam) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ X : ℕ in atTop,
      average X (fun m => unorderedWeight tau lam k f X m^4)≤M := by
  obtain ⟨M,hM,h⟩ := orderedWeight_fourth_bound f hf htau htau4 hlam
  refine ⟨M,hM,?_⟩
  filter_upwards [h,eventually_ge_atTop 2] with X hX hX2
  simpa only [orderedWeight_eq_unordered f hf hX2] using hX

noncomputable def separatedOffsets (s h : ℕ) : Fin (s+1) → ℕ :=
  Fin.snoc (fun _ => h+1) 1

theorem separatedBox_mem {s h : ℕ} (u : Fin s → Fin h) (c : Fin h) :
    Fin.snoc u c∈distinctBox (fun j => (separatedOffsets s h j:ℤ)) ↔
      u∈distinctBox (fun _ : Fin s => ((h+1:ℕ):ℤ)) := by
  classical
  simp only [distinctBox,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hu i j hij
    have he : boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) i.castSucc=
        boxTuple (fun j => (separatedOffsets s h j:ℤ)) (Fin.snoc u c) j.castSucc := by
      simpa [boxTuple,separatedOffsets] using hij
    exact Fin.castSucc_injective s (hu he)
  · intro hu i j hij
    cases i using Fin.lastCases with
    | last =>
      cases j using Fin.lastCases with
      | last => rfl
      | cast j =>
        have hj := (u j).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
    | cast i =>
      cases j using Fin.lastCases with
      | last =>
        have hi := (u i).isLt
        have hc := c.isLt
        simp only [boxTuple,separatedOffsets,Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_one,Nat.cast_add] at hij
        omega
      | cast j =>
        congr 1
        apply hu
        simpa [boxTuple,separatedOffsets] using hij

noncomputable def separatedBoxEquiv (s h : ℕ) :
    ({u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h) ≃
    {u // u∈distinctBox (s:=s+1) (h:=h) (fun j => (separatedOffsets s h j:ℤ))} where
  toFun t := ⟨Fin.snoc t.1.1 t.2,(separatedBox_mem t.1.1 t.2).mpr t.1.2⟩
  invFun v := (⟨Fin.init v.1,by
      have hv : Fin.snoc (Fin.init v.1) (v.1 (Fin.last s))=v.1 := Fin.snoc_init_self v.1
      exact (separatedBox_mem _ _).mp (hv.symm ▸ v.2)⟩,v.1 (Fin.last s))
  left_inv t := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp [Fin.init]
    · simp
  right_inv v := by
    apply Subtype.ext
    exact Fin.snoc_init_self v.1

theorem separated_double_sum {s h : ℕ} (F : (Fin (s+1) → Fin h) → ℂ) :
    (∑ u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ)),∑ c : Fin h,F (Fin.snoc u c))=
      ∑ v∈distinctBox (s:=s+1) (h:=h) (fun j => (separatedOffsets s h j:ℤ)),F v := by
  classical
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  calc
    _ = ∑ t : {u // u∈distinctBox (s:=s) (h:=h) (fun _ => ((h+1:ℕ):ℤ))} × Fin h,
      F (Fin.snoc t.1.val t.2) := (Fintype.sum_prod_type _).symm
    _ = _ := Fintype.sum_equiv (separatedBoxEquiv s h) _ _ (fun _ => rfl)

theorem pattern_marked_sum_eq_box {n : ℕ} (r : Setoid (Fin n)) (h X : ℕ)
    (F : (Fin n → ℝ) → ℝ) :
    (∑ b∈patternClass (α:=Fin h) r,∑ c : Fin h,
      (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ))=
    ∑ v∈distinctBox (s:=Fintype.card (Quotient r)+1) (h:=h)
      (fun j => (separatedOffsets (Fintype.card (Quotient r)) h j:ℤ)),
      (average X (fun m => divisorSum X F m
        (patternBoxShifts (patternLabels r) (fun j => separatedOffsets _ h j.castSucc)
          (fun j => v j.castSucc))*
        theta (m+(separatedOffsets (Fintype.card (Quotient r)) h (Fin.last (Fintype.card (Quotient r)))+(v (Fin.last _):ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  rw [←separated_double_sum]
  simp only [separatedOffsets,Fin.snoc_castSucc,Fin.snoc_last]
  conv_lhs => rw [←Finset.sum_coe_sort]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Fintype.sum_equiv (patternTupleEquiv r h ((h+1:ℕ):ℤ))
  intro b
  have he := patternTupleEquiv_labels r h (h+1) b
  simp only [he]

theorem separatedOffsets_eventually {lam : ℝ} (hlam : 0<lam) (s : ℕ) :
    ∀ᶠ X : ℕ in atTop,∀ j,separatedOffsets s (blockLength lam X) j≤2*blockLength lam X := by
  filter_upwards [blockOffset_eventually hlam] with X hX j
  cases j using Fin.lastCases with
  | last => simp only [separatedOffsets,Fin.snoc_last]; omega
  | cast j => simpa only [separatedOffsets,Fin.snoc_castSucc] using hX

theorem marked_pattern_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam) (r : Setoid (Fin n))
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (F v.ofLp:ℂ)))
    (M : ℝ) (hM : 0≤M) (hbound : ∀ v, (∀ i,0≤v i) → |F v|≤M) :
    Tendsto (fun X : ℕ => ∑ b∈patternClass (α:=Fin (blockLength lam X)) r,∑ c : Fin (blockLength lam X),
      (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
        theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) atTop
      (𝓝 ((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) hF hFs)
        (shiftFamily (fun i => (numericPattern r i:ℤ))))) := by
  have hh := marked_box_pattern_limit hBV hlam (patternLabels r) (patternLabels_surjective r)
    (fun X => separatedOffsets _ (blockLength lam X)) (separatedOffsets_eventually hlam _)
    F rho hrho hrhohalf hbudget hF hFs M hM hbound
  apply hh.congr'
  exact Eventually.of_forall fun X => (pattern_marked_sum_eq_box r _ X F).symm

noncomputable def orderedDetector (X h m : ℕ) : ℝ :=
  (∑ c : Fin h,theta (m+(1+(c:ℕ))))/Real.log X

theorem average_div (X : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    average X (fun m => f m/a)=average X f/a := by
  simpa only [div_eq_mul_inv,mul_comm] using average_const_mul X a⁻¹ f

theorem markedBlock_average_expansion {n X h : ℕ}
    (F : (Fin n → ℝ) → ℝ) (k : Setoid (Fin n) → ℝ) :
    (average X (fun m => weightedBlock X h (h+1) F k m*orderedDetector X h m):ℂ)=
      ∑ b : Fin n → Fin h,(k (Setoid.ker b):ℂ)*∑ c : Fin h,
        (average X (fun m => divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
  classical
  have he (m : ℕ) : weightedBlock X h (h+1) F k m*orderedDetector X h m=
      ∑ b : Fin n → Fin h,∑ c : Fin h,
        k (Setoid.ker b)*(divisorSum X F m (fun i => h+1+(b i:ℕ))*theta (m+(1+(c:ℕ))))/Real.log X := by
    unfold weightedBlock orderedDetector
    rw [←mul_div_assoc,Finset.sum_mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    rw [mul_assoc]
  simp only [he,average_finset_sum,average_div,average_const_mul,
    Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum,mul_div_assoc]

theorem markedBlock_average_limit (hBV : BombieriVinogradov) {n : ℕ}
    {lam : ℝ} (hlam : 0<lam)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ)
    (hrho : 0≤rho) (hrhohalf : rho<1/2) (hbudget : HasBudget F rho)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (k : Setoid (Fin n) → ℝ) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) F k m*
        orderedDetector X (blockLength lam X) m):ℂ)) atTop
      (𝓝 (∑ r : Setoid (Fin n),(k r:ℂ)*((lam:ℂ)^(Fintype.card (Quotient r)+1)*kernelConstant
        (sourceFourier (fourierCoordinateSum (Fin n))
          (fun v => (F v.ofLp:ℂ)) (realEuclidean_compact F hF) (realEuclidean_smooth F hFs))
        (equalityPatternFamily r)))) := by
  classical
  obtain ⟨M,hM⟩ := hFs.continuous.bounded_above_of_compact_support hF
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    (marked_pattern_limit hBV hlam r F rho hrho hrhohalf hbudget
      (realEuclidean_compact F hF) (realEuclidean_smooth F hFs) M
      ((norm_nonneg (F 0)).trans (hM 0)) (fun v _ => by simpa only [Real.norm_eq_abs] using hM v)).const_mul (k r:ℂ))
  apply hh.congr'
  exact Eventually.of_forall (fun X => by
    dsimp only
    rw [markedBlock_average_expansion]
    calc
      (∑ r : Setoid (Fin n), (k r:ℂ)*∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
        ∑ c : Fin (blockLength lam X),
        (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
          theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ)) =
        ∑ r : Setoid (Fin n),∑ b∈patternClass (α:=Fin (blockLength lam X)) r,
          (k (Setoid.ker b):ℂ)*∑ c : Fin (blockLength lam X),
            (average X (fun m => divisorSum X F m (fun i => blockLength lam X+1+(b i:ℕ))*
              theta (m+(1+(c:ℕ)))):ℂ)/(Real.log X:ℂ) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(mem_patternClass r b).mp hb]
      _ = _ := sum_patterns _
    apply Finset.sum_congr (by ext b; simp)
    intro b _
    rfl)

theorem marked_cumulative_pair_limit (hBV : BombieriVinogradov) {n p : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => (average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m*
      orderedDetector X (blockLength lam X) m):ℂ))
      atTop (𝓝 ((lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) := by
  have hh := markedBlock_average_limit hBV hlam
    (cumulativeProfile (tau+tau) (tensorProfile f g)) (tau+tau) (by positivity) (by linarith)
    (cumulativeProfile_budget _ _ (tensorProfile_tsupport f g hsf hsg))
    (cumulativeProfile_compact _ _ (tensorProfile_compact f g hf hg))
    (cumulativeProfile_smooth _ _ (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs))
    (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p))
  have he : (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))=
      (lam:ℂ)*∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^Fintype.card (Quotient r)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  change Tendsto _ _ (𝓝 (∑ r : Setoid (Fin (n+p)),
      (tensorCoefficient (subsetCoefficient n) (subsetCoefficient p) r:ℂ)*
        ((lam:ℂ)^(Fintype.card (Quotient r)+1)*cumulativePatternKernel (tau+tau) (tensorProfile f g)
          (tensorProfile_compact f g hf hg) (tensorProfile_smooth f g hfs hgs) r))) at hh
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  congr 2
  funext m
  rw [weightedBlock_cumulative_mul hX _ _ m f g hsf hsg _ _]

theorem marked_cumulative_square_limit (hBV : BombieriVinogradov) {n : ℕ} {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsym : SymmetricFunction f) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m^2*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 (lam*alpha lam n*l2Mass f)) := by
  have hh := marked_cumulative_pair_limit hBV htau htau2 hlam f f hf hf hfs hfs hsf hsf
  rw [cumulative_square_pattern_sum lam f hf hfs hsf hsym] at hh
  have hh' := Complex.continuous_re.continuousAt.tendsto.comp hh
  simpa [Function.comp_def,Complex.mul_re,←pow_two,mul_assoc] using hh'

theorem marked_cumulative_cross_limit (hBV : BombieriVinogradov) {n p : ℕ} (hnp : n≠p) {tau lam : ℝ}
    (htau : 0≤tau) (htau2 : 2*tau<1/2) (hlam : 0<lam)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin p → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hsf : tsupport f⊆positiveSimplex n tau) (hsg : tsupport g⊆positiveSimplex p tau) :
    Tendsto (fun X : ℕ => average X (fun m =>
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau f) (subsetCoefficient n) m*
      weightedBlock X (blockLength lam X) (blockLength lam X+1) (cumulativeProfile tau g) (subsetCoefficient p) m*
      orderedDetector X (blockLength lam X) m))
      atTop (𝓝 0) := by
  have hh := marked_cumulative_pair_limit hBV htau htau2 hlam f g hf hg hfs hgs hsf hsg
  rw [cumulative_cross_pattern_sum hnp lam f g hf hg hfs hgs hsf hsg,mul_zero] at hh
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

end LargePrimeGaps

end OAI
