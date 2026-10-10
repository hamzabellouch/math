import OAI.Probability.FKMaps.SpineMoments

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

lemma incrementWord_sum (l : List ℕ) : (incrementWord l).sum=(l.sum:ℤ)-l.length := by
  induction l with
  | nil => simp [incrementWord]
  | cons k l ih =>
    simp only [incrementWord,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at *
    omega

lemma degrees_sum (t : PlaneTree) : t.degrees.sum+1=t.degrees.length := by
  have hh := t.degrees_excursion.1
  rw [incrementWord_sum] at hh
  omega

lemma degree_lt_length (t : PlaneTree) {k : ℕ} (hk : k∈t.degrees) : k<t.degrees.length := by
  have := List.le_sum_of_mem hk
  have := t.degrees_sum
  omega

def toCode (t : PlaneTree) : Code t.degrees.length :=
  ⟨fun i => ⟨t.degrees[i],t.degree_lt_length (List.getElem_mem _)⟩,by
    rw [isTreeCode_iff]
    convert t.degrees_excursion using 1
    unfold degreeList incrementWord
    exact List.ofFn_getElem_eq_map t.degrees (fun k : ℕ => (k:ℤ)-1)⟩

lemma toCode_degrees_ofFn (t : PlaneTree) :
    List.ofFn (fun i => ((t.toCode.val i).val))=t.degrees := by
  exact List.ofFn_getElem

lemma incrementWord_ofFn {N : ℕ} (d : Fin N → Fin N) :
    incrementWord (List.ofFn (fun i => (d i).val))=degreeList d := by
  simp only [incrementWord,List.map_ofFn,degreeList,Function.comp_def]

def ofCode {N : ℕ} (d : Code N) : PlaneTree :=
  Classical.choose (exists_tree_of_excursion (l := List.ofFn (fun i => (d.val i).val))
    (by rw [incrementWord_ofFn]; exact (isTreeCode_iff _).mp d.property))

lemma ofCode_degrees {N : ℕ} (d : Code N) :
    (ofCode d).degrees=List.ofFn (fun i => (d.val i).val) :=
  Classical.choose_spec (exists_tree_of_excursion (l := List.ofFn (fun i => (d.val i).val))
    (by rw [incrementWord_ofFn]; exact (isTreeCode_iff _).mp d.property))

lemma ofCode_size {N : ℕ} (d : Code N) : (ofCode d).degrees.length=N := by
  rw [ofCode_degrees,List.length_ofFn]

lemma ofCode_injective (N : ℕ) : Function.Injective (@ofCode N) := by
  intro d e h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he := congrArg degrees h
  rw [ofCode_degrees,ofCode_degrees] at he
  have he' := congrArg (fun l : List ℕ => l[i.val]?) he
  simpa using he'

lemma ofCode_toCode (t : PlaneTree) : ofCode t.toCode=t := by
  apply degrees_injective
  rw [ofCode_degrees,toCode_degrees_ofFn]

abbrev Sized (N : ℕ) := {t : PlaneTree // t.degrees.length=N}

def sizedEquiv (N : ℕ) : Code N ≃ Sized N := Equiv.ofBijective
  (fun d => ⟨ofCode d,ofCode_size d⟩) ⟨fun d e h => ofCode_injective N (congrArg Subtype.val h),by
    rintro ⟨t,ht⟩
    subst N
    exact ⟨t.toCode,Subtype.ext (ofCode_toCode t)⟩⟩

def mirrored {N : ℕ} (d : Code N) : Code N :=
  (sizedEquiv N).symm ⟨(ofCode d).mirror,(ofCode d).mirror_size.trans (ofCode_size d)⟩

lemma ofCode_mirrored {N : ℕ} (d : Code N) : ofCode (mirrored d)=(ofCode d).mirror := by
  exact congrArg Subtype.val ((sizedEquiv N).apply_symm_apply _)

lemma mirrored_involutive (N : ℕ) : Function.Involutive (@mirrored N) := by
  intro d
  apply ofCode_injective N
  rw [ofCode_mirrored,ofCode_mirrored,mirror_mirror]

def mirrorEquiv (N : ℕ) : Equiv.Perm (Code N) := (mirrored_involutive N).toPerm

lemma codeWeight_ofCode {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    ((ofCode d).degrees.map p.mass).prod=codeWeight p d := by
  rw [ofCode_degrees,List.map_ofFn,List.prod_ofFn]
  rfl

lemma mirrored_weight {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    codeWeight p (mirrored d)=codeWeight p d := by
  rw [← codeWeight_ofCode,ofCode_mirrored,mirror_weight,codeWeight_ofCode]

lemma mirrorEquiv_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (mirrorEquiv (2*n+1)) (p.codeLaw n) (p.codeLaw n) := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (mirrorEquiv (2*n+1)) ⁻¹' {d}={mirrored d} := by
    ext x
    change mirrored x=d ↔ x=mirrored d
    constructor
    · intro h
      rw [← h,mirrored_involutive]
    · rintro rfl
      exact mirrored_involutive _ _
  rw [he]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (p.codeLaw n).real {mirrored d}=(p.codeLaw n).real {d}
  rw [← integral_indicator_one (measurableSet_singleton _),
    ← integral_indicator_one (measurableSet_singleton _),p.code_integral,p.code_integral]
  simp only [Set.indicator,Set.mem_singleton_iff]
  simp [mirrored_weight]

end PlaneTree
end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma recordSpineSum_extend (b : ℕ×ℕ → ℝ) (x y : ℕ → ℕ) {n m : ℕ} (hnm : n ≤ m)
    (hxy : ∀ k < n,x k=y k)
    (hmax : ∀ k ≤ n,integerSum x k ≤ integerSum x n)
    (hmid : ∀ k,n < k → k ≤ m → integerSum y k < integerSum x n)
    (hfin : integerSum x n ≤ integerSum y (m+1)) :
    recordSpineSum b y (m+1)=recordSpineSum b x n+
      b (y m,(integerSum y (m+1)-integerSum x n).toNat) := by
  have hS (k) (hk : k ≤ n) : integerSum x k=integerSum y k := integerSum_congr_prefix hxy k hk
  have hmaxy (k) (hk : k ≤ m) : integerSum y k ≤ integerSum x n := by
    by_cases hkn : k ≤ n
    · rw [← hS k hkn]; exact hmax k hkn
    · exact (hmid k (by omega) hk).le
  have hrecords : weakRecords (integerSum y) (m+1)=
      insert (m+1) (weakRecords (integerSum y) n) := by
    ext k
    simp only [mem_weakRecords,Finset.mem_insert]
    constructor
    · rintro ⟨hk0,hkm,hrec⟩
      by_cases hkn : k ≤ n
      · exact Or.inr ⟨hk0,hkn,hrec⟩
      · left
        by_contra he
        have hh := hrec n (by omega)
        rw [← hS n le_rfl] at hh
        have := hmid k (by omega) (by omega)
        omega
    · rintro (rfl | ⟨hk0,hkn,hrec⟩)
      · refine ⟨by omega,le_rfl,?_⟩
        intro j hj
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · rfl
        · exact (hmaxy j (by omega)).trans hfin
      · exact ⟨hk0,hkn.trans (by omega),hrec⟩
  have hp : prefixMaximum (integerSum y) m=integerSum x n := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun k hk => hmaxy k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    · rw [hS n le_rfl]
      exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))
  unfold recordSpineSum
  rw [hrecords,Finset.sum_insert (by
    intro h
    have := (mem_weakRecords _ _ _).mp h
    omega)]
  rw [show recordTypeAt y (m+1)=(y m,(integerSum y (m+1)-integerSum x n).toNat) by
    simp only [recordTypeAt,Nat.add_sub_cancel,hp]]
  rw [add_comm]
  congr 1
  exact recordSpineSum_congr_prefix (fun k hk => (hxy k hk).symm) b

def listStream (l : List ℕ) (k : ℕ) : ℕ := l[k]?.getD 0

lemma listStream_get {l : List ℕ} {k : ℕ} (hk : k < l.length) : listStream l k=l[k] := by
  simp [listStream,List.getElem?_eq_getElem hk]

lemma integerSum_listStream (l : List ℕ) {k : ℕ} (hk : k ≤ l.length) :
    integerSum (listStream l) k=prefixSum (PlaneTree.incrementWord l) k := by
  induction k with
  | zero => simp [prefixSum]
  | succ k ih =>
    rw [integerSum_succ,ih (by omega),listStream_get (by omega)]
    unfold prefixSum
    rw [List.take_succ_eq_append_getElem (by simpa [PlaneTree.incrementWord] using (show k < l.length by omega)),List.sum_append]
    simp only [PlaneTree.incrementWord,List.getElem_map,List.sum_cons,List.sum_nil,add_zero]
    omega

lemma integerSum_listStream_length (l : List ℕ) :
    integerSum (listStream l) l.length=(PlaneTree.incrementWord l).sum := by
  rw [integerSum_listStream l le_rfl,prefixSum,List.take_of_length_le (by simp [PlaneTree.incrementWord])]

lemma listStream_append_prefix (l r : List ℕ) : ∀ k < l.length,listStream (l++r) k=listStream l k := by
  intro k hk
  simp [listStream,List.getElem?_append_left hk]

lemma prefixSum_reverse_nat (l : List ℕ) {j : ℕ} (_hj : j ≤ l.length) :
    prefixSum (PlaneTree.incrementWord l.reverse) j=
      (PlaneTree.incrementWord l).sum-prefixSum (PlaneTree.incrementWord l) (l.length-j) := by
  rw [PlaneTree.incrementWord,List.map_reverse,prefixSum]
  rw [List.take_reverse,List.sum_reverse]
  change ((PlaneTree.incrementWord l).drop _).sum=_
  rw [sum_drop]
  simp [PlaneTree.incrementWord]

lemma list_reverse_prefix_max (l : List ℕ) (h : ∀ j ≤ l.length,0 ≤ prefixSum (PlaneTree.incrementWord l) j) :
    ∀ j ≤ l.length,integerSum (listStream l.reverse) j ≤ integerSum (listStream l.reverse) l.length := by
  intro j hj
  rw [integerSum_listStream _ (by simpa using hj),prefixSum_reverse_nat l hj,
    integerSum_listStream _ (by simp),prefixSum_reverse_nat l le_rfl]
  simp only [Nat.sub_self,prefixSum,List.take_zero,List.sum_nil,sub_zero]
  exact sub_le_self _ (h _ (by omega))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma record_count_reverse (x : ℕ → ℕ) (v : ℕ) :
    (weakRecords (integerSum (reverseFirst v x)) v).card=recordHeight (integerSum x) 0 v := by
  rw [recordHeight_dual,Nat.sub_zero]
  congr 1
  exact weakRecords_congr_prefix (fun k hk => integerSum_reverseFirst x v k hk)

lemma CriticalEvenOffspring.record_spine_bound (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (N K : ℕ) {r : ℝ} (hr : 0<r) :
    p.streamLaw.real {x | ∃ v≤N,
      (weakRecords (integerSum (reverseFirst v x)) v).card≤K ∧
      r≤|recordSpineSum b (reverseFirst v x) v-
        (∫ z,b z ∂p.spineLaw)*(weakRecords (integerSum (reverseFirst v x)) v).card|} ≤
      (N+1:ℝ)*K*2*Real.exp (-r^2/(2*K*((d-a)/2)^2)) := by
  let E : ℕ → Set (ℕ → ℕ) := fun h => {x | r≤|∑ i∈Finset.range h,
    (b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw)|}
  have hE (h) : MeasurableSet (E h) := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_of_countable b).comp (measurable_ladderType.comp
      (measurable_ladderTail.iterate i))).sub measurable_const
  let A : Fin (N+1) → Fin K → Set (ℕ → ℕ) := fun v h => reverseFirst v.val ⁻¹' E (h.val+1)
  have hsub : ∀ᵐ x ∂p.streamLaw,
      (∃ v≤N,(weakRecords (integerSum (reverseFirst v x)) v).card≤K ∧
        r≤|recordSpineSum b (reverseFirst v x) v-
          (∫ z,b z ∂p.spineLaw)*(weakRecords (integerSum (reverseFirst v x)) v).card|) →
        x∈⋃ v,⋃ h,A v h := by
    filter_upwards [p.ae_reverse_ladders] with x hx
    rintro ⟨v,hv,hK,hbad⟩
    have hen := ladderTime_enumeration (hx v)
    rw [recordSpineSum_eq (hx v),hen.card_records] at hbad
    rw [hen.card_records] at hK
    let h := renewalCount (ladderTime (reverseFirst v x)) v
    have hh0 : 0<h := by
      by_contra hn
      have he : h=0 := by omega
      change r≤|(∑ i∈Finset.range h,b (ladderType (ladderTail^[i] (reverseFirst v x)))) -
        (∫ z,b z ∂p.spineLaw)*h| at hbad
      simp only [he,Finset.range_zero,Finset.sum_empty,Nat.cast_zero,mul_zero,sub_self,abs_zero] at hbad
      exact hr.not_ge hbad
    apply Set.mem_iUnion.mpr
    refine ⟨⟨v,by omega⟩,Set.mem_iUnion.mpr ⟨⟨h-1,by change h≤K at hK; omega⟩,?_⟩⟩
    change reverseFirst v x∈E (h-1+1)
    rw [Nat.sub_add_cancel hh0]
    change r≤|∑ i∈Finset.range h,(b (ladderType (ladderTail^[i] (reverseFirst v x)))-_)|
    simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm] using hbad
  have hu := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  change _≤p.streamLaw.real (⋃ v,⋃ h,A v h) at hu
  apply hu.trans
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    ∑ v : Fin (N+1),p.streamLaw.real (⋃ h,A v h) ≤
        ∑ _v : Fin (N+1),∑ _h : Fin K,2*Real.exp (-r^2/(2*K*((d-a)/2)^2)) := by
      apply Finset.sum_le_sum
      intro v _
      apply (measureReal_iUnion_fintype_le _).trans
      apply Finset.sum_le_sum
      intro h _
      have hm : p.streamLaw.real (A v h)=p.streamLaw.real (E (h.val+1)) :=
        (reverseFirst_preserving p v.val).measureReal_preimage (hE _).nullMeasurableSet
      rw [hm]
      apply (p.spine_label_deviation b a d hb (h.val+1) r hr.le).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hk : (h.val+1:ℝ)≤K := by exact_mod_cast Nat.succ_le_iff.mpr h.isLt
      have hc2 := sq_nonneg ((d-a)/2)
      by_cases hzero : ((d-a)/2)^2=0
      · simp only [hzero,mul_zero,div_zero,le_refl]
      · have hc : 0<((d-a)/2)^2 := lt_of_le_of_ne hc2 (Ne.symm hzero)
        simp only [neg_div,Nat.cast_add,Nat.cast_one]
        apply neg_le_neg
        change r^2/(2*K*((d-a)/2)^2)≤r^2/(2*(h.val+1)*((d-a)/2)^2)
        exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) (by nlinarith)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; ring

/-- The exact deterministic ancestral statistic at preorder position v. -/
def codeSpineSum {N : ℕ} (b : ℕ×ℕ → ℝ) (d : Code N) (v : ℕ) : ℝ :=
  recordSpineSum b (reverseFirst v (arrayStream (codeEmbedding N d))) v

lemma reverseFirst_prefix_congr {x y : ℕ → ℕ} {N v : ℕ} (hv : v≤N)
    (h : ∀ k<N,x k=y k) : ∀ k<v,reverseFirst v x k=reverseFirst v y k := by
  intro k hk
  simp only [reverseFirst]
  simp only [reverseIndex,ite_eq_left hk]
  exact h _ (by omega)

lemma CriticalEvenOffspring.code_spine_bound (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (n K : ℕ) {r : ℝ} (hr : 0<r) :
    (p.codeLaw n).real {c | ∃ v≤2*n+1,height c.val v≤K ∧
      r≤|codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|} ≤
      ((2*n+1:ℕ)+1:ℝ)*K*2*Real.exp (-r^2/(2*K*((d-a)/2)^2))/codePartition p (2*n+1) := by
  apply (p.code_probability_le_stream n _ _ ?_).trans
  · exact div_le_div_of_nonneg_right (p.record_spine_bound b a d hb (2*n+1) K hr)
      (codePartition_nonneg p _)
  · rintro c ⟨v,hv,hK,hbad⟩ x hx
    have hp : ∀ k<2*n+1,x k=arrayStream (codeEmbedding (2*n+1) c) k := by
      intro k hk
      have := congrFun hx ⟨k,hk⟩
      simpa [streamPrefix,arrayStream,hk] using this
    have hS : ∀ k≤2*n+1,integerSum x k=walk c.val k := by
      intro k hk
      rw [integerSum_congr_prefix hp k hk]
      exact integerSum_arrayStream_bridge ⟨c.val,c.property.1⟩ hk
    have hh : (weakRecords (integerSum (reverseFirst v x)) v).card=height c.val v := by
      rw [record_count_reverse,recordHeight_congr_prefix hv hS,← height_eq_recordHeight c.val hv]
    refine ⟨v,hv,hh.symm ▸ hK,?_⟩
    rw [hh,recordSpineSum_congr_prefix (reverseFirst_prefix_congr hv hp)]
    exact hbad

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma integerSum_list_append (a b : List ℕ) {j : ℕ} (hj : j ≤ b.length) :
    integerSum (listStream (a++b)) (a.length+j)=
      (PlaneTree.incrementWord a).sum+integerSum (listStream b) j := by
  rw [integerSum_listStream _ (by simpa using hj),integerSum_listStream _ hj,
    PlaneTree.incrementWord_append]
  unfold prefixSum
  rw [List.take_append,List.sum_append]
  simp only [PlaneTree.incrementWord,List.length_map,Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (by simp only [List.length_map]; omega)]

lemma reverse_word_strict_negative (l : List ℕ) (h : PlaneTree.SuffixNegative l)
    {j : ℕ} (hj : 0 < j) (hjl : j ≤ l.length) :
    integerSum (listStream l.reverse) j < 0 := by
  rw [integerSum_listStream _ (by simpa using hjl),prefixSum_reverse_nat l hjl]
  have hh := h (l.length-j) (by omega)
  rw [PlaneTree.incrementWord,List.map_drop,sum_drop] at hh
  exact hh

/-- Sum of the genuine ancestral record types of a finite preorder prefix. -/
def profileSum (b : ℕ×ℕ → ℝ) (l : List ℕ) : ℝ :=
  recordSpineSum b (listStream l.reverse) l.length

lemma profileSum_empty (b : ℕ×ℕ → ℝ) : profileSum b []=0 := by
  simp [profileSum,recordSpineSum,weakRecords]

lemma profileSum_attach (b : ℕ×ℕ → ℝ) (a f : List ℕ) {i k : ℕ}
    (ha : ∀ j ≤ a.length,0 ≤ prefixSum (PlaneTree.incrementWord a) j)
    (hf : PlaneTree.SuffixNegative f) (hfs : (PlaneTree.incrementWord f).sum= -(i:ℤ))
    (hik : i < k) :
    profileSum b (k::(f++a))=profileSum b a+b (k,k-1-i) := by
  let x := listStream a.reverse
  let y := listStream ((a.reverse++f.reverse)++[k])
  let n := a.length
  let m := a.length+f.length
  have hp : ∀ j < n,x j=y j := by
    intro j hj
    dsimp [x,y,n] at *
    rw [List.append_assoc]
    exact (listStream_append_prefix a.reverse (f.reverse++[k]) j (by simpa using hj)).symm
  have hS : integerSum x n=(PlaneTree.incrementWord a).sum := by
    dsimp [x,n]
    convert integerSum_listStream_length a.reverse using 1
    · simp
    · simp [PlaneTree.incrementWord]
  have hm : ∀ j ≤ m,integerSum y j=integerSum (listStream (a.reverse++f.reverse)) j := by
    intro j hj
    apply integerSum_congr_prefix (N := m) _ j hj
    intro r hr
    exact listStream_append_prefix (a.reverse++f.reverse) [k] r (by simpa [m] using hr)
  have hmid : ∀ j,n < j → j ≤ m → integerSum y j < integerSum x n := by
    intro j hj hjm
    rw [hm j hjm]
    have hsub : j-n ≤ f.reverse.length := by simp only [List.length_reverse]; dsimp [m,n] at *; omega
    have he : j=a.reverse.length+(j-n) := by dsimp [n] at *; simp only [List.length_reverse]; omega
    rw [he,integerSum_list_append _ _ hsub]
    rw [show (PlaneTree.incrementWord a.reverse).sum=(PlaneTree.incrementWord a).sum by simp [PlaneTree.incrementWord],hS]
    exact add_lt_of_neg_right _ (reverse_word_strict_negative f hf (by omega) (by simpa using hsub))
  have hfinal : integerSum y (m+1)=integerSum x n+((k:ℤ)-1-i) := by
    dsimp [y,m]
    have he : a.length+f.length+1=(((a.reverse++f.reverse)++[k])).length := by simp [Nat.add_assoc]
    rw [he,integerSum_listStream_length,PlaneTree.incrementWord_append,PlaneTree.incrementWord_append]
    simp only [List.sum_append,PlaneTree.incrementWord,List.map_reverse,List.sum_reverse,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [hS]
    unfold PlaneTree.incrementWord
    unfold PlaneTree.incrementWord at hfs
    rw [hfs]
    omega
  have hy : y m=k := by
    dsimp [y,m]
    rw [listStream_get (by simp),List.getElem_append_right (by simp)]
    simp
  have ht := recordSpineSum_extend b x y (by dsimp [n,m]; omega) hp
    (list_reverse_prefix_max a ha) hmid (by rw [hfinal]; omega)
  rw [hy,hfinal,show (integerSum x n+((k:ℤ)-1-i)-integerSum x n).toNat=k-1-i by omega] at ht
  simpa only [profileSum,List.reverse_cons,List.reverse_append,List.length_cons,List.length_append,
    add_comm f.length a.length,x,y,n,m] using ht

lemma reverseFirst_list_prefix (l : List ℕ) {v : ℕ} (hv : v ≤ l.length) :
    ∀ k < v,reverseFirst v (listStream l) k=listStream (l.take v).reverse k := by
  intro k hk
  simp only [reverseFirst,reverseIndex,ite_eq_left hk]
  rw [listStream_get (by omega),listStream_get (by simp only [List.length_reverse,List.length_take]; omega),List.getElem_reverse]
  simp only [List.length_take,Nat.min_eq_left hv]
  rw [List.getElem_take]

lemma code_profileSum {N : ℕ} (d : Code N) (b : ℕ×ℕ → ℝ) {v : ℕ} (hv : v ≤ N) :
    codeSpineSum b d v=profileSum b ((PlaneTree.ofCode d).degrees.take v) := by
  rw [PlaneTree.ofCode_degrees]
  let l := List.ofFn (fun i => (d.val i).val)
  have hx : ∀ k < N,arrayStream (codeEmbedding N d) k=listStream l k := by
    intro k hk
    rw [listStream_get (by simpa [l] using hk)]
    simp only [arrayStream,dite_eq_left hk,l,List.getElem_ofFn]
    rfl
  have hrev := reverseFirst_prefix_congr hv hx
  have hlt : (l.take v).length=v := by simp [l,Nat.min_eq_left hv]
  unfold codeSpineSum profileSum
  change recordSpineSum b (reverseFirst v _) v=recordSpineSum b (listStream (l.take v).reverse) _
  rw [hlt]
  apply recordSpineSum_congr_prefix
  intro k hk
  exact (hrev k hk).trans (reverseFirst_list_prefix l (by simpa [l] using hv) k hk)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
namespace PlaneTree

lemma forest_properties (fs : List PlaneTree) :
    (incrementWord (forestDegrees fs)).sum= -(fs.length:ℤ) ∧ SuffixNegative (forestDegrees fs) := by
  induction fs with
  | nil => simp [forestDegrees,incrementWord,SuffixNegative]
  | cons f fs ih =>
    have hp := f.degrees_properties
    change (incrementWord (f.degrees++forestDegrees fs)).sum= -((f::fs).length:ℤ) ∧ _
    constructor
    · rw [incrementWord_append,List.sum_append,hp.1,ih.1]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; omega
    · change SuffixNegative (f.degrees++forestDegrees fs)
      exact suffixNegative_append hp.2 ih.2 (by rw [ih.1]; omega)

lemma forest_split_index (fs : List PlaneTree) {v : ℕ} (hv : v<(forestDegrees fs).length) :
    ∃ pre t post j,fs=pre++t::post ∧ j<t.degrees.length ∧ v=(forestDegrees pre).length+j := by
  induction fs generalizing v with
  | nil => simp [forestDegrees] at hv
  | cons t fs ih =>
    by_cases hvt : v<t.degrees.length
    · exact ⟨[],t,fs,v,rfl,hvt,by simp [forestDegrees]⟩
    · obtain ⟨pre,s,post,j,he,hj,hv'⟩ := ih (v := v-t.degrees.length) (by
        simp only [forestDegrees,List.flatMap_cons,List.length_append] at hv ⊢; omega)
      refine ⟨t::pre,s,post,j,by simp [he],hj,?_⟩
      simp only [forestDegrees,List.flatMap_cons,List.length_append] at hv' ⊢
      omega

/-- Literal ancestor offspring/slot list of a preorder vertex. Slot counts siblings to its right. -/
inductive Profile : PlaneTree → ℕ → List (ℕ×ℕ) → Prop
  | root (t) : Profile t 0 []
  | child (pre : List PlaneTree) (t : PlaneTree) (post : List PlaneTree) {v a}
      (h : Profile t v a) :
      Profile (node (pre++t::post)) (1+(forestDegrees pre).length+v)
        (((pre++t::post).length,post.length)::a)

lemma Profile.bound {t v a} (h : Profile t v a) : v<t.degrees.length := by
  induction h with
  | root t => exact List.length_pos_iff.mpr t.degrees_nonempty
  | @child pre t post v a h ih =>
    simp only [degrees,List.flatMap_append,List.flatMap_cons,List.length_cons,List.length_append]
    simp only [forestDegrees] at *
    omega

lemma exists_profile (t : PlaneTree) {v : ℕ} (hv : v<t.degrees.length) : ∃ a,Profile t v a := by
  induction t using inductionMem generalizing v with
  | hn fs ih =>
    by_cases hv0 : v=0
    · subst v; exact ⟨[],Profile.root _⟩
    · obtain ⟨pre,t,post,j,hfs,hj,hvj⟩ := forest_split_index fs (v := v-1) (by
        simpa only [degrees,List.length_cons,forestDegrees] using (show v-1<(fs.flatMap degrees).length by
          simp only [degrees,List.length_cons] at hv; omega))
      obtain ⟨a,ha⟩ := ih t (by rw [hfs]; simp) hj
      refine ⟨((pre++t::post).length,post.length)::a,?_⟩
      rw [hfs,show v=1+(forestDegrees pre).length+j by omega]
      exact Profile.child pre t post ha

lemma degrees_take_child (pre : List PlaneTree) (t : PlaneTree) (post : List PlaneTree)
    {v : ℕ} (hv : v≤t.degrees.length) :
    (node (pre++t::post)).degrees.take (1+(forestDegrees pre).length+v)=
      (pre++t::post).length::(forestDegrees pre++t.degrees.take v) := by
  simp only [degrees,List.flatMap_append,List.flatMap_cons]
  rw [show 1+(forestDegrees pre).length+v=((forestDegrees pre).length+v)+1 by omega,
    List.take_succ_cons]
  rw [List.take_append]
  congr 1
  change (List.take ((forestDegrees pre).length+v) (forestDegrees pre) ++
    List.take (((forestDegrees pre).length+v)-(forestDegrees pre).length) (t.degrees++forestDegrees post)) = _
  rw [List.take_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.take_append_of_le_length hv]

lemma Profile.spineSum {t v a} (h : Profile t v a) (b : ℕ×ℕ → ℝ) :
    profileSum b (t.degrees.take v)=(a.map b).sum := by
  induction h with
  | root t => simp [profileSum_empty]
  | @child pre t post v a h ih =>
    rw [degrees_take_child pre t post h.bound.le]
    have hp := forest_properties pre
    have ht := t.degrees_excursion.2
    have ha : ∀ j≤(t.degrees.take v).length,0≤prefixSum (incrementWord (t.degrees.take v)) j := by
      intro j hj
      rw [incrementWord,List.map_take,prefixSum,List.take_take]
      have hjv : j≤v := hj.trans (List.length_take_le _ _)
      rw [Nat.min_eq_left hjv]
      apply ht j
      simpa [incrementWord] using (hjv.trans_lt h.bound)
    rw [profileSum_attach b _ _ ha hp.2 hp.1 (by simp)]
    rw [ih]
    simp only [List.length_append,List.length_cons,List.map_cons,List.sum_cons]
    rw [add_comm]
    congr 2
    apply Prod.ext
    · rfl
    · dsimp; omega

 def flipSlot (z : ℕ×ℕ) : ℕ×ℕ := (z.1,z.1-1-z.2)

lemma Profile.slots {t v a} (h : Profile t v a) : ∀ z∈a,z.2<z.1 := by
  induction h with
  | root _ => simp
  | @child pre t post v a h ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · simp; omega
    · exact ih z hz

lemma Profile.mirrored {t v a} (h : Profile t v a) :
    ∃ w,Profile t.mirror w (a.map flipSlot) := by
  induction h with
  | root t => exact ⟨0,by simpa using Profile.root t.mirror⟩
  | @child pre t post v a h ih =>
    obtain ⟨w,hw⟩ := ih
    refine ⟨1+(forestDegrees (post.reverse.map mirror)).length+w,?_⟩
    have hh := Profile.child (post.reverse.map mirror) t.mirror (pre.reverse.map mirror) hw
    simpa [mirror,List.reverse_append,List.map_append,List.reverse_cons,List.append_assoc,
      flipSlot,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

end PlaneTree
end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma distribution_norm_tight {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Ω : ℕ → Type*} {Ω' : Type*} [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Y : Ω' → E} (h : TendstoInDistribution X atTop Y μ ν)
    (hm : ∀ n,Measurable (X n)) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(μ n).real {x | C<‖X n x‖}≤η := by
  let G : ℕ → E → ℝ := fun j z => min 1 (‖z‖/(j+1:ℝ))
  have hG (j) : Continuous (G j) := continuous_const.min (continuous_norm.div_const _)
  have hG0 (j z) : 0≤G j z := le_min (by norm_num) (by positivity)
  have hG1 (j z) : |G j z|≤1 := by rw [abs_of_nonneg (hG0 j z)]; exact min_le_left _ _
  have ht : Tendsto (fun j : ℕ => ∫ x,G j (Y x) ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω' => (1:ℝ))
      (F := fun j x => G j (Y x)) (f := fun _ =>0)
      (fun j => ((hG j).measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable)
      (integrable_const _) (fun j => ae_of_all ν (fun z => hG1 j (Y z))) (by
        apply ae_of_all
        intro z
        have hh : Tendsto (fun j : ℕ => ‖Y z‖/(j+1:ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa only [G,min_eq_right (by norm_num : (0:ℝ)≤1)] using
          (tendsto_const_nhds.min hh (f := fun _ : ℕ => (1:ℝ))))
    simpa only [integral_zero] using hh
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds (half_pos hη))).exists
  have hx := integral_tendsto_of_tendstoInDistribution h (hG j) (hG1 j)
  refine ⟨j+1,by positivity,?_⟩
  filter_upwards [hx.eventually (gt_mem_nhds (hj.trans (half_lt_self hη)))] with n hn
  apply le_of_lt (lt_of_le_of_lt ?_ hn)
  let A := {x : Ω n | (j+1:ℝ)<‖X n x‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hm n).norm
  rw [← integral_indicator_one hA]
  have hi : Integrable (fun x => G j (X n x)) (μ n) :=
    Integrable.of_bound ((hG j).measurable.comp (hm n)).aestronglyMeasurable 1
      (ae_of_all _ (fun x => hG1 j (X n x)))
  apply integral_mono ((integrable_const (1:ℝ)).indicator hA) hi
  intro x
  by_cases hx : x∈A
  · rw [Set.indicator_of_mem hx]
    exact le_min le_rfl ((le_div_iff₀ (by positivity : (0:ℝ)<j+1)).mpr (by simpa using hx.le))
  · rw [Set.indicator_of_notMem hx]
    exact hG0 j _

local instance : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

lemma code_height_le_norm {N : ℕ} (hN : 0<N) (p : CriticalEvenOffspring) (d : Code N)
    {v : ℕ} (hv : v≤N) :
    (height d.val v:ℝ)≤(2/p.sigma)*Real.sqrt (N:ℝ)*‖jointCode p.sigma d‖ := by
  have hσ := p.sigma_pos
  have h := ContinuousMap.norm_coe_le_norm (jointCode p.sigma d) (gridPoint N ⟨v,by omega⟩)
  have he : (jointCode p.sigma d (gridPoint N ⟨v,by omega⟩)).2=
      p.sigma*height d.val v/(2*Real.sqrt N) := by
    change (interpolation N _ (gridPoint N ⟨v,by omega⟩))=_
    exact interpolation_gridPoint hN _ _
  have h2 : ‖(jointCode p.sigma d (gridPoint N ⟨v,by omega⟩)).2‖≤‖jointCode p.sigma d‖ :=
    (norm_snd_le _).trans h
  rw [he,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at h2
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hb := (div_le_iff₀ (by positivity : 0<2*Real.sqrt (N:ℝ))).mp h2
  have hg : (height d.val v:ℝ)*p.sigma ≤
      ((2/p.sigma)*Real.sqrt (N:ℝ)*‖jointCode p.sigma d‖)*p.sigma := by
    calc
      _ = p.sigma*(height d.val v:ℝ) := by ring
      _ ≤ ‖jointCode p.sigma d‖*(2*Real.sqrt N) := hb
      _ = _ := by field_simp
  exact (mul_le_mul_iff_left₀ p.sigma_pos).mp hg

lemma CriticalEvenOffspring.code_height_tight (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,
      (p.codeLaw n).real {d | ∃ v≤2*n+1,C*Real.sqrt ((2*n+1:ℕ):ℝ)<height d.val v}≤η := by
  have hσ := p.sigma_pos
  obtain ⟨C,hC,hlim⟩ := distribution_norm_tight (p.jointCode_vervaat_CLT hB)
    (fun _ => measurable_of_countable _) hη
  refine ⟨(2/p.sigma)*C,by positivity,?_⟩
  filter_upwards [hlim] with n hn
  apply (measureReal_mono ?_).trans hn
  rintro d ⟨v,hv,hbad⟩
  change C<‖jointCode p.sigma d‖
  have he := code_height_le_norm (by omega : 0<2*n+1) p d hv
  have hs : 0<Real.sqrt ((2*n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hc : 0<2/p.sigma := by positivity
  apply (mul_lt_mul_iff_right₀ (mul_pos hc hs)).mp
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hbad.trans_le he

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma polynomial_exp_sqrt {κ : ℝ} (hκ : 0<κ) (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.sqrt ((2*n+1:ℕ):ℝ))^k *
      Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (odd_sqrt_tendsto.const_mul_atTop hκ)).div_const (κ^k)
  simp only [zero_div] at h
  convert h using 1
  funext n
  simp only [Function.comp_apply,mul_pow,neg_mul]
  field_simp

lemma CriticalEvenOffspring.code_spine_exp_vanish (p : CriticalEvenOffspring)
    {κ : ℝ} (hκ : 0<κ) (C : ℝ) :
    Tendsto (fun n : ℕ => 2*(C+1)*(((2*n+1:ℕ):ℝ)+1)*Real.sqrt ((2*n+1:ℕ):ℝ)*
      Real.exp (-κ*Real.sqrt ((2*n+1:ℕ):ℝ))/codePartition p (2*n+1)) atTop (𝓝 0) := by
  have h := ((polynomial_exp_sqrt hκ 6).add (polynomial_exp_sqrt hκ 4)).const_mul (2*(C+1))
  have hpos : 0<2/(p.sigma*Real.sqrt (2*Real.pi)) :=
    div_pos (by norm_num) (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity)))
  have ht := h.div p.codePartition_asymptotic hpos.ne'
  simp only [zero_add,mul_zero,zero_div] at ht
  convert ht using 1
  funext n
  set s := Real.sqrt ((2*n+1:ℕ):ℝ)
  have hs : s^2=((2*n+1:ℕ):ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : s≠0 := (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne'
  have hsn : (2*n+1:ℝ)=s^2 := by rw [hs]; push_cast; rfl
  change _=2*(C+1)*(s^6*Real.exp (-κ*s)+s^4*Real.exp (-κ*s))/
    ((2*n+1:ℝ)*Real.sqrt (2*n+1)*codePartition p (2*n+1))
  rw [show Real.sqrt (2*n+1:ℝ)=s by congr 1; push_cast; rfl,hsn,← hs]
  field_simp

lemma spine_exp_ceiling_bound {C R ε s : ℝ} (hC : 0<C) (hR : 0<R)
    (hε : 0<ε) (hs : 1 ≤ s) :
    (⌈C*s⌉₊:ℝ)*2*Real.exp (-(ε*s)^2/(2*⌈C*s⌉₊*R^2)) ≤
      2*(C+1)*s*Real.exp (-(ε^2/(2*(C+1)*R^2))*s) := by
  have hs0 : 0<s := lt_of_lt_of_le zero_lt_one hs
  have hK : (⌈C*s⌉₊:ℝ)≤(C+1)*s := by
    have h := (Nat.ceil_lt_add_one (mul_nonneg hC.le hs0.le)).le
    nlinarith
  have hK0 : 0<(⌈C*s⌉₊:ℝ) := (mul_pos hC hs0).trans_le (Nat.le_ceil _)
  have he : -(ε*s)^2/(2*⌈C*s⌉₊*R^2) ≤ -(ε^2/(2*(C+1)*R^2))*s := by
    rw [neg_div,neg_mul]
    apply neg_le_neg
    apply (le_div_iff₀ (by positivity : 0<2*(⌈C*s⌉₊:ℝ)*R^2)).mpr
    have heq : (ε^2/(2*(C+1)*R^2))*s*(2*(C+1)*s*R^2)=(ε*s)^2 := by
      field_simp
    calc
      _ ≤ (ε^2/(2*(C+1)*R^2))*s*(2*(C+1)*s*R^2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg R)]
      _ = _ := heq
  apply mul_le_mul (by nlinarith : (⌈C*s⌉₊:ℝ)*2≤2*(C+1)*s)
    (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)

/-- All-vertex bounded ancestral sums under the actual conditioned code law.
The centering is the derived spine expectation, not an assumed path average. -/
theorem CriticalEvenOffspring.uniform_bounded_spine_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (b : ℕ×ℕ → ℝ) {R ε : ℝ} (hR : 0<R) (hb : ∀ z,|b z|≤R) (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {c | ∃ v≤2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  obtain ⟨C,hC,htight⟩ := p.code_height_tight hB (by positivity : 0<η/3)
  let κ := ε^2/(2*(C+1)*R^2)
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hlim := p.code_spine_exp_vanish hκ C
  filter_upwards [htight,hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3))] with n hn hln
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let K := ⌈C*s⌉₊
  let A := {c : Code N | ∃ v≤N,C*s<height c.val v}
  let D := {c : Code N | ∃ v≤N,height c.val v≤K ∧
      ε*s≤|codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|}
  have hs : 1 ≤ s := by
    change 1≤Real.sqrt (N:ℝ)
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    dsimp [N]
    norm_num
  have hsub : {c : Code N | ∃ v≤N,ε*s< |codeSpineSum b c v-(∫ z,b z ∂p.spineLaw)*height c.val v|}
      ⊆ A∪D := by
    rintro c ⟨v,hv,hbad⟩
    by_cases hh : C*s<(height c.val v:ℝ)
    · exact Or.inl ⟨v,hv,hh⟩
    · exact Or.inr ⟨v,hv,by exact_mod_cast (not_lt.mp hh).trans (Nat.le_ceil (C*s)),hbad.le⟩
  have hbound := p.code_spine_bound b (-R) R (fun z => abs_le.mp (hb z)) n K
    (mul_pos hε (lt_of_lt_of_le zero_lt_one hs))
  have hbd : (p.codeLaw n).real D ≤
      2*(C+1)*((N:ℝ)+1)*s*Real.exp (-κ*s)/codePartition p N := by
    apply hbound.trans
    simp only [sub_neg_eq_add,show (R+R)/2=R by ring]
    apply div_le_div_of_nonneg_right _ (codePartition_nonneg p N)
    have he := mul_le_mul_of_nonneg_left (spine_exp_ceiling_bound hC hR hε hs)
      (by positivity : 0≤(N:ℝ)+1)
    dsimp [K,κ] at *
    nlinarith
  have hh := (measureReal_mono (μ := p.codeLaw n) hsub).trans (measureReal_union_le A D)
  change (p.codeLaw n).real A≤η/3 at hn
  change 2*(C+1)*((N:ℝ)+1)*s*Real.exp (-κ*s)/codePartition p N<η/3 at hln
  exact hh.trans_lt (by linarith [hbd.trans_lt hln])

end FKCRT.TreeCoding
end

end OAI
