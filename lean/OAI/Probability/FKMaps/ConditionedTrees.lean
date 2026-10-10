import OAI.Probability.FKMaps.MarkedSpines

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma CriticalEvenOffspring.code_singleton (p : CriticalEvenOffspring) (n : ℕ)
    (d : Code (2*n+1)) : p.codeLaw n {d}=ENNReal.ofReal (codeWeight p d/codePartition p (2*n+1)) := by
  rw [← ofReal_measureReal,← integral_indicator_one (measurableSet_singleton d),p.code_integral]
  simp [Set.indicator]

lemma CriticalEvenOffspring.marked_singleton {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : CriticalEvenOffspring) (κ : ℕ → PMF A) (n : ℕ)
    (d : Code (2*n+1)) (a : Fin (2*n+1) → A) :
    p.markedCodeLaw (fun k => (κ k).toMeasure) n {(d,a)}=
      ENNReal.ofReal (codeWeight p d/codePartition p (2*n+1)) * ∏ i,κ (d.val i).val (a i) := by
  have he : ({(d,a)} : Set (Code (2*n+1)×(Fin (2*n+1) → A)))={d}×ˢ{a} := by ext x;simp
  rw [he,CriticalEvenOffspring.markedCodeLaw,Measure.compProd_apply_prod
    (measurableSet_singleton _) (measurableSet_singleton _),lintegral_singleton]
  simp only [codeMarkKernel,Kernel.coe_mk,codeMarkLaw,Measure.pi_singleton ]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [p.code_singleton,mul_comm]

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

lemma word_length_degrees (T : CoreTree) : T.word.length=T.degrees.sum := by
  induction T with
  | leaf => simp [word,degrees,labels,CoreLabel.arity]
  | branch c ts ih =>
    have hw : (branch c ts).word.length=∑ i,(1+(ts i).word.length) := by
      simp [word,cornerInsert,cornerList,List.length_flatMap,List.map_ofFn,List.sum_ofFn,
        add_comm]
    have hd : (branch c ts).degrees.sum=c.val.length+∑ i,(ts i).degrees.sum := by
      simp [degrees,labels_branch,CoreLabel.arity,List.flatMap_def,List.map_flatten,
        List.sum_flatten,List.map_ofFn,List.sum_ofFn]
    rw [hw,hd]
    simp_rw [ih]
    simp [Finset.sum_add_distrib]

lemma labels_length (T : CoreTree) : T.labels.length=T.word.length+1 := by
  have h := T.shape.degrees_sum
  rw [T.shape_degrees,← T.word_length_degrees] at h
  simpa only [degrees,List.length_map] using h.symm

def toCode (T : CoreTree) : Code T.labels.length :=
  ⟨fun i => ⟨(T.labels[i.val]).arity,by
    have hm : (T.labels[i.val]).arity∈T.shape.degrees := by
      rw [T.shape_degrees]
      exact List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩
    have hl := T.shape.degree_lt_length hm
    simpa only [shape_degrees,degrees,List.length_map] using hl⟩,by
    rw [isTreeCode_iff]
    convert T.degrees_excursion using 1
    unfold degreeList PlaneTree.incrementWord degrees
    simp only [List.map_map,Function.comp_def]
    exact List.ofFn_getElem_eq_map T.labels (fun c => (c.arity:ℤ)-1)⟩

abbrev MarkedCode (N : ℕ) := {x : Code N × (Fin N → CoreLabel) // ∀ i,(x.2 i).arity=(x.1.val i).val}

abbrev Sized (N : ℕ) := {T : CoreTree // T.labels.length=N}

def ofMarkedCode {N : ℕ} (x : MarkedCode N) : CoreTree :=
  labelEquiv.symm ⟨List.ofFn x.val.2,by
    have h : (List.ofFn x.val.2).map CoreLabel.arity=List.ofFn (fun i => (x.val.1.val i).val) := by
      simp only [List.map_ofFn,Function.comp_def]
      exact congrArg List.ofFn (funext x.property)
    rw [h,PlaneTree.incrementWord_ofFn]
    exact (isTreeCode_iff _).mp x.val.1.property⟩

lemma ofMarkedCode_labels {N : ℕ} (x : MarkedCode N) :
    (ofMarkedCode x).labels=List.ofFn x.val.2 :=
  congrArg Subtype.val (labelEquiv.apply_symm_apply _)

lemma ofMarkedCode_size {N : ℕ} (x : MarkedCode N) : (ofMarkedCode x).labels.length=N := by
  rw [ofMarkedCode_labels,List.length_ofFn]

lemma ofMarkedCode_injective (N : ℕ) : Function.Injective (@ofMarkedCode N) := by
  intro x y h
  have hl := congrArg labels h
  rw [ofMarkedCode_labels,ofMarkedCode_labels] at hl
  have ha : x.val.2=y.val.2 := List.ofFn_injective hl
  have hd : x.val.1=y.val.1 := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rw [← x.property i,← y.property i,ha]
  exact Subtype.ext (Prod.ext hd ha)

def sizedEquiv (N : ℕ) : MarkedCode N ≃ Sized N := Equiv.ofBijective
  (fun x => ⟨ofMarkedCode x,ofMarkedCode_size x⟩) ⟨by
    intro x y h
    exact ofMarkedCode_injective N (congrArg Subtype.val h),by
    rintro ⟨T,hT⟩
    subst N
    let d : Code T.labels.length := T.toCode
    let a : Fin T.labels.length → CoreLabel := fun i => T.labels[i.val]
    have ha : List.ofFn a=T.labels := List.ofFn_getElem
    have hcomp : ∀ i,(a i).arity=(d.val i).val := fun _ => rfl
    refine ⟨⟨(d,a),hcomp⟩,Subtype.ext ?_⟩
    apply labels_injective
    rw [ofMarkedCode_labels,ha]⟩

end CoreTree

/-- The actual conditioned independent marking density, with no change of
root distribution and no appeal to a conditional GW law as a hypothesis. -/
theorem actual_marked_singleton (P : Parameters) (n : ℕ)
    (d : Code (2*n+1)) (a : Fin (2*n+1) → CoreLabel) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n {(d,a)}=
      (if ∀ i,(a i).arity=(d.val i).val then ∏ i,CoreLabel.rootLaw P (a i) else 0)/
        ENNReal.ofReal (codePartition (actualOffspring P) (2*n+1)) := by
  rw [CriticalEvenOffspring.marked_singleton,ENNReal.ofReal_div_of_pos
    (codePartition_odd_pos _ n)]
  have hw : ENNReal.ofReal (codeWeight (actualOffspring P) d)=
      ∏ i,(actualOffspring P).law (d.val i).val := by
    unfold codeWeight
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => (actualOffspring P).nonneg _)]
    simp only [CriticalEvenOffspring.law_apply]
  rw [hw]
  simp only [div_eq_mul_inv]
  rw [mul_right_comm,CoreLabel.product_disintegration]
  by_cases h : ∀ i,(a i).arity=(d.val i).val
  · rw [ite_eq_left h,ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h]

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

/-- The actual successful words and compatible independently marked tree
codes are equivalent at each fixed total edge size. -/
def sizedWordEquiv (N : ℕ) : Sized (N+1) ≃ {w : EmptyTypedWord // w.val.length=N} :=
  Equiv.ofBijective (fun T => ⟨wordEquiv T.val,by
    have h := T.val.labels_length
    have hT := T.property
    change T.val.word.length=N
    omega⟩) ⟨by
      intro T U h
      exact Subtype.ext (word_injective (congrArg (fun w => w.val.val) h)),by
      rintro ⟨w,hw⟩
      let T := wordEquiv.symm w
      have hT : T.word=w.val := congrArg Subtype.val (wordEquiv.apply_symm_apply w)
      refine ⟨⟨T,?_⟩,Subtype.ext (Subtype.ext hT)⟩
      rw [T.labels_length,hT,hw]⟩

abbrev SizedWord (N : ℕ) := {w : EmptyTypedWord // w.val.length=N}

def markedWordEquiv (N : ℕ) : MarkedCode (N+1) ≃ SizedWord N :=
  (sizedEquiv (N+1)).trans (sizedWordEquiv N)

lemma markedWordEquiv_word (N : ℕ) (x : MarkedCode (N+1)) :
    ((markedWordEquiv N) x).val.val=(ofMarkedCode x).word := rfl

lemma rootMass_product (P : Parameters) {N : ℕ} (x : MarkedCode N) :
    (∏ i,CoreLabel.rootMass P (x.val.2 i))=
      wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) (ofMarkedCode x).word/emptyTotal P := by
  have h := (ofMarkedCode x).productMass_eq (flexParameter P)
    (Real.sqrt (radiusParameter P)) (emptyTotal P) (emptyTotal_pos P).ne'
  rw [productMass_labels,ofMarkedCode_labels,List.map_ofFn,List.prod_ofFn] at h
  exact h

lemma rootLaw_product (P : Parameters) {N : ℕ} (x : MarkedCode N) :
    (∏ i,CoreLabel.rootLaw P (x.val.2 i))=ENNReal.ofReal
      (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P)) (ofMarkedCode x).word/emptyTotal P) := by
  rw [← rootMass_product]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => CoreLabel.rootMass_nonneg P _)]
  rfl

end CoreTree

/-- Complete pointwise finite-law density, now expressed in the word of the
original map bijection. Every leaf, every admissible arity and the common
normalizing factor are retained. -/
theorem actual_marked_word_density (P : Parameters) (n : ℕ)
    (x : CoreTree.MarkedCode (2*n+1)) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n {x.val}=
      ENNReal.ofReal (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P))
        ((CoreTree.markedWordEquiv (2*n)) x).val.val/emptyTotal P)/
          ENNReal.ofReal (codePartition (actualOffspring P) (2*n+1)) := by
  rw [actual_marked_singleton P n x.val.1 x.val.2,ite_eq_left x.property,
    CoreTree.rootLaw_product P x]
  rfl

/-- There is no positive mass on inconsistent marks. In particular the
arbitrary mark at an impossible offspring value is irrelevant. -/
theorem actual_marked_compatible (P : Parameters) (n : ℕ) :
    ∀ᵐ x ∂(actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) n,
      ∀ i,(x.2 i).arity=(x.1.val i).val := by
  rw [ae_iff_of_countable]
  intro x hx
  by_contra hc
  have h := actual_marked_singleton P n x.1 x.2
  rw [ite_eq_right hc,ENNReal.zero_div] at h
  exact hx h

end FKCRT.Inventory
end

end OAI
