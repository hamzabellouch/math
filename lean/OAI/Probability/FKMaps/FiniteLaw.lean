import OAI.Probability.FKMaps.ConditionedTrees
import OAI.Probability.FKMaps.RootedLaw

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory
variable {n : ℕ}

def treeActivity (x : RootedSpanningTree n) : ℕ :=
  explorationActivity (reversal x.1) (rotation x.1) (tourSelector (reversal x.1)
    (rotation x.1) x.1.out.property.1) ∅ Finset.univ x.2.val (n+1)

lemma rootedWord_activity (x : RootedSpanningTree n) :
    treeActivity x=flexibleCount (List.ofFn (rootedWordEquiv n x).val) [] := by
  let X := canonicalizeTree x.1.out x.2.val x.2.property
  have hn : Fintype.card (Orbit x.1.out.val.1)=n+1 :=
    reversal_card x.1.out.val.1 x.1.out.property.1 x.1.out.property.2.1
  have h1 := canonicalizeTree_activity x.1.out x.2.val x.2.property
  have h2 := canonical_activity_eq_flexible X.toMap X.A X.tree X.tour
  rw [hn] at h1
  exact h1.symm.trans h2

/-- Full finite weighted pushforward. An arbitrary observable on the actual
rooted map quotient is retained; this is stronger than a partition equality. -/
theorem loopPolynomial_word_transport (t : ℝ) (ht : t≠0) (F : RootedMap n→ℝ) :
    (∑ M : RootedMap n,F M*loopPolynomial t M)=
      ∑ w : SuccessfulWord n,
        F ((rootedWordEquiv n).symm w).1 * (1+t)^flexibleCount (List.ofFn w.val) [] := by
  have hs : (∑ M : RootedMap n,F M*loopPolynomial t M)=
      ∑ x : RootedSpanningTree n,F x.1*(1+t)^treeActivity x := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro M _
    rw [loopPolynomial_tour_activity t ht,Finset.mul_sum]
    change (∑ T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ,
      F M*(1+t)^explorationActivity (reversal M) (rotation M)
        (tourSelector (reversal M) (rotation M) M.out.property.1) ∅ Finset.univ T (n+1))=_
    exact Finset.sum_subtype _ (fun _ => Iff.rfl) _
  rw [hs]
  have hh := Equiv.sum_comp (rootedWordEquiv n) (fun w : SuccessfulWord n =>
    F ((rootedWordEquiv n).symm w).1*(1+t)^flexibleCount (List.ofFn w.val) [])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro x _
  rw [Equiv.symm_apply_apply,rootedWord_activity]

/-- Exact FK marginal on *unlabelled rooted* maps, with the original cluster
weight. The common sqrt(q) factor is explicit, not absorbed into the law. -/
theorem fk_word_transport (q : ℝ) (hq : 0<q) (F : RootedMap n→ℝ) :
    (∑ M : RootedMap n, ∑ A : Finset (Edge M),F M*fkWeight q M A)=
      Real.sqrt q * ∑ w : SuccessfulWord n,
        F ((rootedWordEquiv n).symm w).1 * (1+Real.sqrt q)^flexibleCount (List.ofFn w.val) [] := by
  simp_rw [← Finset.mul_sum,fk_marginal_loopPolynomial q hq]
  calc
    _=Real.sqrt q*(∑ M : RootedMap n,F M*loopPolynomial (Real.sqrt q) M) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      ring
    _=_ := congrArg (Real.sqrt q*·) (loopPolynomial_word_transport _ (ne_of_gt (Real.sqrt_pos.mpr hq)) F)

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT
open Inventory

lemma Parameters.ofQ_ratio (q : ℝ) (hq : 4<q) :
    2*(Parameters.ofQ q hq).p/(1-(Parameters.ofQ q hq).p)=Real.sqrt q := by
  have hs : 0<Real.sqrt q+2 := by positivity
  dsimp [Parameters.ofQ]
  field_simp
  ring

/-- The finite functions and literal word lists encode exactly the same
successful words, including their fixed length. -/
def successfulListEquiv (n : ℕ) : SuccessfulWord n ≃ {v // v∈typedEmptyWords (2*(n+1))} where
  toFun w := ⟨List.ofFn w.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr List.length_ofFn,
    by simpa only [List.ofFn_eq_map] using w.property⟩⟩
  invFun v := ⟨fun i => v.val[i.val]'(by
      have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1
      omega),by
    have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1
    have he : ((List.finRange (2*(n+1))).map (fun i => v.val[i.val]'(by omega)))=v.val := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hj
        simp
    rw [he]
    exact (Finset.mem_filter.mp v.property).2⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact List.getElem_ofFn _
  right_inv v := by
    apply Subtype.ext
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using (mem_wordsOfLength.mp (Finset.mem_filter.mp v.property).1).symm
    · intro i hi hj
      simp only [List.getElem_ofFn]

lemma typed_word_sum (n : ℕ) (x : ℝ) :
    (∑ v∈typedEmptyWords (2*(n+1)),x^flexibleCount v [])=
      ∑ w : SuccessfulWord n,x^flexibleCount (List.ofFn w.val) [] := by
  rw [Finset.sum_subtype _ (fun _ => Iff.rfl)]
  exact (Equiv.sum_comp (successfulListEquiv n) (fun v => x^flexibleCount v.val [])).symm

/-- The exact finite inventory/FK coefficient identity. No asymptotic
hypothesis, normalization assumption, or automorphism divisor appears. -/
theorem emptyProb_fk (q : ℝ) (hq : 4<q) (n : ℕ) :
    emptyProb (Parameters.ofQ q hq) (2*(n+1))=
      ((1-(Parameters.ofQ q hq).p)/16)^(n+1)*
        ∑ M : RootedMap n,loopPolynomial (Real.sqrt q) M := by
  rw [emptyProb,rawEmpty_real,empty_wordMass_sum,Parameters.ofQ_ratio,typed_word_sum]
  congr 1
  have ht : Real.sqrt q≠0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  simpa only [one_mul] using (loopPolynomial_word_transport (n:=n) _ ht (fun _ => 1)).symm

end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace FKCRT
open Inventory

/-- The genuine rooted-map coefficient, with the stipulated trivial map. -/
def mapCoefficient (q : ℝ) : ℕ→ℝ
  | 0 => 1
  | n+1 => ∑ M : RootedMap n,loopPolynomial (Real.sqrt q) M

def inventoryRadius (q : ℝ) (hq : 4<q) : ℝ := (1-(Parameters.ofQ q hq).p)/16

lemma inventoryRadius_pos (q : ℝ) (hq : 4<q) : 0 < inventoryRadius q hq := by
  exact div_pos (sub_pos.mpr (Parameters.ofQ q hq).upper) (by norm_num)

/-- Exact rooted FK-map coefficients are the genuine iid empty-word
probabilities, including the constant term. -/
theorem coefficient_inventory (q : ℝ) (hq : 4<q) (n : ℕ) :
    mapCoefficient q n*(inventoryRadius q hq)^n=emptyProb (Parameters.ofQ q hq) (2*n) := by
  cases n with
  | zero => simp [mapCoefficient,emptyProb_zero]
  | succ n => simpa only [mapCoefficient,inventoryRadius,mul_comm] using (emptyProb_fk q hq n).symm

lemma mapCoefficient_nonneg (q : ℝ) (hq : 4<q) (n : ℕ) : 0 ≤ mapCoefficient q n := by
  have h := emptyProb_nonneg (Parameters.ofQ q hq) (2*n)
  rw [← coefficient_inventory] at h
  exact nonneg_of_mul_nonneg_left h (pow_pos (inventoryRadius_pos q hq) n)

/-- Endpoint finiteness is now established for the actual source map series,
not a freely chosen coefficient sequence. -/
theorem mapCoefficient_endpoint_summable (q : ℝ) (hq : 4<q) :
    Summable (fun n => mapCoefficient q n*(inventoryRadius q hq)^n) := by
  simpa only [coefficient_inventory] using emptyProb_even_summable (Parameters.ofQ q hq)

/-- The source lower bound on the size-weighted Abel series, with no
unproved map enumeration or asymptotic premise. -/
theorem mapCoefficient_abel_lower (q : ℝ) (hq : 4<q) :
    ∃ c : ℝ,0<c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
      c/Real.sqrt (1-x)≤∑' n : ℕ,(n:ℝ)*mapCoefficient q n*(inventoryRadius q hq)^n*x^n := by
  obtain ⟨c,hc,h⟩ := empty_abel_lower (Parameters.ofQ q hq)
  refine ⟨c,hc,?_⟩
  intro x hx hx'
  simpa only [mul_assoc,coefficient_inventory] using h x hx hx'

lemma partition_mapCoefficient (q : ℝ) (hq : 0<q) (n : ℕ) :
    partition q n=Real.sqrt q*mapCoefficient q (n+1) := by
  simp only [partition,mapCoefficient,fk_marginal_loopPolynomial q hq,Finset.mul_sum]

lemma mapCoefficient_pos (q : ℝ) (hq : 4<q) (n : ℕ) : 0 < mapCoefficient q n := by
  cases n with
  | zero => exact zero_lt_one
  | succ n =>
    have h := partition_pos (q:=q) (by linarith) n
    rw [partition_mapCoefficient q (by linarith)] at h
    exact pos_of_mul_pos_right h (Real.sqrt_nonneg q)

/-- Exact finite word normalizer for the map marginal. -/
def typedPartition (q : ℝ) (n : ℕ) : ℝ :=
  ∑ w : SuccessfulWord n,(1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []

lemma partition_typedPartition (q : ℝ) (hq : 0<q) (n : ℕ) :
    partition q n=Real.sqrt q*typedPartition q n := by
  simpa only [partition,typedPartition,one_mul] using fk_word_transport q hq (n:=n) (fun _ => 1)

lemma typedPartition_pos (q : ℝ) (hq : 0<q) (n : ℕ) : 0 < typedPartition q n := by
  have h := partition_pos hq n
  rw [partition_typedPartition q hq n] at h
  exact pos_of_mul_pos_right h (Real.sqrt_nonneg q)

/-- The original all-edge metric and normalized degree measure are retained
under the exact finite word pushforward. This is a finite identity, not the
unproved GHP limit. -/
theorem finiteExpectation_typed (q : ℝ) (hq : 0<q) (scale : ℝ) (n : ℕ)
    (F : MetricMeasureData→ℝ) :
    finiteExpectation q scale n F=
      ∑ w : SuccessfulWord n,
        ((1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []/typedPartition q n)*
          F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
  unfold finiteExpectation
  have h := fk_word_transport q hq (n:=n) (fun M => F (mapSpace scale M))
  have hs : Real.sqrt q≠0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hnum : (∑ M : RootedMap n,∑ A : Finset (Edge M),
      fkWeight q M A*F (mapSpace scale M))=
      Real.sqrt q*∑ w : SuccessfulWord n,
        (1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []*F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
    calc
      _=(∑ M : RootedMap n,∑ A : Finset (Edge M),F (mapSpace scale M)*fkWeight q M A) := by
        apply Finset.sum_congr rfl
        intro M _
        apply Finset.sum_congr rfl
        intro A _
        exact mul_comm _ _
      _=_ := h
      _=_ := by
        congr 1
        apply Finset.sum_congr rfl
        intro w _
        exact mul_comm _ _
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
  rw [hnum,partition_typedPartition q hq n,mul_div_mul_left _ _ hs]

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

lemma finite_atomic_of_ae_range {X I : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] [Fintype I]
    (μ : Measure X) (f : I→X) (hf : Function.Injective f)
    (hs : ∀ᵐ x ∂μ,x∈Set.range f) :
    μ=∑ i : I, μ {f i} • Measure.dirac (f i) := by
  apply Measure.ext_of_singleton
  intro x
  by_cases hx : x∈Set.range f
  · obtain ⟨i,rfl⟩ := hx
    simp only [Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',
      measurableSet_singleton,Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply,smul_eq_mul]
    simp only [hf.eq_iff,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have hz : μ {x}=0 := by
      rw [ae_iff_of_countable] at hs
      exact not_not.mp (fun hn => hx (hs x hn))
    rw [hz]
    symm
    simp only [Measure.finsetSum_apply,Measure.smul_apply,Measure.dirac_apply',
      measurableSet_singleton,Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun h => hx ⟨i,h⟩),mul_zero]

namespace Inventory.CoreTree

def sizedListEquiv (N : ℕ) : SizedWord N ≃ {w // w∈typedEmptyWords N} where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr w.property,w.val.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).2⟩,
    mem_wordsOfLength.mp (Finset.mem_filter.mp w.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def successfulMarkedEquiv (n : ℕ) : SuccessfulWord n ≃ MarkedCode (2*(n+1)+1) :=
  ((successfulListEquiv n).trans (sizedListEquiv (2*(n+1))).symm).trans
    (markedWordEquiv (2*(n+1))).symm

lemma successfulMarked_word (n : ℕ) (w : SuccessfulWord n) :
    ((markedWordEquiv (2*(n+1))) (successfulMarkedEquiv n w)).val.val=List.ofFn w.val := by
  simp only [successfulMarkedEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
  rfl

end Inventory.CoreTree

/-- The genuine independently marked conditioned tree law is exactly a
finite atomic law indexed by the successful words of the original map
bijection, not just proportional formal generating functions. -/
theorem actual_marked_atomic (P : Parameters) (n : ℕ) :
    (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1)=
      ∑ w : SuccessfulWord n,
        (ENNReal.ofReal (wordMonomial (flexParameter P) (Real.sqrt (radiusParameter P))
          (List.ofFn w.val)/emptyTotal P)/
          ENNReal.ofReal (codePartition (actualOffspring P) (2*(n+1)+1))) •
          Measure.dirac (CoreTree.successfulMarkedEquiv n w).val := by
  let f : SuccessfulWord n → Code (2*(n+1)+1)×(Fin (2*(n+1)+1)→ CoreLabel) :=
    fun w => (CoreTree.successfulMarkedEquiv n w).val
  have hf : Function.Injective f := Subtype.val_injective.comp (CoreTree.successfulMarkedEquiv n).injective
  have hs : ∀ᵐ x ∂(actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1),
      x∈Set.range f := by
    filter_upwards [actual_marked_compatible P (n+1)] with x hx
    exact ⟨(CoreTree.successfulMarkedEquiv n).symm ⟨x,hx⟩,
      congrArg Subtype.val ((CoreTree.successfulMarkedEquiv n).apply_symm_apply ⟨x,hx⟩)⟩
  rw [finite_atomic_of_ae_range _ f hf hs]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [actual_marked_word_density P (n+1),CoreTree.successfulMarked_word]

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

lemma atomic_normalize {X I : Type*} [MeasurableSpace X] [Fintype I]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : I → X) (w : I → ℝ)
    (hw : ∀ i,0 ≤ w i) {K : ℝ} (hK : 0 ≤ K)
    (h : μ=∑ i,ENNReal.ofReal (K*w i) • Measure.dirac (f i))
    (hs : 0 < ∑ i,w i) :
    μ=∑ i,ENNReal.ofReal (w i/(∑ j,w j)) • Measure.dirac (f i) := by
  have hm := congrArg (fun ν : Measure X => ν Set.univ) h
  simp only [measure_univ,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one] at hm
  have hm' : (1 : ℝ)=K*∑ i,w i := by
    have hh : ENNReal.ofReal (1 : ℝ)=ENNReal.ofReal (∑ i,K*w i) := by
      simpa only [ENNReal.ofReal_one,ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hK (hw i))] using hm
    have ht := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg hK (hw i)))] at ht
    simpa only [Finset.mul_sum] using ht
  have hK' : K=(∑ i,w i)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hs.ne').mpr hm'.symm
  rw [h,hK']
  congr 1
  apply funext
  intro i
  rw [div_eq_mul_inv,mul_comm]

lemma actual_marked_normalized (q : ℝ) (hq : 4<q) (n : ℕ) :
    (actualOffspring (Parameters.ofQ q hq)).markedCodeLaw
      (fun k => (CoreLabel.markLaw (Parameters.ofQ q hq) k).toMeasure) (n+1)=
      ∑ w : SuccessfulWord n,
        ENNReal.ofReal ((1+Real.sqrt q)^flexibleCount (List.ofFn w.val) []/typedPartition q n) •
          Measure.dirac (CoreTree.successfulMarkedEquiv n w).val := by
  let P := Parameters.ofQ q hq
  let K := (Real.sqrt (radiusParameter P))^(2*(n+1))/emptyTotal P/
    codePartition (actualOffspring P) (2*(n+1)+1)
  have hK : 0 ≤ K := le_of_lt (div_pos (div_pos
    (pow_pos (Real.sqrt_pos.mpr (radiusParameter_pos P)) _) (emptyTotal_pos P))
    (codePartition_odd_pos (actualOffspring P) (n+1)))
  apply atomic_normalize _ _ _ (fun _ => pow_nonneg (by positivity) _) hK _
    (typedPartition_pos q (by linarith) n)
  rw [actual_marked_atomic P n]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [← ENNReal.ofReal_div_of_pos (codePartition_odd_pos (actualOffspring P) (n+1))]
  congr 1
  change (flexParameter P)^flexibleCount (List.ofFn w.val) []*
    (Real.sqrt (radiusParameter P))^(List.ofFn w.val).length/emptyTotal P/
      codePartition (actualOffspring P) (2*(n+1)+1)=_
  rw [List.length_ofFn]
  have hp : flexParameter P=1+Real.sqrt q := by
    exact congrArg (fun t : ℝ => 1+t) (Parameters.ofQ_ratio q hq)
  rw [hp]
  dsimp [K]
  ring

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

/-- Evaluate precisely the original all-edge metric and degree measure of
an actual compatible marked core tree. Incompatible marks have probability
zero, and are assigned zero only to totalize an observable. -/
def markedMapTest (scale : ℝ) (n : ℕ) (F : MetricMeasureData → ℝ)
    (x : Code (2*(n+1)+1) × (Fin (2*(n+1)+1) → CoreLabel)) : ℝ :=
  if h : ∀ i,(x.2 i).arity=(x.1.val i).val then
    F (mapSpace scale ((rootedWordEquiv n).symm
      ((CoreTree.successfulMarkedEquiv n).symm ⟨x,h⟩)).1)
  else 0

lemma markedMapTest_word (scale : ℝ) (n : ℕ) (F : MetricMeasureData → ℝ)
    (w : SuccessfulWord n) :
    markedMapTest scale n F (CoreTree.successfulMarkedEquiv n w).val=
      F (mapSpace scale ((rootedWordEquiv n).symm w).1) := by
  rw [markedMapTest,dite_eq_left (CoreTree.successfulMarkedEquiv n w).property]
  exact congrArg (fun u : SuccessfulWord n =>
    F (mapSpace scale ((rootedWordEquiv n).symm u).1))
      ((CoreTree.successfulMarkedEquiv n).symm_apply_apply w)

/-- The full original finite FK observable is the integral under the true
independently marked conditioned GW law. No law identification or
normalizing constant remains as a hypothesis. -/
theorem finiteExpectation_marked (q : ℝ) (hq : 4<q) (scale : ℝ) (n : ℕ)
    (F : MetricMeasureData → ℝ) :
    finiteExpectation q scale n F=
      ∫ x,markedMapTest scale n F x ∂(actualOffspring (Parameters.ofQ q hq)).markedCodeLaw
        (fun k => (CoreLabel.markLaw (Parameters.ofQ q hq) k).toMeasure) (n+1) := by
  rw [actual_marked_normalized q hq n]
  rw [integral_finsetSum_measure (fun w _ =>
    (integrable_dirac (f := markedMapTest scale n F) (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,integral_dirac,smul_eq_mul,markedMapTest_word]
  rw [finiteExpectation_typed q (by linarith)]
  apply Finset.sum_congr rfl
  intro w _
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg (by positivity) _)
    (typedPartition_pos q (by linarith) n).le)]

end FKCRT
end

end OAI
