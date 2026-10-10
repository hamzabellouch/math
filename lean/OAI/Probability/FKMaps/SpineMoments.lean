import OAI.Probability.FKMaps.BlockLaw

namespace OAI

noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable
namespace CoreLabel

instance : MeasurableSpace CoreLabel := ⊤
instance : MeasurableSingletonClass CoreLabel := ⟨fun _ => trivial⟩

lemma rootMass_pos (P : Parameters) (c : CoreLabel) : 0<rootMass P c := by
  cases c with
  | none => exact div_pos zero_lt_one (emptyTotal_pos P)
  | some c =>
    exact div_pos (mul_pos (pow_pos (flexParameter_pos P) _)
      (pow_pos (mul_pos (Real.sqrt_pos.mpr (radiusParameter_pos P)) (emptyTotal_pos P)) _))
      (emptyTotal_pos P)

lemma rootLaw_pos (P : Parameters) (c : CoreLabel) : 0<rootLaw P c :=
  ENNReal.ofReal_pos.mpr (rootMass_pos P c)

lemma root_fiber (P : Parameters) (k : ℕ) :
    (∑' c : CoreLabel,if c.arity=k then rootLaw P c else 0)=(actualOffspring P).law k := by
  have h := rootLaw_by_size P (fun j => if j=k then 1 else 0)
  simpa only [mul_ite,mul_one,mul_zero,tsum_ite_eq] using h

/-- Actual conditional root-core marks. The arbitrary probability at an
unattainable arity is never used by the offspring distribution. -/
def markLaw (P : Parameters) (k : ℕ) : PMF CoreLabel :=
  if h : ∃ c : CoreLabel,c.arity=k then
    (rootLaw P).filter {c | c.arity=k} (by
      obtain ⟨c,hc⟩ := h
      exact ⟨c,hc,(rootLaw_pos P c).ne'⟩)
  else PMF.pure none

lemma markLaw_apply (P : Parameters) (k : ℕ) (h : ∃ c : CoreLabel,c.arity=k) (c : CoreLabel) :
    markLaw P k c=(if c.arity=k then rootLaw P c else 0)*((actualOffspring P).law k)⁻¹ := by
  rw [markLaw,dite_eq_left h,PMF.filter_apply]
  simp only [Set.indicator_apply,Set.mem_ofPred_eq,root_fiber]

lemma offspring_zero_unattainable (P : Parameters) (k : ℕ)
    (h : ¬∃ c : CoreLabel,c.arity=k) : (actualOffspring P).law k=0 := by
  rw [← root_fiber]
  have hc (c : CoreLabel) : c.arity≠k := fun hc => h ⟨c,hc⟩
  simp only [ite_eq_right (hc _),tsum_zero]

lemma offspring_pos_attainable (P : Parameters) (c : CoreLabel) :
    0<(actualOffspring P).law c.arity := by
  rw [← root_fiber]
  exact (rootLaw_pos P c).trans_le (by
    simpa using ENNReal.le_tsum (f := fun d : CoreLabel => if d.arity=c.arity then rootLaw P d else 0) c)

/-- Exact disintegration identity. The marks are independent draws from
this kernel after the actual offspring array is fixed. -/
theorem offspring_mul_mark (P : Parameters) (k : ℕ) (c : CoreLabel) :
    (actualOffspring P).law k*markLaw P k c=if c.arity=k then rootLaw P c else 0 := by
  by_cases h : ∃ d : CoreLabel,d.arity=k
  · rw [markLaw_apply P k h]
    by_cases hc : c.arity=k
    · rw [ite_eq_left hc]
      have hk := offspring_pos_attainable P c
      rw [hc] at hk
      rw [mul_comm (rootLaw P c),← mul_assoc,ENNReal.mul_inv_cancel hk.ne'
        ((actualOffspring P).law.apply_ne_top k),one_mul]
    · simp [hc]
  · rw [offspring_zero_unattainable P k h,zero_mul,ite_eq_right (fun hc => h ⟨c,hc⟩)]

/-- The finite product form used in the source's conditional marked law. -/
theorem product_disintegration (P : Parameters) {I : Type*} [Fintype I]
    (d : I→ℕ) (a : I → CoreLabel) :
    (∏ i,(actualOffspring P).law (d i))*(∏ i,markLaw P (d i) (a i))=
      if ∀ i,(a i).arity=d i then ∏ i,rootLaw P (a i) else 0 := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [offspring_mul_mark]
  by_cases h : ∀ i,(a i).arity=d i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end CoreLabel
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Offspring and right-child index seen at a genuine weak ascending record. -/
def ladderType (x : ℕ → ℕ) : ℕ × ℕ := (x (ladderIndex x),ladderOvershoot x)

lemma measurable_ladderType : Measurable ladderType := by
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply n
  exact (he.comp (measurable_id.prodMk measurable_ladderIndex)).prodMk
    measurable_ladderOvershoot

lemma weakLadderHit_terminal_lt {x : ℕ → ℕ} {n l : ℕ}
    (h : weakLadderHit x n l) : l < x n := by
  have hn : integerSum x n ≤ 0 := by
    cases n with
    | zero => simp
    | succ n => exact (h.1 _ (by omega) le_rfl).le
  have he := h.2
  rw [integerSum_succ] at he
  omega

lemma ladderType_of_hit {x : ℕ → ℕ} {n l : ℕ} (h : weakLadderHit x n l) :
    ladderType x=(x n,l) := by
  simp only [ladderType,ladderIndex_eq_of_hit h,ladderOvershoot_of_hit h]

lemma measurableSet_ladderTypeHit (n k l : ℕ) :
    MeasurableSet {x | weakLadderHit x n l ∧ x n=k} :=
  (measurableSet_weakLadderHit n l).inter
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

lemma ladderTypeHit_truncate (n k l : ℕ) :
    (truncateStream (n+1)) ⁻¹' {x | weakLadderHit x n l ∧ x n=k}=
      {x | weakLadderHit x n l ∧ x n=k} := by
  rw [show {x | weakLadderHit x n l ∧ x n=k}=
    {x | weakLadderHit x n l} ∩ {x | x n=k} by rfl,Set.preimage_inter,
    weakLadderHit_truncate]
  congr 1
  ext x
  simp [truncateStream]

lemma ladderTypeHit_endpoint (n k l : ℕ) (hl : l<k) :
    {x | weakLadderHit x n l ∧ x n=k}=
      {x | integerSum x n= -((k-l-1:ℕ):ℤ) ∧ negativeSurvival x n} ∩ {x | x n=k} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,weakLadderHit,integerSum_succ]
  constructor
  · rintro ⟨⟨hs,he⟩,hx⟩
    refine ⟨⟨?_,hs⟩,hx⟩
    omega
  · rintro ⟨⟨he,hs⟩,hx⟩
    refine ⟨⟨hs,?_⟩,hx⟩
    omega

lemma CriticalEvenOffspring.ladderTypeHit_mass (p : CriticalEvenOffspring) (k l : ℕ) :
    (∑' n,p.streamLaw {x | weakLadderHit x n l ∧ x n=k})=
      if l<k then p.law k else 0 := by
  split_ifs with hl
  · simp_rw [ladderTypeHit_endpoint _ _ _ hl,p.prefix_inter_next _ _ _
      (measurableSet_survival_endpoint _ _) (survival_endpoint_truncate _ _)]
    rw [ENNReal.tsum_mul_right,p.negative_potential,one_mul]
  · have he : ∀ n,{x | weakLadderHit x n l ∧ x n=k}=(∅ : Set (ℕ → ℕ)) := by
      intro n
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hh,hk⟩
      exact hl (hk ▸ weakLadderHit_terminal_lt hh)
    simp only [he,measure_empty,tsum_zero]

/-- The exact spine pair has probability p(k) for each of its k possible child slots,
and is independent of the infinite future. -/
lemma CriticalEvenOffspring.ladderType_slice (p : CriticalEvenOffspring)
    (k l : ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw ({x | ladderType x=(k,l)} ∩ ladderTail ⁻¹' F)=
      (if l<k then p.law k else 0)*p.streamLaw F := by
  have he : ({x | ladderType x=(k,l)} ∩ ladderTail ⁻¹' F : Set (ℕ → ℕ)) =ᵐ[p.streamLaw]
      ⋃ n : ℕ, {x | weakLadderHit x n l ∧ x n=k} ∩ (streamShift (n+1)) ⁻¹' F := by
    filter_upwards [p.ae_weakLadderHit] with x hx
    apply propext
    obtain ⟨n,j,hh⟩ := hx
    constructor
    · rintro ⟨ht,hxF⟩
      change ladderType x=(k,l) at ht
      rw [ladderType_of_hit hh,Prod.mk.injEq] at ht
      obtain ⟨hk,rfl⟩ := ht
      exact Set.mem_iUnion.mpr ⟨n,⟨hh,hk⟩,by
        simpa only [Set.mem_preimage,← ladderTail_of_hit hh] using hxF⟩
    · intro hm
      obtain ⟨m,⟨hm,hk⟩,hxF⟩ := Set.mem_iUnion.mp hm
      refine ⟨by change ladderType x=(k,l); rw [ladderType_of_hit hm,hk],?_⟩
      simpa only [Set.mem_preimage,ladderTail_of_hit hm] using hxF
  rw [measure_congr he,measure_iUnion]
  · simp_rw [p.prefix_inter_shift (n := _)
      (hE := measurableSet_ladderTypeHit _ _ _) (hF := hF)
      (htr := ladderTypeHit_truncate _ _ _)]
    rw [ENNReal.tsum_mul_right,p.ladderTypeHit_mass]
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (weakLadderHit_unique hn.1.1 hm.1.1).1
  · intro n
    exact (measurableSet_ladderTypeHit n k l).inter ((measurable_streamShift (n+1)) hF)

def CriticalEvenOffspring.spineLaw (p : CriticalEvenOffspring) : Measure (ℕ×ℕ) :=
  p.streamLaw.map ladderType

instance (p : CriticalEvenOffspring) : IsProbabilityMeasure p.spineLaw :=
  inferInstanceAs (IsProbabilityMeasure (p.streamLaw.map ladderType))

lemma CriticalEvenOffspring.spineLaw_singleton (p : CriticalEvenOffspring) (k l : ℕ) :
    p.spineLaw {(k,l)}=if l<k then p.law k else 0 := by
  rw [CriticalEvenOffspring.spineLaw,Measure.map_apply measurable_ladderType (measurableSet_singleton _)]
  change p.streamLaw {x | ladderType x=(k,l)}=_
  simpa
    using p.ladderType_slice k l Set.univ MeasurableSet.univ

lemma CriticalEvenOffspring.ladderType_rectangle (p : CriticalEvenOffspring)
    (A : Set (ℕ×ℕ)) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw (ladderType ⁻¹' A ∩ ladderTail ⁻¹' F)=p.spineLaw A*p.streamLaw F := by
  classical
  have he : ladderType ⁻¹' A ∩ ladderTail ⁻¹' F=
      ⋃ z ∈ A,{x | ladderType x=z} ∩ ladderTail ⁻¹' F := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨ladderType x,hx.1,rfl,hx.2⟩
    · rintro ⟨z,hz,he,hx⟩
      exact ⟨he.symm ▸ hz,hx⟩
  rw [he,measure_biUnion (Set.to_countable A)]
  · simp_rw [p.ladderType_slice _ _ F hF,ENNReal.tsum_mul_right]
    congr 1
    simp_rw [← p.spineLaw_singleton]
    exact tsum_measure_preimage_singleton (Set.to_countable A) (fun _ _ => measurableSet_singleton _)
  · intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    exact hkl (hk.1.symm.trans hl.1)
  · intro k _
    exact (measurableSet_eq_fun measurable_ladderType measurable_const).inter (measurable_ladderTail hF)

lemma CriticalEvenOffspring.ladderType_indep_tail (p : CriticalEvenOffspring) :
    IndepFun ladderType ladderTail p.streamLaw := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A F hA hF
  rw [p.ladderTail_preserving.measure_preimage hF.nullMeasurableSet]
  rw [← Measure.map_apply measurable_ladderType hA]
  exact p.ladderType_rectangle A F hF

lemma CriticalEvenOffspring.ladderTypes_iid (p : CriticalEvenOffspring) :
    iIndepFun (fun i x => ladderType (ladderTail^[i] x)) p.streamLaw :=
  regenerative_iIndepFun p.streamLaw ladderType ladderTail measurable_ladderType
    p.ladderTail_preserving p.ladderType_indep_tail

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.spine_lintegral_fst (p : CriticalEvenOffspring) :
    (∫⁻ z : ℕ×ℕ,(z.1:ℝ≥0∞) ∂p.spineLaw)=ENNReal.ofReal (p.variance+1) := by
  rw [lintegral_countable',ENNReal.tsum_prod']
  simp_rw [p.spineLaw_singleton,mul_ite,mul_zero]
  have he (k : ℕ) : (∑' l : ℕ,if l<k then (k:ℝ≥0∞)*p.law k else 0)=
      (k:ℝ≥0∞)^2*p.law k := by
    rw [tsum_eq_sum (s := Finset.range k)]
    · simp only [Finset.sum_ite_of_true (fun l hl => Finset.mem_range.mp hl),Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [pow_two,mul_assoc]
    · intro l hl
      simp only [Finset.mem_range] at hl
      simp [hl]
  simp_rw [he]
  rw [p.variance_eq_second_sub_one,sub_add_cancel,
    ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) (p.nonneg k)) p.second]
  apply tsum_congr
  intro k
  simp only [p.law_apply,ENNReal.ofReal_mul (sq_nonneg (k:ℝ)),ENNReal.ofReal_pow (Nat.cast_nonneg k)]
  norm_cast

lemma CriticalEvenOffspring.spine_integrable_fst (p : CriticalEvenOffspring) :
    Integrable (fun z : ℕ×ℕ => (z.1:ℝ)) p.spineLaw := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_natCast,ENNReal.ofReal_natCast]
  rw [p.spine_lintegral_fst]
  exact ENNReal.ofReal_lt_top

lemma CriticalEvenOffspring.spine_integral_fst (p : CriticalEvenOffspring) :
    (∫ z : ℕ×ℕ,(z.1:ℝ) ∂p.spineLaw)=p.variance+1 := by
  calc
    _ = (∫⁻ z : ℕ×ℕ, ENNReal.ofReal (z.1:ℝ) ∂p.spineLaw).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun z => Nat.cast_nonneg z.1))
        (measurable_of_countable _).aestronglyMeasurable
    _ = _ := by
      simp only [ENNReal.ofReal_natCast]
      rw [p.spine_lintegral_fst,ENNReal.toReal_ofReal (by linarith [p.variance_pos])]

lemma CriticalEvenOffspring.spine_integrable_label (p : CriticalEvenOffspring) (b : ℕ×ℕ → ℝ)
    (hb : ∀ z,0≤b z ∧ b z≤z.1) : Integrable b p.spineLaw := by
  apply p.spine_integrable_fst.mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb z).1] using (hb z).2)

lemma CriticalEvenOffspring.ladderType_hasLaw (p : CriticalEvenOffspring) :
    HasLaw ladderType p.spineLaw p.streamLaw :=
  ⟨measurable_ladderType.aemeasurable,rfl⟩

lemma CriticalEvenOffspring.ladderTypes_hasLaw (p : CriticalEvenOffspring) (i : ℕ) :
    HasLaw (fun x => ladderType (ladderTail^[i] x)) p.spineLaw p.streamLaw := by
  exact p.ladderType_hasLaw.comp (p.ladderTail_preserving.iterate i).hasLaw

/-- A genuinely sampled spine's bounded labels satisfy a two-sided Hoeffding bound.
The label mean is the exact p(k)-per-child-slot spine expectation. -/
lemma CriticalEvenOffspring.spine_label_deviation (p : CriticalEvenOffspring)
    (b : ℕ×ℕ → ℝ) (a d : ℝ) (hb : ∀ z,b z∈Set.Icc a d)
    (h : ℕ) (r : ℝ) (hr : 0≤r) :
    p.streamLaw.real {x | r≤|∑ i ∈ Finset.range h,
      (b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw)|} ≤
      2*Real.exp (-r^2/(2*h*((d-a)/2)^2)) := by
  let Y : ℕ → (ℕ → ℕ) → ℝ := fun i x =>
    b (ladderType (ladderTail^[i] x)) - ∫ z,b z ∂p.spineLaw
  have hi : iIndepFun Y p.streamLaw := p.ladderTypes_iid.comp
    (fun _ z => b z - ∫ z,b z ∂p.spineLaw) (fun _ => measurable_of_countable _)
  have hg : ∀ i,HasSubgaussianMGF (Y i) ((‖d-a‖₊/2)^2) p.streamLaw := by
    intro i
    have hm : Measurable (fun x => b (ladderType (ladderTail^[i] x))) :=
      (measurable_of_countable b).comp (measurable_ladderType.comp (measurable_ladderTail.iterate i))
    have hx := hasSubgaussianMGF_of_mem_Icc (μ := p.streamLaw) hm.aemeasurable
      (Eventually.of_forall (fun x => hb (ladderType (ladderTail^[i] x))))
    have he : (∫ x,b (ladderType (ladderTail^[i] x)) ∂p.streamLaw)=∫ z,b z ∂p.spineLaw :=
      (p.ladderTypes_hasLaw i).integral_comp (measurable_of_countable b).aestronglyMeasurable
    simpa only [he] using hx
  have hp := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := h) hi (fun i _ => hg i) hr
  have hn := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := h) (hi.comp (fun _ t => -t) (fun _ => measurable_neg))
    (fun i _ => (hg i).neg) hr
  have hs : {x | r≤|∑ i∈Finset.range h,Y i x|} ⊆
      {x | r≤∑ i∈Finset.range h,Y i x} ∪ {x | r≤∑ i∈Finset.range h,-Y i x} := by
    intro x hx
    change r≤|_| at hx
    rcases le_abs.mp hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simpa only [Set.mem_ofPred_eq,Finset.sum_neg_distrib] using hx)
  have hle := (measureReal_mono (μ := p.streamLaw) hs).trans (measureReal_union_le _ _)
  change _≤_ at hp hn
  push_cast at hp hn
  simp only [Real.norm_eq_abs,div_pow,sq_abs] at hp hn
  dsimp only [Y, Function.comp_apply] at hp hn hle
  simp only [div_pow]
  exact hle.trans (by linarith)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma prefixMaximum_eq_ladder {S : ℕ → ℤ} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    prefixMaximum S n=S (τ (renewalCount τ n)) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun k hk => h.maximum (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  · exact Finset.le_sup' S (Finset.mem_range.mpr (by have := renewalCount_spec h.zero n; omega))

lemma renewalCount_before {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) (r : ℕ) :
    renewalCount τ (τ (r+1)-1)=r := by
  apply le_antisymm
  · have ht : τ (r+1)-1<τ (r+1) := by have : r+1≤τ (r+1) := hτ.le_apply; omega
    have := (le_renewalCount_iff hτ h₀ (r+1) (τ (r+1)-1)).not.mpr (not_le_of_gt ht)
    omega
  · apply (le_renewalCount_iff hτ h₀ r (τ (r+1)-1)).mpr
    have ht : τ r<τ (r+1) := hτ (Nat.lt_succ_self r)
    omega

/-- A record's terminal offspring and its increase over the previous running maximum.
This definition uses only the first t offspring, even for streams which have no later records. -/
def recordTypeAt (x : ℕ → ℕ) (t : ℕ) : ℕ×ℕ :=
  (x (t-1),(integerSum x t-prefixMaximum (integerSum x) (t-1)).toNat)

lemma recordTypeAt_ladder {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    recordTypeAt x (ladderTime x (r+1))=ladderType (ladderTail^[r] x) := by
  have hh := ladderTime_enumeration hx
  have hsum := ladderTime_step_level hx r
  unfold recordTypeAt ladderType
  rw [prefixMaximum_eq_ladder hh,renewalCount_before hh.strictMono hh.zero]
  apply Prod.ext
  · rw [ladderTail_iterate]
    change x (ladderTime x (r+1)-1)=x (ladderTime x r+ladderIndex (streamShift (ladderTime x r) x))
    congr 1
    rw [ladderTime,ladderTail_iterate]
    omega
  · change (integerSum x (ladderTime x (r+1))-integerSum x (ladderTime x r)).toNat=_
    rw [hsum,Int.toNat_natCast]
    rfl

def recordSpineSum (b : ℕ×ℕ → ℝ) (x : ℕ → ℕ) (v : ℕ) : ℝ :=
  ∑ t ∈ weakRecords (integerSum x) v,b (recordTypeAt x t)

lemma recordSpineSum_eq {x : ℕ → ℕ} (hx : HasAllLadders x) (b : ℕ×ℕ → ℝ) (v : ℕ) :
    recordSpineSum b x v=∑ i∈Finset.range (renewalCount (ladderTime x) v),
      b (ladderType (ladderTail^[i] x)) := by
  have he := ladderTime_enumeration hx
  rw [recordSpineSum,he.records,Finset.sum_image]
  · have hs : Finset.Icc 1 (renewalCount (ladderTime x) v)=
        (Finset.range (renewalCount (ladderTime x) v)).image (fun i => i+1) := by
      ext i
      simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
      constructor
      · intro hi
        exact ⟨i-1,by omega,by omega⟩
      · rintro ⟨j,hj,rfl⟩
        omega
    rw [hs,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      rw [recordTypeAt_ladder hx]
    · intro i _ j _ hij
      exact Nat.add_right_cancel hij
  · exact fun _ _ _ _ hij => he.strictMono.injective hij

lemma integerSum_congr_prefix {x y : ℕ → ℕ} {N : ℕ} (h : ∀ k<N,x k=y k) :
    ∀ k≤N,integerSum x k=integerSum y k := by
  intro k hk
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)]

lemma recordSpineSum_congr_prefix {x y : ℕ → ℕ} {N : ℕ}
    (h : ∀ k<N,x k=y k) (b : ℕ×ℕ → ℝ) :
    recordSpineSum b x N=recordSpineSum b y N := by
  have hS := integerSum_congr_prefix h
  unfold recordSpineSum
  rw [weakRecords_congr_prefix hS]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht0,htN,_⟩ := (mem_weakRecords _ _ _).mp ht
  have he : recordTypeAt x t=recordTypeAt y t := by
    unfold recordTypeAt
    rw [h (t-1) (by omega),hS t htN,prefixMaximum_congr (fun k hk => hS k (by omega))]
  rw [he]

lemma measurable_recordSpineSum (b : ℕ×ℕ → ℝ) (v : ℕ) : Measurable (fun x => recordSpineSum b x v) := by
  have he : (fun x => recordSpineSum b x v)=(fun z : Fin v → ℕ => recordSpineSum b (arrayStream z) v) ∘ streamPrefix v := by
    funext x
    apply recordSpineSum_congr_prefix
    intro k hk
    simp [arrayStream,streamPrefix,hk]
  rw [he]
  exact (measurable_of_countable _).comp (measurable_streamPrefix v)

end FKCRT.TreeCoding
end

end OAI
