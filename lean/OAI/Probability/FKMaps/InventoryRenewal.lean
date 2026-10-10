import OAI.Probability.FKMaps.InventoryDrift
import OAI.Probability.FKMaps.LadderRecords

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def survivorTail (x : ℕ → Letter) : ℕ → Letter := tail ((firstSurvivor x).untopD 0+1) x
def survivorData (x : ℕ → Letter) : ℕ × Bool := (K x,firstType x)
def prefixData (n : ℕ) (x : ℕ → Letter) : ℕ × Bool :=
  ((reduce (revealed x (n+1))).orders.length,(reduce (revealed x (n+1))).burgers.headD false)
lemma measurable_prefixData (n : ℕ) : Measurable[rawFiltration n] (prefixData n) :=
  prefix_measurable n (fun y => ((reduce (List.ofFn y).reverse).orders.length,
    (reduce (List.ofFn y).reverse).burgers.headD false))
lemma measurable_survivorData : Measurable survivorData := measurable_K.prodMk measurable_firstType
lemma measurable_survivorTail : Measurable survivorTail := by
  have hm : Measurable (fun x : ℕ → Letter => (firstSurvivor x).untopD 0+1) :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0+1)).comp measurable_firstSurvivor
  have ht : Measurable (fun z : ℕ × (ℕ → Letter) => tail z.1 z.2) :=
    measurable_from_prod_countable_right (fun n => measurable_tail n)
  exact ht.comp (hm.prodMk measurable_id)
lemma survivorData_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    survivorData x=prefixData n x := by
  simp only [survivorData,prefixData,K_of_hit h,firstType_of_hit h]
lemma survivorTail_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    survivorTail x=tail (n+1) x := by
  simp only [survivorTail,h]
  rfl

lemma survivor_rectangle_sum (P : Parameters) (A : Set (ℕ × Bool)) (B : Set (ℕ → Letter))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B)=
      (∑' n : ℕ,streamLaw P ℕ ({x | firstSurvivor x=WithTop.some n} ∩ prefixData n ⁻¹' A))*streamLaw P ℕ B := by
  let C : ℕ → Set (ℕ → Letter) := fun n => {x | firstSurvivor x=WithTop.some n} ∩ prefixData n ⁻¹' A
  have hC (n : ℕ) : MeasurableSet[rawFiltration n] (C n) :=
    (firstSurvivor_stopping.measurableSet_eq n).inter (measurable_prefixData n hA)
  have hCm (n : ℕ) : MeasurableSet (C n) := rawFiltration.le n _ (hC n)
  have he : (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B : Set (ℕ → Letter)) =ᵐ[streamLaw P ℕ]
      (⋃ n,C n ∩ tail (n+1) ⁻¹' B : Set (ℕ → Letter)) := by
    filter_upwards [firstSurvivor_finite P] with x hx
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    have hn' : firstSurvivor x=WithTop.some n := hn.symm
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨n,⟨hn',by simpa only [Set.mem_preimage,← survivorData_of_hit hn'] using ha⟩,
        by simpa only [Set.mem_preimage,← survivorTail_of_hit hn'] using hb⟩
    · intro h
      obtain ⟨m,⟨hm,ha⟩,hb⟩ := Set.mem_iUnion.mp h
      exact ⟨by simpa only [Set.mem_preimage,survivorData_of_hit hm] using ha,
        by simpa only [Set.mem_preimage,survivorTail_of_hit hm] using hb⟩
  rw [measure_congr he,measure_iUnion]
  · have hs (n : ℕ) : streamLaw P ℕ (C n ∩ tail (n+1) ⁻¹' B)=streamLaw P ℕ (C n)*streamLaw P ℕ B := by
      have h := ((indep_iff_forall_indepSet _).mp (raw_indep_tail P n) _ _ (hC n)
        (measurable_iff_comap_le.mpr le_rfl hB)).measure_inter_eq_mul
      rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at h
      exact h
    simp_rw [hs]
    rw [ENNReal.tsum_mul_right]
  · intro n m hnm
    exact Set.disjoint_left.mpr (fun x hn hm => hnm (WithTop.coe_injective (hn.1.1.symm.trans hm.1.1)))
  · intro n
    exact (hCm n).inter ((measurable_tail (n+1)) hB)

lemma survivor_rectangle (P : Parameters) (A : Set (ℕ × Bool)) (B : Set (ℕ → Letter))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B)=
      streamLaw P ℕ (survivorData ⁻¹' A)*streamLaw P ℕ B := by
  rw [survivor_rectangle_sum P A B hA hB]
  have h := survivor_rectangle_sum P A Set.univ hA MeasurableSet.univ
  simp only [Set.preimage_univ,Set.inter_univ,measure_univ,mul_one] at h
  rw [h]
lemma survivorTail_preserving (P : Parameters) :
    MeasurePreserving survivorTail (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_survivorTail,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_survivorTail hB]
  simpa using survivor_rectangle P Set.univ B MeasurableSet.univ hB
lemma survivorData_indep_tail (P : Parameters) : IndepFun survivorData survivorTail (streamLaw P ℕ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  rw [(survivorTail_preserving P).measure_preimage hB.nullMeasurableSet]
  exact survivor_rectangle P A B hA hB

def parsingData (j : ℕ) (x : ℕ → Letter) : ℕ × Bool := survivorData (survivorTail^[j] x)
lemma parsingData_iid (P : Parameters) : iIndepFun parsingData (streamLaw P ℕ) :=
  TreeCoding.regenerative_iIndepFun (streamLaw P ℕ) survivorData survivorTail measurable_survivorData
    (survivorTail_preserving P) (survivorData_indep_tail P)
lemma parsingData_identDistrib (P : Parameters) (j : ℕ) :
    IdentDistrib (parsingData j) survivorData (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨(measurable_survivorData.comp ((survivorTail_preserving P).iterate j).measurable).aemeasurable,
    measurable_survivorData.aemeasurable,?_⟩
  change Measure.map (survivorData ∘ survivorTail^[j]) (streamLaw P ℕ)=_
  rw [← Measure.map_map measurable_survivorData ((survivorTail_preserving P).iterate j).measurable,
    ((survivorTail_preserving P).iterate j).map_eq]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.DefectHitting
variable {Ω : Type*}
attribute [local instance] Classical.propDecidable

def walk (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : ℤ := ∑ j∈Finset.range n,(1-(X j x:ℤ))
def alive (X : ℕ → Ω → ℕ) (n : ℕ) : Set Ω := {x | ∀ k  ≤  n,walk X k x  ≤  0}
def stoppedSum (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : ℝ :=
  ∑ j∈Finset.range n,(alive X j).indicator (fun x => 1-(X j x:ℝ)) x

lemma walk_succ (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) :
    walk X (n+1) x=walk X n x+1-X n x := by simp [walk,Finset.sum_range_succ]; ring
lemma alive_zero (X : ℕ → Ω → ℕ) (x : Ω) : x∈alive X 0 := by simp [alive,walk]
lemma alive_succ {X : ℕ → Ω → ℕ} {n : ℕ} {x : Ω} :
    x∈alive X (n+1) ↔ x∈alive X n ∧ walk X (n+1) x ≤ 0 := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h _ le_rfl⟩
  · rintro ⟨h,h'⟩ k hk
    rcases lt_or_eq_of_le hk with hh | rfl
    · exact h k (by omega)
    · exact h'
lemma stoppedSum_eq (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) :
    stoppedSum X n x=if x∈alive X n then (walk X n x:ℝ) else 1 := by
  classical
  induction n with
  | zero => simp [stoppedSum,walk,alive_zero]
  | succ n ih =>
    rw [stoppedSum,Finset.sum_range_succ]
    change stoppedSum X n x+_= _
    rw [ih]
    by_cases hn : x∈alive X n
    · rw [ite_eq_left hn,Set.indicator_of_mem hn]
      by_cases hs : walk X (n+1) x ≤ 0
      · rw [ite_eq_left (alive_succ.mpr ⟨hn,hs⟩),walk_succ]
        push_cast; ring
      · rw [ite_eq_right (fun h => hs (alive_succ.mp h).2)]
        have hle := hn n le_rfl
        have hw := walk_succ X n x
        have he : walk X (n+1) x=1 := by omega
        have he' : walk X n x+1-(X n x:ℤ)=1 := hw.symm.trans he
        have hh := congrArg (fun z : ℤ => (z:ℝ)) he'
        push_cast at hh
        linarith
    · rw [ite_eq_right hn,Set.indicator_of_notMem hn,
        ite_eq_right (fun h => hn (alive_succ.mp h).1),add_zero]
lemma stoppedSum_le_one (X : ℕ → Ω → ℕ) (n : ℕ) (x : Ω) : stoppedSum X n x ≤ 1 := by
  rw [stoppedSum_eq]
  split_ifs with h
  · have hh := h n le_rfl
    exact (Int.cast_nonpos.mpr hh).trans (by norm_num)
  · exact le_rfl

variable [MeasurableSpace Ω]

@[instance_reducible] def past (X : ℕ → Ω → ℕ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ j∈Set.Iio n,MeasurableSpace.comap (X j) inferInstance
lemma past_le {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) (n : ℕ) : past X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup_le fun j => iSup_le fun _ => (hX j).comap_le
omit [MeasurableSpace Ω] in
lemma measurable_walk_prefix (X : ℕ → Ω → ℕ) (n k : ℕ) (hk : k ≤ n) : Measurable[past X n] (walk X k) := by
  apply Finset.measurable_sum
  intro j hj
  simp only [Finset.mem_range] at hj
  have hm : Measurable[past X n] (X j) := measurable_iff_comap_le.mpr
    (le_iSup_of_le j (le_iSup_of_le (show j∈Set.Iio n by simp only [Set.mem_Iio]; omega) le_rfl))
  exact measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k:ℤ))).comp hm)
omit [MeasurableSpace Ω] in
lemma measurableSet_alive_prefix (X : ℕ → Ω → ℕ) (n : ℕ) : MeasurableSet[past X n] (alive X n) := by
  simp only [alive,Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
    measurableSet_le (measurable_walk_prefix X n k hk) measurable_const
lemma measurableSet_alive {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) (n : ℕ) : MeasurableSet (alive X n) :=
  past_le hX n _ (measurableSet_alive_prefix X n)
lemma alive_indep_next {X : ℕ → Ω → ℕ} {μ : Measure Ω}
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ) (n : ℕ) :
    IndepFun ((alive X n).indicator (fun _ => (1:ℝ))) (X n) μ := by
  have h := indep_iSup_of_disjoint (fun j => (hX j).comap_le) hi
    (show Disjoint (Set.Iio n) ({n}:Set ℕ) by simp)
  have hh : Indep (past X n) (MeasurableSpace.comap (X n) inferInstance) μ := by
    simpa only [iSup_singleton,past] using h
  exact indep_of_indep_of_le_left hh (measurable_const.indicator (measurableSet_alive_prefix X n)).comap_le

lemma integral_alive_increment {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) (n : ℕ) :
    (∫ x,(alive X n).indicator (fun x => 1-(X n x:ℝ)) x ∂μ)=
      μ.real (alive X n)*(1-∫ x,(X n x:ℝ) ∂μ) := by
  have hind := (alive_indep_next hX hi n).comp measurable_id
    (measurable_of_countable (fun k : ℕ => (1:ℝ)-k))
  have hf : Integrable ((alive X n).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_alive hX n)
  have hg : Integrable (fun x => (1:ℝ)-X n x) μ := (integrable_const 1).sub (hint n)
  have h := hind.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable
  change (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x*(1-X n x) ∂μ)=
    (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x ∂μ)*(∫ x,(1:ℝ)-X n x ∂μ) at h
  have he : (fun x => (alive X n).indicator (fun _ => (1:ℝ)) x*(1-X n x))=
      (alive X n).indicator (fun x => (1:ℝ)-X n x) := by
    funext x
    by_cases hx : x∈alive X n <;> simp [hx]
  rw [he] at h
  rw [integral_indicator_const (1:ℝ) (measurableSet_alive hX n),integral_sub (integrable_const 1) (hint n)] at h
  simpa only [smul_eq_mul,mul_one,integral_const,probReal_univ,one_smul] using h

theorem bounded_wald_bound {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (n : ℕ) :
    (1-m)*(∑ j∈Finset.range n,μ.real (alive X j)) ≤ 1 := by
  have hint' (j : ℕ) : Integrable ((alive X j).indicator (fun x => 1-(X j x:ℝ))) μ :=
    ((integrable_const 1).sub (hint j)).indicator (measurableSet_alive hX j)
  have he : (∫ x,stoppedSum X n x ∂μ)=(1-m)*(∑ j∈Finset.range n,μ.real (alive X j)) := by
    unfold stoppedSum
    rw [integral_finsetSum _ (fun j _ => hint' j)]
    simp_rw [integral_alive_increment hX hi hint,hmean]
    rw [← Finset.sum_mul,mul_comm]
  rw [← he]
  have h := integral_mono (integrable_finsetSum _ (fun j _ => hint' j)) (integrable_const 1)
    (stoppedSum_le_one X n)
  simpa only [stoppedSum,integral_const,probReal_univ,one_smul] using h

lemma integral_alive_length {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) (n : ℕ) :
    (∫ x,(alive X n).indicator (fun x => 1+(X n x:ℝ)) x ∂μ)=
      μ.real (alive X n)*(1+∫ x,(X n x:ℝ) ∂μ) := by
  have hind := (alive_indep_next hX hi n).comp measurable_id
    (measurable_of_countable (fun k : ℕ => (1:ℝ)+k))
  have hf : Integrable ((alive X n).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (measurableSet_alive hX n)
  have hg : Integrable (fun x => (1:ℝ)+X n x) μ := (integrable_const 1).add (hint n)
  have h := hind.integral_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable
  change (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x*(1+X n x) ∂μ)=
    (∫ x,(alive X n).indicator (fun _ => (1:ℝ)) x ∂μ)*(∫ x,(1:ℝ)+X n x ∂μ) at h
  have he : (fun x => (alive X n).indicator (fun _ => (1:ℝ)) x*(1+X n x))=
      (alive X n).indicator (fun x => (1:ℝ)+X n x) := by
    funext x
    by_cases hx : x∈alive X n <;> simp [hx]
  rw [he] at h
  rw [integral_indicator_const (1:ℝ) (measurableSet_alive hX n),integral_add (integrable_const 1) (hint n)] at h
  simpa only [smul_eq_mul,mul_one,integral_const,probReal_univ,one_smul] using h

def totalLength (X : ℕ → Ω → ℕ) (x : Ω) : ℝ≥0∞ :=
  ∑' j : ℕ,(alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x

lemma measurable_totalLength {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) : Measurable (totalLength X) := by
  exact Measurable.tsum (fun j =>
    (measurable_const.add ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp (hX j))).indicator
      (measurableSet_alive hX j))

lemma totalLength_expectation {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    (∫⁻ x,totalLength X x ∂μ) ≤ ENNReal.ofReal ((1+m)/(1-m)) := by
  have hn : 0  ≤  m := by rw [← hmean 0]; exact integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hb (n : ℕ) : (∑ j∈Finset.range n,μ.real (alive X j)) ≤ 1/(1-m) := by
    apply (le_div_iff₀ (sub_pos.mpr hm)).mpr
    simpa [mul_comm] using bounded_wald_bound hX hi hint hmean n
  have hs := summable_of_sum_range_le (fun j => (measureReal_nonneg : 0 ≤ μ.real (alive X j))) hb
  have hs' := hs.mul_right (1+m)
  have he (j : ℕ) : (∫⁻ x,(alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x ∂μ)=
      ENNReal.ofReal (μ.real (alive X j)*(1+m)) := by
    rw [← hmean j,← integral_alive_length hX hi hint]
    rw [ofReal_integral_eq_lintegral_ofReal
      (f := fun x => (alive X j).indicator (fun x => (1:ℝ)+(X j x:ℝ)) x)
      (((integrable_const 1).add (hint j)).indicator (measurableSet_alive hX j))
      (Eventually.of_forall (fun x => by
        change (0:ℝ)  ≤  (alive X j).indicator (fun x => (1:ℝ)+(X j x:ℝ)) x
        by_cases hx : x∈alive X j
        · rw [Set.indicator_of_mem hx]; positivity
        · rw [Set.indicator_of_notMem hx]))]
    apply lintegral_congr
    intro x
    by_cases hx : x∈alive X j
    · simp [hx,ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 1) (Nat.cast_nonneg _)]
    · simp [hx]
  unfold totalLength
  rw [lintegral_tsum (f := fun j x => (alive X j).indicator (fun x => (1+(X j x:ℝ≥0∞))) x) (fun j =>
    ((measurable_const.add ((measurable_of_countable (fun k : ℕ => (k:ℝ≥0∞))).comp (hX j))).indicator
      (measurableSet_alive hX j)).aemeasurable)]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg measureReal_nonneg (by linarith)) hs',
    hs.tsum_mul_right]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑' j,μ.real (alive X j))*(1+m)  ≤  (1/(1-m))*(1+m) :=
      mul_le_mul_of_nonneg_right (hs.tsum_le_of_sum_range_le hb) (by linarith)
    _ = (1+m)/(1-m) := by ring

lemma totalLength_finite {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    ∀ᵐ x ∂μ,totalLength X x<∞ :=
  ae_lt_top (measurable_totalLength hX)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (totalLength_expectation hX hi hint hmean hm))

omit [MeasurableSpace Ω] in
lemma hit_of_totalLength_finite {X : ℕ → Ω → ℕ} {x : Ω} (h : totalLength X x<∞) :
    ∃ n,x∉alive X n := by
  by_contra hh
  push Not at hh
  have hle : (∑' _j : ℕ,(1:ℝ≥0∞)) ≤ totalLength X x :=
    ENNReal.tsum_le_tsum (fun j => by simp only [Set.indicator_of_mem (hh j)]; exact le_self_add)
  have he : (∑' _j : ℕ,(1:ℝ≥0∞))=∞ := by simp
  rw [he] at hle
  exact (not_le_of_gt h) hle

lemma integrable_totalLength {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    Integrable (fun x => (totalLength X x).toReal) μ :=
  (integrable_toReal_iff (measurable_totalLength hX).aemeasurable
    ((totalLength_finite hX hi hint hmean hm).mono (fun _ h => h.ne))).mpr
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (totalLength_expectation hX hi hint hmean hm))

omit [MeasurableSpace Ω] in
lemma alive_antitone (X : ℕ → Ω → ℕ) {n k : ℕ} (h : n ≤ k) : alive X k ⊆ alive X n :=
  fun _ hx j hj => hx j (hj.trans h)

def stopPredicate (X : ℕ → Ω → ℕ) (x : Ω) (n : ℕ) : Prop :=
  x∉alive X n ∨ ∀ k,x∈alive X k
omit [MeasurableSpace Ω] in
lemma stop_exists (X : ℕ → Ω → ℕ) (x : Ω) : ∃ n,stopPredicate X x n := by
  by_cases h : ∃ n,x∉alive X n
  · obtain ⟨n,hn⟩ := h; exact ⟨n,Or.inl hn⟩
  · exact ⟨0,Or.inr (by simpa only [not_exists,not_not] using h)⟩
def stopIndex (X : ℕ → Ω → ℕ) (x : Ω) : ℕ := Nat.find (stop_exists X x)

lemma measurable_stopIndex {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) : Measurable (stopIndex X) := by
  apply measurable_find (stop_exists X)
  intro n
  simp only [stopPredicate,Set.ofPred_or,Set.ofPred_forall]
  exact (measurableSet_alive hX n).compl.union (MeasurableSet.iInter (fun k => measurableSet_alive hX k))

omit [MeasurableSpace Ω] in
lemma stop_spec {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    x∉alive X (stopIndex X x) ∧ ∀ k<stopIndex X x,x∈alive X k := by
  have hn : ¬∀ k,x∈alive X k := by simpa only [not_forall] using hx
  refine ⟨(Nat.find_spec (stop_exists X x)).resolve_right hn,?_⟩
  intro k hk
  have hh := Nat.find_min (stop_exists X x) hk
  exact not_not.mp (fun h => hh (Or.inl h))

omit [MeasurableSpace Ω] in
lemma stop_eq_zero_of_no_hit {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∀ n,x∈alive X n) : stopIndex X x=0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' (stop_exists X x) (Or.inr hx))

omit [MeasurableSpace Ω] in
lemma walk_at_stop {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    walk X (stopIndex X x) x=1 := by
  obtain ⟨hn,hbefore⟩ := stop_spec hx
  have hpos : 0<stopIndex X x := by
    by_contra hh
    have he : stopIndex X x=0 := by omega
    exact hn (he ▸ alive_zero X x)
  obtain ⟨n,hn'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have ha : x∈alive X n := hbefore n (by omega)
  have hneg : ¬walk X (n+1) x ≤ 0 := by
    intro h; exact hn (hn' ▸ alive_succ.mpr ⟨ha,h⟩)
  have hh := ha n le_rfl
  rw [hn',walk_succ] at *
  omega

omit [MeasurableSpace Ω] in
lemma totalLength_eq_sum {X : ℕ → Ω → ℕ} {x : Ω} (hx : ∃ n,x∉alive X n) :
    totalLength X x=∑ j∈Finset.range (stopIndex X x),(1+(X j x:ℝ≥0∞)) := by
  obtain ⟨hn,hbefore⟩ := stop_spec hx
  unfold totalLength
  rw [tsum_eq_sum (s := Finset.range (stopIndex X x)) (fun j hj => ?_)]
  · exact Finset.sum_congr rfl (fun j hj => Set.indicator_of_mem (hbefore j (Finset.mem_range.mp hj)) _)
  · exact Set.indicator_of_notMem (fun h => hn (alive_antitone X (by simpa only [Finset.mem_range,not_lt] using hj) h)) _

def stoppedLength (X : ℕ → Ω → ℕ) (x : Ω) : ℕ :=
  ∑ j∈Finset.range (stopIndex X x),(1+X j x)

lemma measurable_stoppedLength {X : ℕ → Ω → ℕ} (hX : ∀ j,Measurable (X j)) : Measurable (stoppedLength X) := by
  have hf (n : ℕ) : Measurable (fun x => ∑ j∈Finset.range n,(1+X j x)) :=
    Finset.measurable_sum _ (fun j _ => measurable_const.add (hX j))
  have hp : Measurable (fun z : ℕ × Ω => ∑ j∈Finset.range z.1,(1+X j z.2)) :=
    measurable_from_prod_countable_right hf
  exact hp.comp ((measurable_stopIndex hX).prodMk measurable_id)

omit [MeasurableSpace Ω] in
lemma totalLength_toReal (X : ℕ → Ω → ℕ) (x : Ω) :
    (totalLength X x).toReal=(stoppedLength X x:ℝ) := by
  by_cases hx : ∃ n,x∉alive X n
  · rw [totalLength_eq_sum hx]
    have he : (∑ j∈Finset.range (stopIndex X x),(1+(X j x:ℝ≥0∞)))=(stoppedLength X x:ℝ≥0∞) := by
      simp only [stoppedLength,Nat.cast_sum,Nat.cast_add,Nat.cast_one]
    rw [he,ENNReal.toReal_natCast]
  · have hn : ∀ n,x∈alive X n := by simpa only [not_exists,not_not] using hx
    have he : totalLength X x=∞ := by
      apply eq_top_iff.mpr
      calc
        ∞ = ∑' _j : ℕ,(1:ℝ≥0∞) := by simp
        _  ≤  totalLength X x := ENNReal.tsum_le_tsum (fun j => by
          simp only [Set.indicator_of_mem (hn j)]; exact le_self_add)
    simp only [he,ENNReal.toReal_top,stoppedLength,stop_eq_zero_of_no_hit hn,Finset.range_zero,
      Finset.sum_empty,Nat.cast_zero]

lemma integrable_stoppedLength {X : ℕ → Ω → ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : ∀ j,Measurable (X j)) (hi : iIndepFun X μ)
    (hint : ∀ j,Integrable (fun x => (X j x:ℝ)) μ) {m : ℝ}
    (hmean : ∀ j,(∫ x,(X j x:ℝ) ∂μ)=m) (hm : m<1) :
    Integrable (fun x => (stoppedLength X x:ℝ)) μ := by
  simpa only [totalLength_toReal] using integrable_totalLength hX hi hint hmean hm

end FKCRT.DefectHitting
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance : MeasurableSpace (List Letter) := ⊤
instance : MeasurableSingletonClass (List Letter) := ⟨fun _ => trivial⟩

def parsingK (j : ℕ) (x : ℕ → Letter) : ℕ := (parsingData j x).1
lemma measurable_parsingK (j : ℕ) : Measurable (parsingK j) :=
  measurable_K.comp (measurable_survivorTail.iterate j)
lemma parsingK_iid (P : Parameters) : iIndepFun parsingK (streamLaw P ℕ) :=
  (parsingData_iid P).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
lemma parsingK_identDistrib (P : Parameters) (j : ℕ) :
    IdentDistrib (parsingK j) K (streamLaw P ℕ) (streamLaw P ℕ) :=
  (parsingData_identDistrib P j).comp measurable_fst
lemma integrable_parsingK (P : Parameters) (j : ℕ) :
    Integrable (fun x => (parsingK j x:ℝ)) (streamLaw P ℕ) :=
  ((parsingK_identDistrib P j).comp (measurable_of_countable (fun k : ℕ => (k:ℝ)))).integrable_iff.mpr (integrable_K P)
lemma integral_parsingK (P : Parameters) (j : ℕ) :
    (∫ x,(parsingK j x:ℝ) ∂streamLaw P ℕ)=(∫ x,(K x:ℝ) ∂streamLaw P ℕ) :=
  ((parsingK_identDistrib P j).comp (measurable_of_countable (fun k : ℕ => (k:ℝ)))).integral_eq

def allParsingFinite (x : ℕ → Letter) : Prop := ∀ j,firstSurvivor (survivorTail^[j] x)≠⊤
lemma ae_allParsingFinite (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,allParsingFinite x := by
  apply ae_all_iff.mpr
  intro j
  exact ((survivorTail_preserving P).iterate j).quasiMeasurePreserving.ae (firstSurvivor_finite P)

def parsingLength (x : ℕ → Letter) : ℕ := (firstSurvivor x).untopD 0+1
def parsingOffset : ℕ → (ℕ → Letter) → ℕ
  | 0,_ => 0
  | n+1,x => parsingOffset n x+parsingLength (survivorTail^[n] x)
def rawChunk (j : ℕ) (x : ℕ → Letter) : List Letter :=
  revealed (survivorTail^[j] x) (parsingLength (survivorTail^[j] x))
def shortPrefix : ℕ → (ℕ → Letter) → List Letter
  | 0,_ => []
  | n+1,x => normalWord (reduce (rawChunk n x))++shortPrefix n x

def leftSteps (x : ℕ → Letter) : ℕ := DefectHitting.stopIndex parsingK x
def leftWord (x : ℕ → Letter) : List Letter := revealed x (parsingOffset (leftSteps x) x)
def shortLeftWord (x : ℕ → Letter) : List Letter := shortPrefix (leftSteps x) x

lemma parsingTail_eq (j : ℕ) (x : ℕ → Letter) : survivorTail^[j] x=tail (parsingOffset j x) x := by
  induction j with
  | zero => exact (tail_zero x).symm
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change tail (parsingLength (survivorTail^[j] x)) (survivorTail^[j] x)=_
    conv_lhs => rw [ih]
    rw [tail_tail]
    simp only [parsingOffset,ih]
lemma revealed_offset_succ (j : ℕ) (x : ℕ → Letter) :
    revealed x (parsingOffset (j+1) x)=rawChunk j x++revealed x (parsingOffset j x) := by
  rw [parsingOffset,revealed_add,← parsingTail_eq]
  rfl
lemma run_shortPrefix (j : ℕ) (x : ℕ → Letter) (e : Evaluation) :
    run (shortPrefix j x) e=run (revealed x (parsingOffset j x)) e := by
  induction j generalizing e with
  | zero => rfl
  | succ j ih => rw [shortPrefix,run_append,run_normalWord,ih,revealed_offset_succ,run_append]
lemma run_shortLeftWord (x : ℕ → Letter) (e : Evaluation) : run (shortLeftWord x) e=run (leftWord x) e :=
  run_shortPrefix (leftSteps x) x e

lemma parsing_shape {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    ∃ b,reduce (revealed x (parsingLength x))=⟨List.replicate (K x) (some (!b)),[b]⟩ := by
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp h
  have hh : firstSurvivor x=WithTop.some n := hn.symm
  obtain ⟨b,hb,ho⟩ := firstSurvivor_shape hh
  have hlen : parsingLength x=n+1 := by simp only [parsingLength,hh]; rfl
  refine ⟨b,?_⟩
  rw [hlen,hb,K_of_hit hh,hb]
  congr 1
  exact List.eq_replicate_of_mem ho

lemma normal_parsing_length {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    (normalWord (reduce (revealed x (parsingLength x)))).length=1+K x := by
  obtain ⟨b,hb⟩ := parsing_shape h
  simp only [hb,normalWord,List.length_append,List.length_map,List.length_replicate,
    List.length_reverse,List.length_singleton,Nat.add_comm]

lemma signSum_add (x : ℕ → Letter) (n k : ℕ) :
    signSum x (n+k)=signSum x n+signSum (tail n x) k := by
  rw [← revealed_sum,revealed_add,List.map_append,List.sum_append,revealed_sum,revealed_sum,add_comm]
lemma signSum_parsing {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    signSum x (parsingLength x)=1-(K x:ℤ) := by
  obtain ⟨b,hb⟩ := parsing_shape h
  have he := reduce_imbalance (revealed x (parsingLength x))
  rw [hb,imbalance,List.length_singleton,List.length_replicate,revealed_sum] at he
  exact he.symm
lemma signSum_before_parsing {x : ℕ → Letter} (h : firstSurvivor x≠⊤) {k : ℕ}
    (hk : k<parsingLength x) : signSum x k≤0 := by
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp h
  have hh : firstSurvivor x=WithTop.some n := hn.symm
  have hlen : parsingLength x=n+1 := by simp only [parsingLength,hh]; rfl
  by_contra hp
  have hb : (reduce (revealed x k)).burgers≠[] := survivor_of_sum_pos _ (by rw [revealed_sum]; omega)
  cases k with
  | zero => simp [revealed_zero,reduce,run] at hb
  | succ k =>
    have he := (firstSurvivor_le_iff x k).mpr hb
    rw [hh] at he
    have hnk := WithTop.coe_le_coe.mp he
    omega

lemma signSum_offset {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) :
    signSum x (parsingOffset j x)=DefectHitting.walk parsingK j x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parsingOffset,signSum_add,← parsingTail_eq,signSum_parsing (hx j),ih,DefectHitting.walk_succ]
    change _+(1-(parsingK j x:ℤ))=_+1-parsingK j x
    ring
lemma shortPrefix_length {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) :
    (shortPrefix j x).length=∑ i∈Finset.range j,(1+parsingK i x) := by
  induction j with
  | zero => simp [shortPrefix]
  | succ j ih =>
    rw [shortPrefix,List.length_append,ih,Finset.sum_range_succ]
    have hh := normal_parsing_length (hx j)
    change (normalWord (reduce (rawChunk j x))).length=1+parsingK j x at hh
    omega
lemma shortLeftWord_length {x : ℕ → Letter} (hx : allParsingFinite x) :
    (shortLeftWord x).length=DefectHitting.stoppedLength parsingK x := shortPrefix_length hx _

lemma signSum_nonpos_prefix {x : ℕ → Letter} (hx : allParsingFinite x) (n : ℕ)
    (hwalk : ∀ j<n,DefectHitting.walk parsingK j x≤0) :
    ∀ k<parsingOffset n x,signSum x k≤0 := by
  induction n with
  | zero => simp [parsingOffset]
  | succ n ih =>
    intro k hk
    by_cases hkn : k<parsingOffset n x
    · exact ih (fun j hj => hwalk j (by omega)) k hkn
    · have hle : parsingOffset n x≤k := by omega
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [signSum_add,← parsingTail_eq,signSum_offset hx]
      have hr : r<parsingLength (survivorTail^[n] x) := by rw [parsingOffset] at hk; omega
      exact add_nonpos (hwalk n (by omega)) (signSum_before_parsing (hx n) hr)

lemma ae_left_first_hit (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    signSum x (parsingOffset (leftSteps x) x)=1 ∧
      ∀ k<parsingOffset (leftSteps x) x,signSum x k≤0 := by
  filter_upwards [ae_allParsingFinite P,
    DefectHitting.totalLength_finite measurable_parsingK (parsingK_iid P)
      (integrable_parsingK P) (integral_parsingK P) (integral_K_lt_one P)] with x hx hf
  have hh := DefectHitting.hit_of_totalLength_finite hf
  refine ⟨(signSum_offset hx _).trans (DefectHitting.walk_at_stop hh),?_⟩
  apply signSum_nonpos_prefix hx
  intro j hj
  exact (DefectHitting.stop_spec hh).2 j hj j le_rfl

lemma measurable_shortLeftWord : Measurable shortLeftWord := by
  have hmL : Measurable parsingLength :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0+1)).comp measurable_firstSurvivor
  have hmc (j : ℕ) : Measurable (rawChunk j) := by
    have hr : Measurable (fun z : ℕ × (ℕ → Letter) => revealed z.2 z.1) :=
      measurable_from_prod_countable_right (fun n => (measurable_of_countable (fun y : Fin n → Letter => (List.ofFn y).reverse)).comp
        (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ))))
    exact hr.comp ((hmL.comp (measurable_survivorTail.iterate j)).prodMk (measurable_survivorTail.iterate j))
  have hms (j : ℕ) : Measurable (shortPrefix j) := by
    induction j with
    | zero => exact measurable_const
    | succ j ih =>
      exact (measurable_of_countable (fun z : List Letter × List Letter => normalWord (reduce z.1)++z.2)).comp ((hmc j).prodMk ih)
  have hf : Measurable (fun z : ℕ × (ℕ → Letter) => shortPrefix z.1 z.2) :=
    measurable_from_prod_countable_right hms
  exact hf.comp ((DefectHitting.measurable_stopIndex measurable_parsingK).prodMk measurable_id)

/-- Source ladder:short-length for the actual first-hit left ladder word,
shortened by the proved reduction-preserving parsing. No E J is used. -/
theorem integrable_shortLeftWord_length (P : Parameters) :
    Integrable (fun x => ((shortLeftWord x).length:ℝ)) (streamLaw P ℕ) := by
  have hh := DefectHitting.integrable_stoppedLength measurable_parsingK (parsingK_iid P)
    (integrable_parsingK P) (integral_parsingK P) (integral_K_lt_one P)
  exact hh.congr ((ae_allParsingFinite P).mono (fun x hx => by change (DefectHitting.stoppedLength parsingK x:ℝ)=((shortLeftWord x).length:ℝ); rw [shortLeftWord_length hx]))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma K_flip (x : ℕ → Letter) : K (flipStream x)=K x := by
  simp only [K,firstSurvivor_flip,revealed_flip,reduce_flip,Evaluation.flip,List.length_map]
lemma tail_flip (n : ℕ) (x : ℕ → Letter) : tail n (flipStream x)=flipStream (tail n x) := rfl
lemma survivorTail_flip (x : ℕ → Letter) : survivorTail (flipStream x)=flipStream (survivorTail x) := by
  simp only [survivorTail,firstSurvivor_flip,tail_flip]
lemma iterate_survivorTail_flip (j : ℕ) (x : ℕ → Letter) :
    survivorTail^[j] (flipStream x)=flipStream (survivorTail^[j] x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,survivorTail_flip]
lemma parsingK_flip (j : ℕ) (x : ℕ → Letter) : parsingK j (flipStream x)=parsingK j x := by
  change K (survivorTail^[j] (flipStream x))=K (survivorTail^[j] x)
  rw [iterate_survivorTail_flip,K_flip]
lemma leftSteps_flip (x : ℕ → Letter) : leftSteps (flipStream x)=leftSteps x := by
  classical
  unfold leftSteps DefectHitting.stopIndex
  apply Nat.find_congr'
  intro n
  simp only [DefectHitting.stopPredicate,DefectHitting.alive,Set.mem_ofPred_eq,DefectHitting.walk,parsingK_flip]
lemma normalWord_flip (e : Evaluation) : normalWord e.flip=(normalWord e).map Letter.flip := by
  simp only [normalWord,Evaluation.flip,List.map_append,List.map_map,← List.map_reverse,Function.comp_def]
  rfl
lemma rawChunk_flip (j : ℕ) (x : ℕ → Letter) : rawChunk j (flipStream x)=(rawChunk j x).map Letter.flip := by
  simp only [rawChunk,iterate_survivorTail_flip,parsingLength,firstSurvivor_flip,revealed_flip]
lemma shortPrefix_flip (j : ℕ) (x : ℕ → Letter) : shortPrefix j (flipStream x)=(shortPrefix j x).map Letter.flip := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shortPrefix,rawChunk_flip,reduce_flip,normalWord_flip,ih,shortPrefix,List.map_append]
lemma shortLeftWord_flip (x : ℕ → Letter) : shortLeftWord (flipStream x)=(shortLeftWord x).map Letter.flip := by
  rw [shortLeftWord,leftSteps_flip,shortPrefix_flip]; rfl

def Letter.typeNet (b : Bool) : Letter → ℤ
  | .burger c => if c=b then 1 else 0
  | .order (some c) => if c=b then -1 else 0
  | .order none => 0

def typeNet (b : Bool) (w : List Letter) : ℤ := (w.map (Letter.typeNet b)).sum

def FixedWord (w : List Letter) : Prop := Letter.order none∉w

lemma Letter.typeNet_flip (b : Bool) (a : Letter) : Letter.typeNet b a.flip=Letter.typeNet (!b) a := by
  cases a with
  | burger c => cases b <;> cases c <;> rfl
  | order c => cases c with
    | none => rfl
    | some c => cases b <;> cases c <;> rfl
lemma typeNet_flip (b : Bool) (w : List Letter) : typeNet b (w.map Letter.flip)=typeNet (!b) w := by
  simp only [typeNet,List.map_map,Function.comp_def,Letter.typeNet_flip]
lemma Letter.abs_typeNet_le (b : Bool) (a : Letter) : |Letter.typeNet b a| ≤ 1 := by
  cases a with
  | burger c => simp only [Letter.typeNet]; split_ifs <;> norm_num
  | order c => cases c with
    | none => norm_num [Letter.typeNet]
    | some c => simp only [Letter.typeNet]; split_ifs <;> norm_num
lemma abs_typeNet_le (b : Bool) (w : List Letter) : |typeNet b w| ≤ w.length := by
  induction w with
  | nil => simp [typeNet]
  | cons a w ih =>
    change |Letter.typeNet b a+typeNet b w| ≤ (w.length+1:ℕ)
    have ha := Letter.abs_typeNet_le b a
    have ht := abs_add_le (Letter.typeNet b a) (typeNet b w)
    push_cast
    omega
lemma typeNet_total (w : List Letter) (hw : FixedWord w) :
    typeNet false w+typeNet true w=(w.map Letter.increment).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    have hh := ih (fun h => hw (List.mem_cons_of_mem a h))
    have he : Letter.typeNet false a+Letter.typeNet true a=a.increment := by
      cases a with
      | burger b => cases b <;> rfl
      | order o => cases o with
        | none => exact (ha rfl).elim
        | some b => cases b <;> rfl
    change (Letter.typeNet false a+typeNet false w)+(Letter.typeNet true a+typeNet true w)=a.increment+(w.map Letter.increment).sum
    omega

lemma fixed_normal_parsing {x : ℕ → Letter} (hx : firstSurvivor x≠⊤) :
    FixedWord (normalWord (reduce (revealed x (parsingLength x)))) := by
  obtain ⟨b,hb⟩ := parsing_shape hx
  simp only [FixedWord,hb,normalWord,List.map_replicate,List.map_reverse,List.map_cons,List.map_nil]
  simp
lemma fixed_shortPrefix {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) : FixedWord (shortPrefix j x) := by
  induction j with
  | zero => simp [FixedWord,shortPrefix]
  | succ j ih =>
    change Letter.order none∉normalWord (reduce (rawChunk j x))++shortPrefix j x
    simpa only [FixedWord,rawChunk,List.mem_append,not_or] using And.intro (fixed_normal_parsing (hx j)) ih
lemma fixed_shortLeftWord {x : ℕ → Letter} (hx : allParsingFinite x) : FixedWord (shortLeftWord x) :=
  fixed_shortPrefix hx _
lemma shortLeftWord_sign (x : ℕ → Letter) :
    ((shortLeftWord x).map Letter.increment).sum=signSum x (parsingOffset (leftSteps x) x) := by
  rw [← reduce_imbalance,reduce,run_shortLeftWord,← reduce]
  rw [reduce_imbalance]
  exact revealed_sum _ _
lemma ae_short_typeNet_total (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    typeNet false (shortLeftWord x)+typeNet true (shortLeftWord x)=1 := by
  filter_upwards [ae_allParsingFinite P,ae_left_first_hit P] with x hx hh
  rw [typeNet_total _ (fixed_shortLeftWord hx),shortLeftWord_sign,hh.1]
lemma integrable_short_typeNet (P : Parameters) (b : Bool) :
    Integrable (fun x => (typeNet b (shortLeftWord x):ℝ)) (streamLaw P ℕ) := by
  apply (integrable_shortLeftWord_length P).mono'
    (((measurable_of_countable (fun w : List Letter => (typeNet b w:ℝ))).comp measurable_shortLeftWord).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    change |(typeNet b (shortLeftWord x):ℝ)| ≤ ((shortLeftWord x).length:ℝ)
    exact_mod_cast abs_typeNet_le b (shortLeftWord x))

/-- Each genuine shortened L-piece has expected net count 1/2 of either type. -/
theorem integral_short_typeNet (P : Parameters) (b : Bool) :
    (∫ x,(typeNet b (shortLeftWord x):ℝ) ∂streamLaw P ℕ)=1/2 := by
  have he := (flipStream_preserving P).hasLaw.integral_comp (integrable_short_typeNet P false).aestronglyMeasurable
  change (∫ x,(typeNet false (shortLeftWord (flipStream x)):ℝ) ∂streamLaw P ℕ)=_ at he
  simp only [shortLeftWord_flip,typeNet_flip,Bool.not_false] at he
  have ht : (∫ x,(typeNet false (shortLeftWord x):ℝ) ∂streamLaw P ℕ)+
      (∫ x,(typeNet true (shortLeftWord x):ℝ) ∂streamLaw P ℕ)=1 := by
    rw [← integral_add (integrable_short_typeNet P false) (integrable_short_typeNet P true)]
    have hh : (fun x => (typeNet false (shortLeftWord x):ℝ)+(typeNet true (shortLeftWord x):ℝ))=ᵐ[streamLaw P ℕ] fun _ => (1:ℝ) :=
      (ae_short_typeNet_total P).mono (fun x hx => by change (typeNet false (shortLeftWord x):ℝ)+(typeNet true (shortLeftWord x):ℝ)=1; exact_mod_cast hx)
    rw [integral_congr_ae hh]
    simp
  cases b <;> linarith

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def shortLeftLaw (P : Parameters) : Measure (List Letter) :=
  (streamLaw P ℕ).map shortLeftWord
lemma shortLeft_hasLaw (P : Parameters) : HasLaw shortLeftWord (shortLeftLaw P) (streamLaw P ℕ) :=
  ⟨measurable_shortLeftWord.aemeasurable,rfl⟩
instance shortLeftLaw_probability (P : Parameters) : IsProbabilityMeasure (shortLeftLaw P) := by
  unfold shortLeftLaw
  infer_instance

lemma shortLeftLaw_length_integrable (P : Parameters) :
    Integrable (fun w : List Letter => (w.length:ℝ)) (shortLeftLaw P) := by
  rw [shortLeftLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_shortLeftWord.aemeasurable]
  exact integrable_shortLeftWord_length P
lemma shortLeftLaw_typeNet_integrable (P : Parameters) (b : Bool) :
    Integrable (fun w : List Letter => (typeNet b w:ℝ)) (shortLeftLaw P) := by
  rw [shortLeftLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_shortLeftWord.aemeasurable]
  exact integrable_short_typeNet P b
lemma shortLeftLaw_typeNet_mean (P : Parameters) (b : Bool) :
    (∫ w,(typeNet b w:ℝ) ∂shortLeftLaw P)=1/2 := by
  rw [← (shortLeft_hasLaw P).integral_comp (measurable_of_countable _).aestronglyMeasurable]
  exact integral_short_typeNet P b
lemma shortLeftLaw_fixed (P : Parameters) : ∀ᵐ w ∂shortLeftLaw P,FixedWord w := by
  rw [shortLeftLaw,ae_map_iff measurable_shortLeftWord.aemeasurable ((Set.to_countable _).measurableSet)]
  exact (ae_allParsingFinite P).mono (fun x hx => fixed_shortLeftWord hx)

lemma firstSurvivor_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    firstSurvivor x=WithTop.some 0 := by
  apply le_antisymm
  · apply (firstSurvivor_le_iff x 0).mpr
    simp [revealed,reduce,run,step,hx]
  · exact bot_le
lemma parsingLength_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    parsingLength x=1 := by rw [parsingLength,firstSurvivor_of_burger hx]; rfl
lemma K_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) : K x=0 := by
  rw [K_of_hit (firstSurvivor_of_burger hx)]
  simp [revealed,reduce,run,step,hx]
lemma leftSteps_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) : leftSteps x=1 := by
  classical
  have hk : parsingK 0 x=0 := K_of_burger hx
  have hwalk : DefectHitting.walk parsingK 1 x=1 := by
    rw [DefectHitting.walk_succ]
    simp only [DefectHitting.walk,Finset.range_zero,Finset.sum_empty,hk,Nat.cast_zero,zero_add,sub_zero]
  have hnot : x∉DefectHitting.alive parsingK 1 := by
    intro h
    have hh := h 1 le_rfl
    rw [hwalk] at hh
    norm_num at hh
  have hle : leftSteps x ≤ 1 := Nat.find_min' (DefectHitting.stop_exists parsingK x) (Or.inl hnot)
  have hpos : 0<leftSteps x := by
    have hh := (DefectHitting.stop_spec ⟨1,hnot⟩).1
    change x∉DefectHitting.alive parsingK (leftSteps x) at hh
    by_contra hn
    have hz : leftSteps x=0 := by omega
    rw [hz] at hh
    exact hh (by simp [DefectHitting.alive,DefectHitting.walk,Finset.range_zero,Finset.sum_empty])
  omega
lemma shortLeftWord_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    shortLeftWord x=[Letter.burger b] := by
  rw [shortLeftWord,leftSteps_of_burger hx,shortPrefix]
  simp [rawChunk,parsingLength_of_burger hx,shortPrefix,revealed,reduce,run,step,hx,normalWord]

lemma shortLeftLaw_burger_positive (P : Parameters) (b : Bool) :
    0<shortLeftLaw P {w | w=[Letter.burger b]} := by
  rw [shortLeftLaw,Measure.map_apply measurable_shortLeftWord ((Set.to_countable _).measurableSet)]
  have hle : streamLaw P ℕ {x | x 0=Letter.burger b} ≤
      streamLaw P ℕ (shortLeftWord ⁻¹' {w | w=[Letter.burger b]}) :=
    measure_mono (fun x hx => shortLeftWord_of_burger hx)
  have he : streamLaw P ℕ {x | x 0=Letter.burger b}=(law P).toMeasure {Letter.burger b} :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).measure_preimage
      (measurableSet_singleton (Letter.burger b)).nullMeasurableSet
  rw [he,law_singleton] at hle
  exact (ENNReal.ofReal_pos.mpr (mass_pos P _)).trans_le hle

end FKCRT.Inventory
end

end OAI
