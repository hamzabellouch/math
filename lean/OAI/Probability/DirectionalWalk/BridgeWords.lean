import OAI.Probability.DirectionalWalk.RelativeEntropy

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def appendWord {d : ℕ} (a b : Word d) : Word d :=
  prefixWord (a.1+b.1) (concatPath a.1 (wordPath a)
    (shiftPath (wordPath a a.1) (wordPath b)))

lemma appendWord_length {d : ℕ} (a b : Word d) : (appendWord a b).1 = a.1+b.1 := rfl

lemma appendWord_before {d : ℕ} (a b : Word d) (hb : wordPath b 0 = 0)
    {i : ℕ} (hi : i ≤ a.1) : wordPath (appendWord a b) i = wordPath a i := by
  rw [appendWord,wordPath_prefixWord (a.1+b.1) _ (by omega)]
  apply concatPath_before _ _ _ _ hi
  simp [shiftPath,hb]

lemma appendWord_after {d : ℕ} (a b : Word d) {i : ℕ} (hi : i ≤ b.1) :
    wordPath (appendWord a b) (a.1+i) = wordPath a a.1 + wordPath b i := by
  rw [appendWord,wordPath_prefixWord (a.1+b.1) _ (Nat.add_le_add_left hi _),concatPath_after]
  exact add_comm _ _

lemma appendWord_prefixWord {d : ℕ} (X : Path d) (n m : ℕ) :
    appendWord (prefixWord n X) (prefixWord m (relativeTail n X)) = prefixWord (n+m) X := by
  apply (prefixWord_eq_iff _ _ _).mpr
  refine ⟨rfl,?_⟩
  intro i hi
  change i ≤ n+m at hi
  rw [wordPath_prefixWord (n+m) X hi]
  change concatPath n (wordPath (prefixWord n X))
    (shiftPath (wordPath (prefixWord n X) n) (wordPath (prefixWord m (relativeTail n X)))) i = X i
  by_cases hin : i ≤ n
  · rw [concatPath_before _ _ _ _ hin,wordPath_prefixWord _ _ hin]
    simp only [wordPath_prefixWord _ _ (le_refl _),wordPath_prefixWord _ _ (Nat.zero_le _),
      shiftPath,relativeTail_apply,Nat.add_zero,sub_self,zero_add]
  · have hn : n ≤ i := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [concatPath_after,shiftPath,wordPath_prefixWord _ _ (le_refl _),
      wordPath_prefixWord _ _ (by omega),relativeTail_apply]
    abel

def concatenateWords {d : ℕ} : (n : ℕ) → (Fin n → Word d) → Word d
  | 0, _ => prefixWord 0 (fun _ => 0)
  | n+1, a => appendWord (concatenateWords n (fun i => a i.castSucc)) (a (Fin.last n))

def concatenateList {d : ℕ} (a : TapeList (Word d)) : Word d := concatenateWords a.1 a.2

lemma concatenateWords_length {d : ℕ} (n : ℕ) (a : Fin n → Word d) :
    (concatenateWords n a).1 = ∑ i : Fin n, (a i).1 := by
  induction n with
  | zero => simp [concatenateWords,prefixWord]
  | succ n ih => simp only [concatenateWords,appendWord_length,ih,Fin.sum_univ_castSucc]

lemma concatenateList_prefix_slabs {d : ℕ} (v : Fin d → ℝ) (X : Path d) (h0 : X 0 = 0) (k : ℕ) :
    concatenateList (tapePrefix k (slabs v X)) = prefixWord (slabTime v X k) X := by
  induction k with
  | zero =>
    apply (prefixWord_eq_iff _ _ _).mpr
    refine ⟨rfl,?_⟩
    intro i hi
    change i ≤ 0 at hi
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    subst i
    simp [wordPath_prefixWord,h0]
  | succ k ih =>
    change appendWord (concatenateList (tapePrefix k (slabs v X))) (slabs v X k) = _
    rw [ih,slabTime_succ]
    have he : slabs v X k = prefixWord (slabs v X k).1 (relativeTail (slabTime v X k) X) := by
      change prefixWord (slabs v X k).1 ((cutSuffix v)^[k] X) = _
      rw [iterated_cutSuffix_eq_relativeTail v X h0 k]
    rw [he]
    exact appendWord_prefixWord X _ _

lemma concatenateList_length {d : ℕ} (a : TapeList (Word d)) :
    (concatenateList a).1 = listHeight (fun w => w.1) a := concatenateWords_length a.1 a.2

noncomputable def recordWord {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) : Word d := by
  classical
  exact if h : ∃ n, recordPrefix v H X n then prefixWord (Nat.find h) X else prefixWord 0 X

lemma recordWord_eq {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) {n : ℕ}
    (hn : recordPrefix v H X n) : recordWord v H X = prefixWord n X := by
  classical
  have hex : ∃ n, recordPrefix v H X n := ⟨n,hn⟩
  rw [recordWord,dite_eq_left hex]
  rw [recordPrefix_unique v H X (Nat.find_spec hex) hn]

lemma recordWord_atom {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d) (a : Word d) :
    (X ∈ reachRecord v H ∧ recordWord v H X = a) ↔
      recordPrefix v H (wordPath a) a.1 ∧ X ∈ pathCylinder a.1 (wordPath a) := by
  constructor
  · rintro ⟨hX,ha⟩
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
    rw [recordWord_eq v H X hn] at ha
    obtain ⟨rfl,hpre⟩ := (prefixWord_eq_iff n X a).mp ha
    exact ⟨recordPrefix_prefix v H hn (fun i hi => (hpre i hi).symm),hpre⟩
  · rintro ⟨ha,hX⟩
    have hr := recordPrefix_prefix v H ha hX
    exact ⟨Set.mem_iUnion.mpr ⟨a.1,hr⟩,
      (recordWord_eq v H X hr).trans ((prefixWord_eq_iff _ _ _).mpr ⟨rfl,hX⟩)⟩

lemma measurable_recordWord {d : ℕ} (v : Fin d → ℝ) (H : ℕ) : Measurable (recordWord v H) := by
  apply measurable_to_countable'
  intro a
  have he : recordWord v H ⁻¹' {a} =
      (if recordPrefix v H (wordPath a) a.1 then pathCylinder a.1 (wordPath a) else ∅) ∪
      ((reachRecord v H)ᶜ ∩ prefixWord 0 ⁻¹' {a}) := by
    classical
    ext X
    by_cases hX : X ∈ reachRecord v H
    · have hh := recordWord_atom v H X a
      simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_union,Set.mem_inter_iff,
        Set.mem_compl_iff,hX,not_true_eq_false,false_and,or_false,true_and] at hh ⊢
      split_ifs <;> simp_all
    · have hn : ¬∃ n, recordPrefix v H X n := by simpa only [reachRecord,Set.mem_iUnion,Set.mem_ofPred_eq] using hX
      have hrw : recordWord v H X = prefixWord 0 X := by simp only [recordWord,dite_eq_right hn]
      have hnot : recordPrefix v H (wordPath a) a.1 → X ∉ pathCylinder a.1 (wordPath a) := by
        intro ha hc
        exact hX ((recordWord_atom v H X a).mpr ⟨ha,hc⟩).1
      split_ifs <;> simp_all
  rw [he]
  apply MeasurableSet.union
  · split_ifs
    · exact measurableSet_pathCylinder _ _
    · exact MeasurableSet.empty
  · exact (measurableSet_reachRecord v H).compl.inter ((measurable_prefixWord 0) (measurableSet_singleton _))

lemma conditioned_recordWord_atom {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) (a : Word d) :
    conditioned μ v (recordTailEvent v H Set.univ ∩ recordWord v H ⁻¹' {a}) =
      annealed μ 0 (reachRecord v H ∩ recordWord v H ⁻¹' {a}) := by
  let := conditioned_probability μ v hp
  classical
  have he0 : reachRecord v H ∩ recordWord v H ⁻¹' {a} =
      if recordPrefix v H (wordPath a) a.1 then pathCylinder a.1 (wordPath a) else ∅ := by
    ext X
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff,recordWord_atom]
    split_ifs <;> simp_all
  have he1 : recordTailEvent v H Set.univ ∩ recordWord v H ⁻¹' {a} =
      if recordPrefix v H (wordPath a) a.1 then
        pathCylinder a.1 (wordPath a) ∩ relativeTail a.1 ⁻¹' (Set.univ ∩ nonBacktracking v) else ∅ := by
    ext X
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff]
    split_ifs with ha
    · constructor
      · rintro ⟨hX,hw⟩
        obtain ⟨n,hn,hD⟩ := Set.mem_iUnion.mp hX
        have hpre := ((recordWord_atom v H X a).mp ⟨Set.mem_iUnion.mpr ⟨n,hn⟩,hw⟩).2
        have hnn := recordPrefix_unique v H X hn (recordPrefix_prefix v H ha hpre)
        subst n
        exact ⟨hpre,hD⟩
      · rintro ⟨hpre,ht⟩
        have hr := recordPrefix_prefix v H ha hpre
        refine ⟨Set.mem_iUnion.mpr ⟨a.1,hr,ht⟩,?_⟩
        exact ((recordWord_atom v H X a).mpr ⟨ha,hpre⟩).2
    · constructor
      · rintro ⟨hX,hw⟩
        obtain ⟨n,hn,_⟩ := Set.mem_iUnion.mp hX
        exact ha ((recordWord_atom v H X a).mp ⟨Set.mem_iUnion.mpr ⟨n,hn⟩,hw⟩).1
      · exact False.elim
  rw [he0,he1]
  split_ifs with ha
  · rw [conditioned_recordCylinder μ v H a.1 (wordPath a) ha MeasurableSet.univ,measure_univ,mul_one]
  · simp only [measure_empty]

noncomputable def rawBridgeMeasure {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (H : ℕ) : Measure (Word d) :=
  ((annealed μ 0).restrict (reachRecord v H)).map (recordWord v H)

lemma rawBridgeMeasure_conditioned {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    ((conditioned μ v).restrict (recordTailEvent v H Set.univ)).map (recordWord v H) =
      rawBridgeMeasure μ v H := by
  apply Measure.ext_of_singleton
  intro a
  simp only [rawBridgeMeasure,Measure.map_apply (measurable_recordWord v H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_recordWord v H) (measurableSet_singleton _))]
  simpa only [Set.inter_comm] using conditioned_recordWord_atom μ v hp H a

lemma concatenate_cutList_slabs {d : ℕ} (v : Fin d → ℝ) (H : ℕ) (X : Path d)
    (hX : GoodSlabPath v X) (hH : slabs v X ∈ tapeCut v H) :
    concatenateList (cutList (slabRecords v) H (slabs v X)) = recordWord v H X := by
  obtain ⟨k,hk⟩ := hH
  have hpos : ∀ i, 0 < slabRecords v (slabs v X i) := fun i => slabRecords_pos v _ (hX.2 i)
  rw [cutList,cutListIndex_eq (slabRecords v) H (slabs v X) hpos hk,
    concatenateList_prefix_slabs v X hX.1 k]
  symm
  apply recordWord_eq
  refine ⟨(slabTime_boundary v X hX k).imp_right And.left,?_,fun i _ => ?_⟩
  · rw [recordCount_slabTime v X hX k]
    exact hk
  · exact goodSlabPath_height_nonneg v X hX i

lemma bridgeListMeasure_concatenate {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    letI := slabLaw_probability μ v hp
    (bridgeListMeasure (slabLaw μ v) (slabRecords v) H).map concatenateList =
      rawBridgeMeasure μ v H := by
  let := slabLaw_probability μ v hp
  let := conditioned_probability μ v hp
  rw [← rawBridgeMeasure_conditioned μ v hp H]
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable concatenateList) (measurableSet_singleton _),
    bridgeListMeasure,Measure.map_apply (measurable_cutList (slabRecords v) H)
      ((measurable_of_countable concatenateList) (measurableSet_singleton _)),
    Measure.restrict_apply ((measurable_cutList (slabRecords v) H)
      ((measurable_of_countable concatenateList) (measurableSet_singleton _))),
    ← slabs_map_eq_infinitePi μ hell v hv hp,
    Measure.map_apply (measurable_slabs v)
      (((measurable_cutList (slabRecords v) H)
        ((measurable_of_countable concatenateList) (measurableSet_singleton _))).inter
        (measurableSet_renewalCut (slabRecords v) H)),
    Measure.map_apply (measurable_recordWord v H) (measurableSet_singleton _),
    Measure.restrict_apply ((measurable_recordWord v H) (measurableSet_singleton _))]
  apply measure_congr
  filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
  apply propext
  change (concatenateList (cutList (slabRecords v) H (slabs v X)) = a ∧
    slabs v X ∈ tapeCut v H) ↔ (recordWord v H X = a ∧ X ∈ recordTailEvent v H Set.univ)
  constructor
  · rintro ⟨ha,hH⟩
    exact ⟨(concatenate_cutList_slabs v H X hX hH).symm.trans ha,
      (tapeCut_iff_recordTailEvent v X hX H).mp hH⟩
  · rintro ⟨ha,hH⟩
    have hc := (tapeCut_iff_recordTailEvent v X hX H).mpr hH
    exact ⟨(concatenate_cutList_slabs v H X hX hc).trans ha,hc⟩

end DirectionalZeroOne

end OAI
