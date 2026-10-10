import OAI.Probability.DirectionalWalk.AxisBridges

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def appendTapeList {α : Type*} (a b : TapeList α) : TapeList α :=
  ⟨a.1+b.1,Fin.append a.2 b.2⟩

lemma listHeight_append {α : Type*} (L : α → ℕ) (a b : TapeList α) :
    listHeight L (appendTapeList a b) = listHeight L a + listHeight L b := by
  change (∑ i : Fin (a.1+b.1), L (Fin.append a.2 b.2 i)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  rfl

lemma listProduct_append {α M : Type*} [CommMonoid M] (f : α → M) (a b : TapeList α) :
    (∏ i : Fin (appendTapeList a b).1, f ((appendTapeList a b).2 i)) =
      (∏ i : Fin a.1, f (a.2 i)) * ∏ i : Fin b.1, f (b.2 i) := by
  change (∏ i : Fin (a.1+b.1), f (Fin.append a.2 b.2 i)) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]

lemma tapeCylinder_append {α : Type*} (a b : TapeList α) (Z : ℕ → α) :
    Z ∈ tapeCylinder (appendTapeList a b) ↔
      Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ tapeCylinder b := by
  constructor
  · intro h
    refine ⟨fun i => ?_,fun i => ?_⟩
    · simpa [appendTapeList] using h (i.castAdd b.1)
    · simpa [appendTapeList] using h (i.natAdd a.1)
  · rintro ⟨ha,hb⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [appendTapeList] using ha j
    · simpa [appendTapeList] using hb j

lemma appendTapeList_cut_recover {α : Type*} (L : α → ℕ) (H J : ℕ)
    (Z : ℕ → α) (hZ : ∀ i, 0 < L (Z i)) (a b : TapeList α)
    (ha : listHeight L a = H) (hb : listHeight L b = J)
    (h : Z ∈ tapeCylinder (appendTapeList a b)) :
    cutList L H Z = a ∧ cutList L J (fun j => Z (a.1+j)) = b := by
  have hh := (tapeCylinder_append a b Z).mp h
  exact ⟨((cutList_atom_iff L H Z hZ a).mpr ⟨ha,hh.1⟩).2,
    ((cutList_atom_iff L J _ (fun i => hZ _) b).mpr ⟨hb,hh.2⟩).2⟩

lemma bridgeList_pair_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) (a b : TapeList α) :
    ((bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)) {(a,b)} =
      if listHeight L a = H ∧ listHeight L b = J then
        Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder (appendTapeList a b)) else 0 := by
  classical
  have ht : ({(a,b)} : Set (TapeList α × TapeList α)) = {a} ×ˢ {b} := by ext p; simp
  rw [ht,Measure.prod_prod,bridgeListMeasure_atom ν L hL,bridgeListMeasure_atom ν L hL,
    tapeCylinder_mass,listProduct_append (fun x => ν {x}) a b]
  split_ifs <;> simp_all

lemma measure_le_of_singleton_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P Q : Measure α) (h : ∀ a, P {a} ≤ Q {a}) : P ≤ Q := by
  classical
  apply Measure.le_iff.mpr
  intro s hs
  rw [← Measure.tsum_indicator_apply_singleton P s hs,← Measure.tsum_indicator_apply_singleton Q s hs]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ s <;> simp only [Set.indicator_apply,ha,ite_true,ite_false]
  · exact h a
  · exact le_rfl

lemma bridgeListMeasure_append_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    (((bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)).map
      (fun p => appendTapeList p.1 p.2)) ≤ bridgeListMeasure ν L (H+J) := by
  classical
  apply measure_le_of_singleton_le
  intro c
  let P := (bridgeListMeasure ν L H).prod (bridgeListMeasure ν L J)
  let f : TapeList α × TapeList α → ℝ≥0∞ := fun p =>
    if appendTapeList p.1 p.2 = c then P {p} else 0
  have he : (P.map (fun p => appendTapeList p.1 p.2)) {c} = ∑' p, f p := by
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      ← Measure.tsum_indicator_apply_singleton P _ ((measurable_of_countable _) (measurableSet_singleton _))]
    apply tsum_congr
    intro p
    simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    rfl
  change (P.map (fun p => appendTapeList p.1 p.2)) {c} ≤ _
  rw [he]
  by_cases hf : ∃ p, f p ≠ 0
  · obtain ⟨p,hp⟩ := hf
    have hac : appendTapeList p.1 p.2 = c := by
      by_contra h
      exact hp (by simp [f,h])
    have hab : listHeight L p.1 = H ∧ listHeight L p.2 = J := by
      by_contra h
      exact hp (by simp [f,hac,P,bridgeList_pair_atom ν L hL,h])
    have hpc : P {p} = Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder c) := by
      dsimp only [P]
      rw [bridgeList_pair_atom ν L hL,ite_eq_left hab,hac]
    have hpos : Measure.infinitePi (fun _ : ℕ => ν) (tapeCylinder c) ≠ 0 := by
      simpa only [f,ite_eq_left hac,hpc] using hp
    obtain ⟨Z,hZc,hZ⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae (ae_tape_prop ν (fun a => 0 < L a)
        (measurableSet_lt measurable_const (measurable_of_countable L)) hL))
    have hpR := appendTapeList_cut_recover L H J Z hZ p.1 p.2 hab.1 hab.2 (hac.symm ▸ hZc)
    have hzero : ∀ q ≠ p, f q = 0 := by
      intro q hqp
      by_contra hq
      have hqc : appendTapeList q.1 q.2 = c := by
        by_contra h
        exact hq (by simp [f,h])
      have hqH : listHeight L q.1 = H ∧ listHeight L q.2 = J := by
        by_contra h
        exact hq (by simp [f,hqc,P,bridgeList_pair_atom ν L hL,h])
      have hqR := appendTapeList_cut_recover L H J Z hZ q.1 q.2 hqH.1 hqH.2 (hqc.symm ▸ hZc)
      have h1 : q.1 = p.1 := hqR.1.symm.trans hpR.1
      have h2 : q.2 = p.2 := by rw [h1] at hqR; exact hqR.2.symm.trans hpR.2
      exact hqp (Prod.ext h1 h2)
    rw [tsum_eq_single p hzero]
    have hc : listHeight L c = H+J := by rw [← hac,listHeight_append,hab.1,hab.2]
    rw [bridgeListMeasure_atom ν L hL,ite_eq_left hc]
    rw [show f p = P {p} by simp [f,hac],hpc,tapeCylinder_mass]
  · push Not at hf
    simp only [hf,tsum_zero,zero_le]

lemma bridgeListLaw_append_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    (((bridgeListLaw ν L H).prod (bridgeListLaw ν L J)).map
      (fun p => appendTapeList p.1 p.2)) ≤
      ((Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J))⁻¹) •
        bridgeListMeasure ν L (H+J) := by
  let : IsFiniteMeasure (bridgeListMeasure ν L H) := by unfold bridgeListMeasure; infer_instance
  let : IsFiniteMeasure (bridgeListMeasure ν L J) := by unfold bridgeListMeasure; infer_instance
  rw [bridgeListLaw,bridgeListLaw,Measure.prod_smul_left,Measure.prod_smul_right,
    smul_smul,Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply,smul_eq_mul]
  simpa only [mul_comm] using
    mul_le_mul_left ((Measure.le_iff.mp (bridgeListMeasure_append_le ν L hL H J)) s hs)
      ((Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J))⁻¹)

lemma bridgeListLaw_join_raw_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H J : ℕ) :
    letI := slabLaw_probability μ v hp
    (((bridgeListLaw (slabLaw μ v) (slabRecords v) H).prod
      (bridgeListLaw (slabLaw μ v) (slabRecords v) J)).map
      (fun p => concatenateList (appendTapeList p.1 p.2))) ≤
      ((Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) J))⁻¹) •
        rawBridgeMeasure μ v (H+J) := by
  let := slabLaw_probability μ v hp
  have hL : ∀ᵐ a ∂slabLaw μ v, 0 < slabRecords v a := by
    filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with a ha
    exact slabRecords_pos v a ha
  have h := Measure.map_mono (bridgeListLaw_append_le (slabLaw μ v) (slabRecords v) hL H J)
    (measurable_of_countable concatenateList)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    bridgeListMeasure_concatenate μ hell v hv hp] at h
  exact h

lemma product_contact_domination {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (n N H J : ℕ)
    (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1)
    (P Q : Measure (Word d)) (a b : ℝ≥0∞) (hb : b ≠ ∞)
    (hP : P ≤ a • rawBridgeMeasure μ (axisDirection e) H)
    (hQ : Q ≤ b • rawBridgeMeasure μ (axisDirection (oppositeStep e)) J) :
    P.prod Q (bridgeWordContact z) ≤ a*b *
      (2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N))) := by
  let : IsFiniteMeasure (rawBridgeMeasure μ (axisDirection e) H) := by
    unfold rawBridgeMeasure; infer_instance
  let : IsFiniteMeasure (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J) := by
    unfold rawBridgeMeasure; infer_instance
  have : Fact (b < ∞) := ⟨hb.lt_top⟩
  have hh := Measure.le_iff.mp (Measure.prod_mono hP hQ) (bridgeWordContact z)
    (Set.to_countable _).measurableSet
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.smul_apply,smul_eq_mul] at hh
  refine hh.trans ?_
  simpa only [mul_comm] using mul_le_mul_left
    (rawBridgeMeasure_contact_le μ hell e z n N H J hH hJ hn hn' hz) (a*b)

lemma bridgeListLaw_reverse_pair {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    ((bridgeListLaw ν L H).prod (bridgeListLaw ν L J)).map
      (Prod.map reverseTapeList reverseTapeList) =
        (bridgeListLaw ν L H).prod (bridgeListLaw ν L J) := by
  rw [← Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    bridgeListLaw_reverse ν L hL,bridgeListLaw_reverse ν L hL]

lemma bridgeListLaw_join_reversed_raw_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H J : ℕ) :
    letI := slabLaw_probability μ v hp
    (((bridgeListLaw (slabLaw μ v) (slabRecords v) H).prod
      (bridgeListLaw (slabLaw μ v) (slabRecords v) J)).map
      (fun p => concatenateList (appendTapeList (reverseTapeList p.1) (reverseTapeList p.2)))) ≤
      ((Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) H))⁻¹ *
       (Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (renewalCut (slabRecords v) J))⁻¹) •
        rawBridgeMeasure μ v (H+J) := by
  let := slabLaw_probability μ v hp
  have hL : ∀ᵐ a ∂slabLaw μ v, 0 < slabRecords v a := by
    filter_upwards [ae_slabLaw_regeneration μ hell v hv hp] with a ha
    exact slabRecords_pos v a ha
  have he := congrArg (fun M : Measure (TapeList (Word d) × TapeList (Word d)) =>
    M.map (fun p => concatenateList (appendTapeList p.1 p.2)))
    (bridgeListLaw_reverse_pair (slabLaw μ v) (slabRecords v) hL H J)
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at he
  exact he.le.trans (bridgeListLaw_join_raw_le μ hell v hv hp H J)

lemma signedThreeKernel_proj12 {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0)
    (H : ℕ × (ℕ × ℕ)) :
    (signedThreeKernel ν L H).map (fun a => (a.1,a.2.1)) =
      (bridgeListLaw ν L H.1).prod (bridgeListLaw ν L H.2.1) := by
  let : ∀ h, IsProbabilityMeasure (bridgeListLaw ν L h) := fun h => bridgeListLaw_probability ν L h (hu h)
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun h => bridgeListLaw_probability ν L h (hu h)⟩
  simp only [signedThreeKernel,Kernel.parallelComp_apply]
  change _ = (bridgeListLaw ν L H.1).prod (bridgeListLaw ν L H.2.1)
  change ((bridgeListLaw ν L H.1).prod
    ((bridgeListLaw ν L H.2.1).prod (bridgeListLaw ν L H.2.2))).map (Prod.map id Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst,Measure.map_id,
    Measure.map_fst_prod,measure_univ,one_smul]

lemma signedThreeKernel_proj32 {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hu : ∀ H, Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) ≠ 0)
    (H : ℕ × (ℕ × ℕ)) :
    (signedThreeKernel ν L H).map (fun a => (a.2.2,a.2.1)) =
      (bridgeListLaw ν L H.2.2).prod (bridgeListLaw ν L H.2.1) := by
  let : ∀ h, IsProbabilityMeasure (bridgeListLaw ν L h) := fun h => bridgeListLaw_probability ν L h (hu h)
  let : IsMarkovKernel (oneBridgeKernel ν L) := ⟨fun h => bridgeListLaw_probability ν L h (hu h)⟩
  simp only [signedThreeKernel,Kernel.parallelComp_apply]
  change ((bridgeListLaw ν L H.1).prod
    ((bridgeListLaw ν L H.2.1).prod (bridgeListLaw ν L H.2.2))).map (Prod.swap ∘ Prod.snd) = _
  rw [← Measure.map_map measurable_swap measurable_snd,Measure.map_snd_prod,
    measure_univ,one_smul,Measure.prod_swap]

end DirectionalZeroOne

end OAI
