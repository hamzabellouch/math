import OAI.Probability.DirectionalWalk.FreshContacts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma quenched_axis_exit_sum {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (k N : ℤ) (hkN : k ≤ N) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ y,
      quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N)) +
        quenchedKernel d (ω,y) (hitBefore (axisUpper e N) (axisLower e k)) = 1 := by
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ∀ y, ∀ᵐ X ∂quenchedKernel d (ω,y),
      ∃ n, X n ∈ axisLower e k ∪ axisUpper e N := by
    rw [ae_all_iff]
    intro y
    apply annealed_ae_quenched μ y
    · change MeasurableSet {X : Path d | ∃ n, X n ∈ axisLower e k ∪ axisUpper e N}
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun n : ℕ =>
        (Set.to_countable (axisLower e k ∪ axisUpper e N)).measurableSet.preimage
          (measurable_pi_apply (X := fun _ : ℕ => Site d) n))
    · exact annealed_axis_exit μ hell e y k N
  filter_upwards [hAE] with ω hω
  intro y
  rw [← measure_union (hitBefore_disjoint _ _) (measurableSet_hitBefore _ _),
    hitBefore_union_eq_eventual _ _ (axis_barriers_disjoint e hkN)]
  have hm : MeasurableSet {X : Path d | ∃ n, X n ∈ axisLower e k ∪ axisUpper e N} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n : ℕ =>
      (Set.to_countable (axisLower e k ∪ axisUpper e N)).measurableSet.preimage
        (measurable_pi_apply (X := fun _ : ℕ => Site d) n))
  exact (mem_ae_iff_prob_eq_one hm).mp (hω y)

lemma shiftPath_preimage_hitBefore {d : ℕ} (z : Site d) (A B : Set (Site d)) :
    shiftPath z ⁻¹' hitBefore A B = hitBefore ((fun x => x+z) ⁻¹' A) ((fun x => x+z) ⁻¹' B) := by
  rfl

lemma axis_barriers_from_top {d : ℕ} (e : Step d) (z : Site d) (N n : ℕ)
    (hz : axisHeight e z = (N : ℤ)-1) :
    (fun x => x+z) ⁻¹' axisUpper e N = axisLower (oppositeStep e) 0 ∧
    (fun x => x+z) ⁻¹' axisLower e 0 = axisUpper (oppositeStep e) N ∧
    (fun x => x+z) ⁻¹' axisLower e ((N : ℤ)-n) = axisUpper (oppositeStep e) n := by
  refine ⟨?_,?_,?_⟩ <;> ext x <;>
    simp only [axisLower,axisUpper,Set.mem_preimage,Set.mem_ofPred_eq,axisHeight_add,
      axisHeight_opposite,hz] <;> omega

lemma annealed_axis_return_from_top {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) {n N : ℕ} (hnN : n ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) :
    annealed μ z (hitBefore (axisLower e ((N : ℤ)-n)) (axisUpper e N) ∩
      hitBefore (axisUpper e N) (axisLower e 0)) =
      axisReachProb μ (oppositeStep e) n - axisReachProb μ (oppositeStep e) N := by
  have hs := annealed_shift μ 0 z
  rw [zero_add] at hs
  rw [← hs,Measure.map_apply (measurable_shiftPath z)
    ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _)),
    Set.preimage_inter,shiftPath_preimage_hitBefore,shiftPath_preimage_hitBefore,
    (axis_barriers_from_top e z N n hz).1,(axis_barriers_from_top e z N n hz).2.1,
    (axis_barriers_from_top e z N n hz).2.2]
  exact annealed_axis_return_probability μ hell (oppositeStep e) hnN

lemma firstContactPairs_axis_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (T : Set (Site d))
    {n N : ℕ} (hnN : n ≤ N) (hz : axisHeight e z = (N : ℤ)-1) :
    ((annealed μ 0).prod (annealed μ z))
      (⋃ p : firstContactPairs T (axisUpper e n) (axisLower e ((N : ℤ)-n))
        (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val) ≤
      2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N)) := by
  have h := firstContactPairs_raw_bound μ 0 z T (axisUpper e n) (axisLower e ((N : ℤ)-n))
    (axisLower e 0) (axisUpper e N) (quenched_axis_exit_sum μ hell e 0 N (by positivity))
  rw [annealed_axis_return_probability μ hell e hnN,
    annealed_axis_return_from_top μ hell e z hnN hz] at h
  exact h

def translateWord {d : ℕ} (z : Site d) (a : Word d) : Word d :=
  ⟨a.1,fun i => a.2 i + z⟩

lemma wordPath_translate {d : ℕ} (z : Site d) (a : Word d) (i : ℕ) (hi : i ≤ a.1) :
    wordPath (translateWord z a) i = wordPath a i + z := by
  simp [wordPath,translateWord,extendPrefix,Finset.mem_Iic,hi]

lemma wordEnd_translate {d : ℕ} (z : Site d) (a : Word d) :
    wordEnd (translateWord z a) = wordEnd a + z := wordPath_translate z a a.1 le_rfl

def AxisBridgeWord {d : ℕ} (e : Step d) (H : ℕ) (a : Word d) : Prop :=
  axisHeight e (wordEnd a) = (H : ℤ) ∧
    ∀ i < a.1, 0 ≤ axisHeight e (wordPath a i) ∧ axisHeight e (wordPath a i) < (H : ℤ)

lemma axisBridgeWord_recordWord {d : ℕ} (e : Step d) (H : ℕ) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) (hH : X ∈ reachRecord (axisDirection e) H) :
    AxisBridgeWord e H (recordWord (axisDirection e) H X) := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hH
  have hh := axis_record_height e X n h0 (fun i _ => axisHeight_nn_le e X hX i) hn.1
  rw [hn.2.1] at hh
  rw [recordWord_eq (axisDirection e) H X hn]
  dsimp only [AxisBridgeWord]
  constructor
  · change axisHeight e (wordPath (prefixWord n X) n) = _
    rw [wordPath_prefixWord n X le_rfl,hh]
  · intro i hi
    change i < n at hi
    rw [wordPath_prefixWord n X hi.le]
    constructor
    · have h := hn.2.2 i hi.le
      rw [height_axisDirection] at h
      exact_mod_cast h
    · rcases hn.1 with rfl | hr
      · omega
      · have h := hr.2 i hi
        rw [height_axisDirection,height_axisDirection,hh] at h
        exact_mod_cast h

lemma rawBridgeMeasure_axis_supported {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) :
    ∀ᵐ a ∂rawBridgeMeasure μ (axisDirection e) H, AxisBridgeWord e H a := by
  rw [rawBridgeMeasure,ae_map_iff (measurable_recordWord _ _).aemeasurable
    (Set.to_countable _).measurableSet]
  filter_upwards [ae_restrict_of_ae (ae_start_and_nearestNeighbour μ 0),
    ae_restrict_mem (measurableSet_reachRecord (axisDirection e) H)] with X hX hH
  exact axisBridgeWord_recordWord e H X hX.1 hX.2 hH

lemma AxisBridgeWord.firstHit {d : ℕ} {e : Step d} {H : ℕ} {a : Word d}
    (ha : AxisBridgeWord e H a) : firstHitWord (axisUpper e H) a := by
  exact ⟨ha.1.ge,fun i hi => not_le_of_gt (ha.2 i hi).2⟩

lemma firstContactPairs_of_bridge_contact {d : ℕ} (e : Step d) (z : Site d)
    (n N H J : ℕ) (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) (a b : Word d)
    (ha : AxisBridgeWord e H a) (hb : AxisBridgeWord (oppositeStep e) J b)
    (hc : ∃ i < a.1, ∃ j < b.1, wordPath a i = wordPath b j + z)
    (X Y : Path d) (hX : X ∈ wordCylinder a) (hY : Y ∈ wordCylinder (translateWord z b)) :
    (X,Y) ∈ ⋃ p : firstContactPairs (axisUpper e H) (axisUpper e n)
      (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val := by
  classical
  have hex : ∃ j, Y j ∈ wordDepartures a := by
    obtain ⟨i,hi,j,hj,hij⟩ := hc
    refine ⟨j,i,hi,?_⟩
    rw [hY j hj.le,wordPath_translate z b j hj.le,hij]
  let j := Nat.find hex
  have hj : Y j ∈ wordDepartures a := Nat.find_spec hex
  have hjb : j < b.1 := by
    obtain ⟨i,hi,k,hk,hik⟩ := hc
    have hYk : Y k ∈ wordDepartures a := ⟨i,hi,by rw [hY k hk.le,wordPath_translate z b k hk.le,hik]⟩
    exact (Nat.find_min' hex hYk).trans_lt hk
  have hjmin : ∀ k < j, Y k ∉ wordDepartures a := fun k hk => Nat.find_min hex hk
  let c := prefixWord j Y
  have hcend : wordEnd c = Y j := wordPath_prefixWord j Y le_rfl
  have hcf : firstHitWord (wordDepartures a) c := by
    refine ⟨?_,fun k hk => ?_⟩
    · rw [hcend]; exact hj
    · rw [wordPath_prefixWord j Y hk.le]
      exact hjmin k hk
  have hYband : ∀ k ≤ j, (N : ℤ)-J ≤ axisHeight e (Y k) ∧ axisHeight e (Y k) < N := by
    intro k hk
    have hb' := hb.2 k (hk.trans_lt hjb)
    rw [axisHeight_opposite] at hb'
    rw [hY k (hk.trans hjb.le),wordPath_translate z b k (hk.trans hjb.le),axisHeight_add,hz]
    omega
  obtain ⟨i,hi,hij⟩ := hj
  have hR : wordPath a i ∈ axisUpper e n := by
    have hband := (hYband j le_rfl).1
    change (n : ℤ) ≤ _
    rw [hij]
    omega
  have hS : wordEnd c ∈ axisLower e ((N : ℤ)-n) := by
    rw [hcend,← hij]
    have hu := (ha.2 i hi).2
    change axisHeight e (wordPath a i) < (N : ℤ)-n
    omega
  have hp : (a,c) ∈ firstContactPairs (axisUpper e H) (axisUpper e n)
      (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N) := by
    refine ⟨ha.firstHit,hcf,⟨i,hi,hij.trans hcend.symm,⟨i,le_rfl,hR⟩,?_⟩,
      ⟨j,le_rfl,hS⟩,?_⟩
    · intro k hk hK
      have hb := ha.2 k (hk.trans_lt hi)
      rcases hK with hK | hK
      · change axisHeight e (wordPath a k) < 0 at hK; omega
      · change (N : ℤ) ≤ axisHeight e (wordPath a k) at hK; omega
    · intro k hk hK
      rw [wordPath_prefixWord j Y hk] at hK
      have hb := hYband k hk
      rcases hK with hK | hK
      · change axisHeight e (Y k) < 0 at hK; omega
      · change (N : ℤ) ≤ axisHeight e (Y k) at hK; omega
  refine Set.mem_iUnion.mpr ⟨⟨(a,c),hp⟩,hX,?_⟩
  rw [wordCylinder_prefixWord]
  exact fun _ _ => rfl

def bridgeWordContact {d : ℕ} (z : Site d) : Set (Word d × Word d) :=
  {p | ∃ i < p.1.1, ∃ j < p.2.1, wordPath p.1 i = wordPath p.2 j + z}

lemma translate_wordCylinder {d : ℕ} (z : Site d) (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) : shiftPath z X ∈ wordCylinder (translateWord z a) := by
  intro i hi
  change X i + z = _
  rw [wordPath_translate z a i hi,hX i hi]

lemma rawBridgeMeasure_contact_le {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (z : Site d) (n N H J : ℕ)
    (hH : H ≤ N) (hJ : J ≤ N) (hn : n+J ≤ N) (hn' : n+H ≤ N)
    (hz : axisHeight e z = (N : ℤ)-1) :
    ((rawBridgeMeasure μ (axisDirection e) H).prod
      (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J)) (bridgeWordContact z) ≤
      2*((axisReachProb μ e n-axisReachProb μ e N) +
        (axisReachProb μ (oppositeStep e) n-axisReachProb μ (oppositeStep e) N)) := by
  let A := ⋃ p : firstContactPairs (axisUpper e H) (axisUpper e n)
    (axisLower e ((N : ℤ)-n)) (axisLower e 0 ∪ axisUpper e N), wordPairCylinder p.val
  have hA : MeasurableSet A := MeasurableSet.iUnion (fun p => measurableSet_wordPairCylinder p.val)
  have hs : ((annealed μ 0).prod (annealed μ 0)).map (Prod.map id (shiftPath z)) =
      (annealed μ 0).prod (annealed μ z) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_shiftPath z),Measure.map_id]
    have hh := annealed_shift μ 0 z
    rw [zero_add] at hh
    rw [hh]
  have hp : ((rawBridgeMeasure μ (axisDirection e) H).prod
      (rawBridgeMeasure μ (axisDirection (oppositeStep e)) J)) (bridgeWordContact z) ≤
      ((annealed μ 0).prod (annealed μ z)) A := by
    rw [rawBridgeMeasure,rawBridgeMeasure,Measure.map_prod_map _ _ (measurable_recordWord _ _)
      (measurable_recordWord _ _),Measure.map_apply
      ((measurable_recordWord _ _).prodMap (measurable_recordWord _ _)) (Set.to_countable _).measurableSet,
      Measure.prod_restrict,Measure.restrict_apply
      (((measurable_recordWord _ _).prodMap (measurable_recordWord _ _)) (Set.to_countable _).measurableSet),
      ← hs,Measure.map_apply (measurable_id.prodMap (measurable_shiftPath z)) hA]
    apply measure_mono_ae
    have hgood : ∀ᵐ p ∂(annealed μ 0).prod (annealed μ 0),
        (p.1 0 = 0 ∧ nearestNeighbour p.1) ∧ (p.2 0 = 0 ∧ nearestNeighbour p.2) :=
      (Measure.quasiMeasurePreserving_fst.ae (ae_start_and_nearestNeighbour μ 0)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_start_and_nearestNeighbour μ 0))
    filter_upwards [hgood] with p hp
    rintro ⟨hc,hpH,hpJ⟩
    have h1 := axisBridgeWord_recordWord e H p.1 hp.1.1 hp.1.2 hpH
    have h2 := axisBridgeWord_recordWord (oppositeStep e) J p.2 hp.2.1 hp.2.2 hpJ
    have hC1 := ((recordWord_atom (axisDirection e) H p.1 _).mp ⟨hpH,rfl⟩).2
    have hC2 := ((recordWord_atom (axisDirection (oppositeStep e)) J p.2 _).mp ⟨hpJ,rfl⟩).2
    exact firstContactPairs_of_bridge_contact e z n N H J hH hJ hn hn' hz _ _ h1 h2 hc _ _
      hC1 (translate_wordCylinder z _ _ hC2)
  exact hp.trans (firstContactPairs_axis_bound μ hell e z (axisUpper e H) (by omega) hz)

end DirectionalZeroOne

end OAI
