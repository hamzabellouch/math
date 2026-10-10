import OAI.Probability.DirectionalWalk.FiniteContacts

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def finiteLateEndpointEvent {d ι : ℕ} (e : Step d) (k r N : ℕ) (z : Fin ι → Site d) :
    Set (Word d × Path d) :=
  {p | (∃ q, wordEnd p.1-stepVector e = z q) ∧ finiteLateContact e k r N p.1 p.2}

lemma measurableSet_finiteLateEndpointEvent {d ι : ℕ} (e : Step d) (k r N : ℕ)
    (z : Fin ι → Site d) : MeasurableSet (finiteLateEndpointEvent e k r N z) :=
  (measurable_fst (Set.to_countable {a : Word d | ∃ q, wordEnd a-stepVector e = z q}).measurableSet).inter
    (measurableSet_finiteLateContact e k r N)

lemma finiteLateContact_prefix {d : ℕ} (e : Step d) (k r N n : ℕ)
    (X Y : Path d) (h : finiteLateContact e k r N (prefixWord n X) Y) :
    ∃ t τ, t ≤ τ ∧ AxisBridgeWord e k (prefixWord t X) ∧
      (∀ j, t ≤ j → j ≤ τ → (k : ℤ) ≤ axisHeight e (X j) ∧ axisHeight e (X j) < (N : ℤ)) ∧
      (r : ℤ) ≤ axisHeight e (X τ) ∧
      (∃ j, Y j+(X n-stepVector e) = X τ) ∧
      (∀ i, t ≤ i → i < τ → ∀ j, Y j+(X n-stepVector e) ≠ X i) := by
  obtain ⟨t,τ,htτ,hτ,ha,hband,hr,hc,hb⟩ := h
  change τ < n at hτ
  have hpre : prefixWord t (wordPath (prefixWord n X)) = prefixWord t X := by
    apply (prefixWord_eq_iff t _ _).mpr
    refine ⟨rfl,fun i hi => ?_⟩
    rw [wordPath_prefixWord t X hi,wordPath_prefixWord n X (hi.trans (htτ.trans hτ.le))]
  rw [hpre] at ha
  have hend : wordEnd (prefixWord n X) = X n := wordPath_prefixWord n X le_rfl
  refine ⟨t,τ,htτ,ha,?_,?_,?_,?_⟩
  · intro j htj hjτ
    simpa only [wordPath_prefixWord n X (hjτ.trans hτ.le)] using hband j htj hjτ
  · simpa only [wordPath_prefixWord n X hτ.le] using hr
  · simpa only [hend,wordPath_prefixWord n X hτ.le] using hc
  · intro i hti hiτ j
    simpa only [hend,wordPath_prefixWord n X (hiτ.le.trans hτ.le)] using hb i hti hiτ j

lemma finite_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hzi : Function.Injective z)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (((axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N).prod
      (conditioned μ (axisDirection (oppositeStep e)))) (finiteLateEndpointEvent e k r N z) ≤
      (axisReachProb μ e N)⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let A := ProbabilityTheory.cond (annealed μ 0) (reachRecord (axisDirection e) N)
  let B := conditioned μ (axisDirection (oppositeStep e))
  have : IsFiniteMeasure B := by dsimp [B,conditioned];infer_instance
  let E : Fin ι → Set (Path d) := fun q =>
    {X | wordEnd (recordWord (axisDirection e) N X)-stepVector e = z q}
  have hE (q) : MeasurableSet (E q) :=
    measurable_recordWord (axisDirection e) N
      (Set.to_countable {a : Word d | wordEnd a-stepVector e = z q}).measurableSet
  have hdis : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro X hi hj
    exact hij (hzi (hi.symm.trans hj))
  have hmap : A.map (recordWord (axisDirection e) N) =
      (axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N := by
    dsimp only [A]
    rw [ProbabilityTheory.cond,
      Measure.map_smul _ (measurable_recordWord (axisDirection e) N).aemeasurable,
      ← axisReachProb_eq_record]
    rfl
  rw [← hmap,show (A.map (recordWord (axisDirection e) N)).prod B =
      (A.prod B).map (fun p => (recordWord (axisDirection e) N p.1,p.2)) from by
        simpa only [Measure.map_id,Measure.map_id',Prod.map_def,Function.id_def] using (Measure.map_prod_map A B
          (measurable_recordWord (axisDirection e) N) measurable_id),
    Measure.map_apply (show Measurable (fun p : Path d × Path d => (recordWord (axisDirection e) N p.1,p.2)) from
      ((measurable_recordWord (axisDirection e) N).comp measurable_fst).prodMk measurable_snd)
      (measurableSet_finiteLateEndpointEvent e k r N z)]
  refine (measure_mono_ae ?_).trans (conditioned_bridge_late_bound μ hell e k r N m hkr hrN E hE hdis z hz hΔ)
  have hreach : ∀ᵐ p ∂A.prod B, p.1 ∈ reachRecord (axisDirection e) N :=
    Measure.quasiMeasurePreserving_fst.ae (ProbabilityTheory.ae_cond_mem (measurableSet_reachRecord _ _))
  filter_upwards [hreach] with p hp hf
  obtain ⟨q,hq⟩ := hf.1
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hp
  have hword := recordWord_eq (axisDirection e) N p.1 hn
  have hfinite : finiteLateContact e k r N (prefixWord n p.1) p.2 := hword ▸ hf.2
  obtain ⟨t,τ,htτ,ha,hband,hr,hc,hb⟩ := finiteLateContact_prefix e k r N n p.1 p.2 hfinite
  have heq : p.1 n-stepVector e = z q := by
    change wordEnd (recordWord (axisDirection e) N p.1)-stepVector e = z q at hq
    rw [hword] at hq
    exact (wordPath_prefixWord n p.1 le_rfl ▸ hq)
  refine ⟨q,hq,t,τ,htτ,ha,hband,⟨τ,htτ,le_rfl,hr⟩,?_,?_⟩
  · simpa only [heq] using hc
  · simpa only [heq] using hb

lemma renewalCut_two_mass {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν]
    (L : α → ℕ) (hL : ∀ᵐ a ∂ν, 0 < L a) (H J : ℕ) :
    Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H ∩ renewalCut L (H+J)) =
      Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L H) *
        Measure.infinitePi (fun _ : ℕ => ν) (renewalCut L J) := by
  classical
  let P := Measure.infinitePi (fun _ : ℕ => ν)
  have hZ := ae_tape_prop ν (fun a => 0 < L a)
    (measurableSet_lt measurable_const (measurable_of_countable L)) hL
  have hf (a : TapeList α) :
      P ({Z | cutList L H Z = a} ∩ (renewalCut L H ∩ renewalCut L (H+J))) =
        P ({Z | cutList L H Z = a} ∩ renewalCut L H) * P (renewalCut L J) := by
    by_cases ha : listHeight L a = H
    · have h1 : P ({Z | cutList L H Z = a} ∩ (renewalCut L H ∩ renewalCut L (H+J))) =
          P {Z | Z ∈ tapeCylinder a ∧ (fun j => Z (a.1+j)) ∈ renewalCut L J} := by
        apply measure_congr
        filter_upwards [hZ] with Z hZ
        apply propext
        constructor
        · rintro ⟨hc,hs,ht⟩
          have hp := ((cutList_atom_iff L H Z hZ a).mp ⟨hs,hc⟩).2
          have hn : tapeHeight L Z a.1 = H := by
            rw [← listHeight_prefix,(tapePrefix_eq_iff _ _ _).mpr ⟨rfl,hp⟩,ha]
          exact ⟨hp,(renewalCut_add_iff L Z hZ hn J).mp ht⟩
        · rintro ⟨hp,ht⟩
          have hc := (cutList_atom_iff L H Z hZ a).mpr ⟨ha,hp⟩
          have hn : tapeHeight L Z a.1 = H := by
            rw [← listHeight_prefix,(tapePrefix_eq_iff _ _ _).mpr ⟨rfl,hp⟩,ha]
          exact ⟨hc.2,hc.1,(renewalCut_add_iff L Z hZ hn J).mpr ht⟩
      have h2 : P ({Z | cutList L H Z = a} ∩ renewalCut L H) = P (tapeCylinder a) := by
        apply measure_congr
        filter_upwards [hZ] with Z hZ
        apply propext
        constructor
        · rintro ⟨hc,hs⟩;exact ((cutList_atom_iff L H Z hZ a).mp ⟨hs,hc⟩).2
        · intro hp;have hc := (cutList_atom_iff L H Z hZ a).mpr ⟨ha,hp⟩;exact ⟨hc.2,hc.1⟩
      rw [h1,h2]
      exact (tapeCylinder_suffix_factorization ν a _ (measurableSet_renewalCut L J)).trans
        (by rw [tapeCylinder_mass])
    · have h0 : P ({Z | cutList L H Z = a} ∩ renewalCut L H) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hZ] with Z hZ hm
        exact ha ((cutList_atom_iff L H Z hZ a).mp ⟨hm.2,hm.1⟩).1
      rw [h0,zero_mul]
      apply measure_mono_null _ h0
      exact fun _ h => ⟨h.1,h.2.1⟩
  rw [measure_eq_tsum_fibres P (cutList L H) (measurable_cutList L H)
    ((measurableSet_renewalCut L H).inter (measurableSet_renewalCut L (H+J)))]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right,← measure_eq_tsum_fibres P (cutList L H)
    (measurable_cutList L H) (measurableSet_renewalCut L H)]

lemma axis_two_cuts_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (s N : ℕ) (hsN : s ≤ N) :
    letI := slabLaw_probability μ (axisDirection e) hp
    (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
      Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
        (tapeCut (axisDirection e) s ∩ tapeCut (axisDirection e) N) := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hL : ∀ᵐ a ∂slabLaw μ (axisDirection e), 0 < slabRecords (axisDirection e) a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) hp] with a ha
    exact slabRecords_pos _ _ ha
  have hh := renewalCut_two_mass (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) hL s (N-s)
  rw [Nat.add_sub_of_le hsN] at hh
  change (annealed μ 0 (nonBacktracking (axisDirection e)))^2 ≤
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) s ∩ renewalCut (slabRecords (axisDirection e)) N)
  rw [hh,show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) s) = axisReachProb μ e s from axis_tapeCut_mass μ hell e hp s,
    show Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
      (renewalCut (slabRecords (axisDirection e)) (N-s)) = axisReachProb μ e (N-s) from axis_tapeCut_mass μ hell e hp (N-s),pow_two]
  exact mul_le_mul' (axisReachProb_lower μ hell e s) (axisReachProb_lower μ hell e (N-s))

lemma reversed_cut_bridge_law {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    letI := slabLaw_probability μ (axisDirection e) hp
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).restrict
      (tapeCut (axisDirection e) N)).map
      (fun Z => concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))) =
        rawBridgeMeasure μ (axisDirection e) N := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hL : ∀ᵐ a ∂slabLaw μ (axisDirection e), 0 < slabRecords (axisDirection e) a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero e) hp] with a ha
    exact slabRecords_pos _ _ ha
  change (((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).restrict
    (tapeCut (axisDirection e) N)).map
    (concatenateList ∘ (reverseTapeList ∘ cutList (slabRecords (axisDirection e)) N))) = _
  rw [← Measure.map_map (measurable_of_countable concatenateList)
    ((measurable_of_countable reverseTapeList).comp (measurable_cutList _ N)),
    ← Measure.map_map (measurable_of_countable reverseTapeList) (measurable_cutList _ N)]
  change ((bridgeListMeasure (slabLaw μ (axisDirection e)) (slabRecords (axisDirection e)) N).map
    reverseTapeList).map concatenateList = _
  rw [bridgeListMeasure_reverse _ _ hL,
    bridgeListMeasure_concatenate μ hell _ (axisDirection_ne_zero e) hp]

lemma mixed_bridge_late_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e)))
    (k r N m : ℕ) (hkr : k ≤ r) (hrN : r ≤ N)
    (z : Fin ι → Site d) (hz : ∀ q, axisHeight e (z q) = (N : ℤ)-1)
    (hzi : Function.Injective z)
    (hΔ : axisReachProb μ e (r-k)-axisReachProb μ e (N-k) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    letI := slabLaw_probability μ (axisDirection e) hp
    ((Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))).prod
      (conditioned μ (axisDirection (oppositeStep e))))
        {p | p.1 ∈ tapeCut (axisDirection e) N ∧
          (concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N p.1)),p.2) ∈
            finiteLateEndpointEvent e k r N z} ≤
      (annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹ *
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let := slabLaw_probability μ (axisDirection e) hp
  let A := Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e))
  let B := conditioned μ (axisDirection (oppositeStep e))
  have : IsFiniteMeasure B := by dsimp [B,conditioned];infer_instance
  let C := tapeCut (axisDirection e) N
  let F := fun Z => concatenateList (reverseTapeList (cutList (slabRecords (axisDirection e)) N Z))
  have hF : Measurable F := (measurable_of_countable concatenateList).comp
    ((measurable_of_countable reverseTapeList).comp (measurable_cutList _ N))
  let E := finiteLateEndpointEvent e k r N z
  have hE : MeasurableSet E := measurableSet_finiteLateEndpointEvent e k r N z
  have hCu : A C ≤ 1 := prob_le_one
  have hCu0 : A C ≠ 0 := by
    rw [show A C = axisReachProb μ e N from axis_tapeCut_mass μ hell e hp N]
    exact ne_of_gt (hp.trans_le (axisReachProb_lower μ hell e N))
  have hcond : (ProbabilityTheory.cond A C).map F =
      (axisReachProb μ e N)⁻¹ • rawBridgeMeasure μ (axisDirection e) N := by
    rw [ProbabilityTheory.cond,Measure.map_smul _ hF.aemeasurable]
    rw [show A C = axisReachProb μ e N from axis_tapeCut_mass μ hell e hp N]
    congr 1
    exact reversed_cut_bridge_law μ hell e hp N
  have hmap : ((ProbabilityTheory.cond A C).prod B).map (fun p => (F p.1,p.2)) =
      (((ProbabilityTheory.cond A C).map F).prod B) := by
    simpa only [Measure.map_id',Prod.map_def,Function.id_def] using
      (Measure.map_prod_map (ProbabilityTheory.cond A C) B hF measurable_id).symm
  have hh := finite_bridge_late_bound μ hell e k r N m hkr hrN z hz hzi hΔ
  rw [← hcond,← hmap] at hh
  rw [Measure.map_apply (show Measurable (fun p : (ℕ → Word d) × Path d => (F p.1,p.2)) from
    (hF.comp measurable_fst).prodMk measurable_snd) hE] at hh
  have hsub : A.restrict C ≤ ProbabilityTheory.cond A C := by
    rw [ProbabilityTheory.cond]
    intro S
    rw [Measure.smul_apply,smul_eq_mul]
    exact le_mul_of_one_le_left' (ENNReal.one_le_inv.mpr hCu)
  have hle := Measure.prod_mono hsub (le_refl B)
  have heq : (A.prod B) {p | p.1 ∈ C ∧ (F p.1,p.2) ∈ E} =
      ((A.restrict C).prod B) ((fun p => (F p.1,p.2)) ⁻¹' E) := by
    rw [Measure.restrict_prod_eq_prod_univ C,
      Measure.restrict_apply (hE.preimage (show Measurable (fun p : (ℕ → Word d) × Path d => (F p.1,p.2)) from (hF.comp measurable_fst).prodMk measurable_snd))]
    congr 1
    ext p
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true]
    exact and_comm
  change (A.prod B) {p | p.1 ∈ C ∧ (F p.1,p.2) ∈ E} ≤ _
  rw [heq]
  refine ((hle _).trans hh).trans ?_
  gcongr
  exact axisReachProb_lower μ hell e N

end DirectionalZeroOne

end OAI
