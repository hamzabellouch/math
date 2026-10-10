import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Bounds

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FiniteAssociation
attribute [local instance] Classical.propDecidable
variable [Fintype E]

private theorem bernoulli_atom_product (p : unitInterval) (ω : Set E) :
    (law p).real {ω} = ∏ e : E, if e ∈ ω then (p : ℝ) else 1 - p := by
  rw [law, setBernoulli_real_singleton p (Set.subset_univ ω) (Set.finite_univ)]
  simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.sdiff_eq]
  exact Or.inl rfl

private theorem bernoulli_atom_modular (p : unitInterval) (a b : Set E) :
    (law p).real {a} * (law p).real {b} =
      (law p).real {a ∩ b} * (law p).real {a ∪ b} := by
  simp only [bernoulli_atom_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

 

theorem association_finite (p : unitInterval) (f g : Set E → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂law p) * (∫ ω, g ω ∂law p) ≤ ∫ ω, f ω * g ω ∂law p := by
  have h := fkg f g (fun ω : Set E => (law p).real {ω})
    (fun _ => measureReal_nonneg) hf0 hg0 hf hg
    (fun a b => (bernoulli_atom_modular p a b).le)
  have hsum : (∑ ω : Set E, (law p).real {ω}) = 1 := by
    simp
  rw [hsum, one_mul] at h
  simpa only [integral_fintype Integrable.of_finite, smul_eq_mul] using h

 
theorem association_events_finite (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  have hm (S : Set (Set E)) (hS : IsUpperSet S) :
      Monotone (S.indicator (fun _ => (1 : ℝ))) := by
    intro a b hab
    by_cases ha : a ∈ S
    · simp [ha, hS hab ha]
    · simp only [Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      B.indicator (fun _ => (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ => 1) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  have h := association_finite p _ _ (hm A hA) (hm B hB)
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
  rw [he] at h
  simpa only [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet B),
    integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet (A ∩ B)),
    smul_eq_mul, mul_one] using h

end FiniteAssociation

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology

 
def FiniteWitness (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Finset E, (s : Set E) ⊆ ω ∧ (s : Set E) ∈ A

theorem association_restricted (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A ∩ B} := by
  let A' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ A}
  let B' : Set (Set (s : Set E)) := {η | Subtype.val '' η ∈ B}
  have hA' : IsUpperSet A' := fun _ _ h ha => hA (Set.image_mono h) ha
  have hB' : IsUpperSet B' := fun _ _ h hb => hB (Set.image_mono h) hb
  have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) =
      ω ∩ (s : Set E) := by
    ext e
    simp [and_comm]
  have hl (C : Set (Set E)) :
      (law p : Measure (Set (s : Set E))).real {η | Subtype.val '' η ∈ C} =
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} := by
    rw [← law_map_restrict p (s : Set E), measureReal_def,
      Measure.map_apply (measurable_set_restrict _) .of_discrete]
    simp only [Set.preimage_ofPred_eq, he, measureReal_def]
  have ht := association_events_finite p A' B' hA' hB'
  change (law p).real {η | Subtype.val '' η ∈ A} *
    (law p).real {η | Subtype.val '' η ∈ B} ≤
    (law p).real {η | Subtype.val '' η ∈ A ∩ B} at ht
  simpa only [hl] using ht

 noncomputable def edgeExhaustion [Encodable E] (n : ℕ) : Finset E :=
  (Finset.range n).preimage Encodable.encode Encodable.encode_injective.injOn

 theorem edgeExhaustion_mono [Encodable E] :
    Monotone (edgeExhaustion : ℕ → Finset E) := by
  intro m n h e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range] at he ⊢
  exact he.trans_le h

private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn

 

theorem association_finiteWitness [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real A * (law p).real B ≤ (law p).real (A ∩ B) := by
  let := Encodable.ofCountable E
  have hfAB : FiniteWitness (A ∩ B) := by
    intro ω hω
    obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
    obtain ⟨t, ht, htb⟩ := hfB ω hω.2
    refine ⟨s ∪ t, ?_, hA ?_ hsa, hB ?_ htb⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs ht
    · simp only [Finset.coe_union]; exact Set.subset_union_left
    · simp only [Finset.coe_union]; exact Set.subset_union_right
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto
    ((hlim A hA hfA).mul (hlim B hB hfB)) (hlim (A ∩ B) (hA.inter hB) hfAB)
    (Filter.Eventually.of_forall fun n => association_restricted p A B hA hB (edgeExhaustion n))

end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

theorem finiteWitness_conn_finset (G : BondGraph V E) (x : V) (t : Finset V) :
    FiniteWitness {ω | ∀ y ∈ t, Conn G ω x y} := by
  intro ω h
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨s, hs, hsa⟩ := finiteWitness_conn G x a ω (h a (by simp))
    obtain ⟨r, hr, hrt⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨s ∪ r, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hs hr
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact conn_mono G (by simp) hsa
      · exact conn_mono G (by simp) (hrt y hy)

 
def clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ t : Finset V, n ≤ t.card ∧ ∀ y ∈ t, Conn G ω x y}

theorem clusterLarge_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (clusterLarge G x n) := by
  rintro ω η h ⟨t, ht, hc⟩
  exact ⟨t, ht, fun y hy => conn_mono G h (hc y hy)⟩

theorem finiteWitness_clusterLarge (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (clusterLarge G x n) := by
  rintro ω ⟨t, ht, hc⟩
  obtain ⟨s, hs, hsc⟩ := finiteWitness_conn_finset G x t ω hc
  exact ⟨s, hs, t, ht, hsc⟩

theorem measurableSet_clusterLarge [Countable E] (G : BondGraph V E) (x : V) (n : ℕ) :
    MeasurableSet (clusterLarge G x n) :=
  measurableSet_finiteWitness _ (clusterLarge_upper G x n) (finiteWitness_clusterLarge G x n)

theorem clusterLarge_antitone (G : BondGraph V E) (x : V) :
    Antitone (clusterLarge G x) := by
  rintro m n h ω ⟨t, ht, hc⟩
  exact ⟨t, h.trans ht, hc⟩

theorem infinite_cluster_eq_iInter (G : BondGraph V E) (x : V) :
    {ω | (cluster G ω x).Infinite} = ⋂ n, clusterLarge G x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    exact ⟨t, hcard.ge, ht⟩
  · intro h hfin
    obtain ⟨t, ht, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr (hc y hy)
    have := Finset.card_le_card hsub
    omega

theorem measurableSet_infinite_cluster [Countable E] (G : BondGraph V E) (x : V) :
    MeasurableSet {ω | (cluster G ω x).Infinite} := by
  rw [infinite_cluster_eq_iInter]
  exact MeasurableSet.iInter (measurableSet_clusterLarge G x)

 
theorem association_decreasing [Countable E] (p : unitInterval)
    (A B : ℕ → Set (Set E)) (hA : Antitone A) (hB : Antitone B)
    (huA : ∀ n, IsUpperSet (A n)) (huB : ∀ n, IsUpperSet (B n))
    (hfA : ∀ n, FiniteWitness (A n)) (hfB : ∀ n, FiniteWitness (B n)) :
    (law p).real (⋂ n, A n) * (law p).real (⋂ n, B n) ≤
      (law p).real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
  have hlim (C : ℕ → Set (Set E)) (hm : Antitone C) (hC : ∀ n, MeasurableSet (C n)) :
      Tendsto (fun n => (law p).real (C n)) atTop (𝓝 ((law p).real (⋂ n, C n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hC n).nullMeasurableSet) hm
        ⟨0, measure_ne_top _ _⟩)
  have hmA n := measurableSet_finiteWitness (A n) (huA n) (hfA n)
  have hmB n := measurableSet_finiteWitness (B n) (huB n) (hfB n)
  have h := le_of_tendsto_of_tendsto ((hlim A hA hmA).mul (hlim B hB hmB))
    (hlim (fun n => A n ∩ B n) (fun m n h => Set.inter_subset_inter (hA h) (hB h))
      (fun n => (hmA n).inter (hmB n)))
    (Filter.Eventually.of_forall fun n =>
      association_finiteWitness p (A n) (B n) (huA n) (huB n) (hfA n) (hfB n))
  simpa only [Set.iInter_inter_distrib] using h

 

theorem association_infinite_cluster [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (law p).real {ω | (cluster G ω x).Infinite} *
      (law p).real {ω | (cluster G ω y).Infinite} ≤
      (law p).real {ω | (cluster G ω x).Infinite ∧ (cluster G ω y).Infinite} := by
  rw [infinite_cluster_eq_iInter, infinite_cluster_eq_iInter]
  change _ ≤ (law p).real ({ω | (cluster G ω x).Infinite} ∩
    {ω | (cluster G ω y).Infinite})
  rw [infinite_cluster_eq_iInter, infinite_cluster_eq_iInter]
  exact association_decreasing p _ _ (clusterLarge_antitone G x) (clusterLarge_antitone G y)
    (clusterLarge_upper G x) (clusterLarge_upper G y)
    (finiteWitness_clusterLarge G x) (finiteWitness_clusterLarge G y)

end ClusterEvents

section Automorphisms
attribute [local instance] Classical.propDecidable

theorem measurable_set_preimage (b : E ≃ E) :
    Measurable (fun ω : Set E => b ⁻¹' ω) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply (b e)).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_preimage_equiv (p : unitInterval) (b : E ≃ E) :
    (law p : Measure (Set E)).map (fun ω => b ⁻¹' ω) = law p := by
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_set_preimage b) measurable_setOfPred]
  have he : (fun ω : Set E => b ⁻¹' ω) ∘ (fun f : E → Prop => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘
        MeasurableEquiv.piCongrLeft (fun _ : E => Prop) b.symm := by
    funext f
    ext e
    simp only [Function.comp_apply, Set.mem_preimage, Set.mem_ofPred_eq]
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : E => Prop) b.symm f (b e)
    exact iff_of_eq (by simpa only [Equiv.symm_apply_apply] using hh.symm)
  rw [he, ← Measure.map_map measurable_setOfPred (MeasurableEquiv.measurable _)]
  simp only [Set.mem_univ]
  congr 1
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : E => unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False) b.symm

theorem isAut_symm (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) : IsAut G a.symm b.symm := by
  intro e
  have hh := congrArg (Sym2.map a.symm) (h (b.symm e))
  simpa only [Equiv.apply_symm_apply, Sym2.map_map, Equiv.symm_comp_self,
    Sym2.map_id', id_eq] using hh.symm

theorem conn_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) {ω : Set E} {x y : V} (hc : Conn G ω x y) :
    Conn G (b '' ω) (a x) (a y) := by
  induction hc with
  | refl => exact conn_refl G _ _
  | @tail v w hvw hed ih =>
    obtain ⟨e, he, hGe⟩ := hed
    exact ih.tail ⟨b e, Set.mem_image_of_mem _ he, by rw [h e, hGe, Sym2.map_mk]⟩

theorem conn_aut_iff (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x y : V) :
    Conn G (b ⁻¹' ω) x y ↔ Conn G ω (a x) (a y) := by
  constructor
  · intro hc
    simpa only [Set.image_preimage_eq _ b.surjective] using conn_aut G h hc
  · intro hc
    have he : b.symm '' ω = b ⁻¹' ω := by
      ext e
      simp
    simpa only [Equiv.symm_apply_apply, he] using
      conn_aut G (isAut_symm G h) hc

theorem cluster_aut (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (h : IsAut G a b) (ω : Set E) (x : V) :
    a '' cluster G (b ⁻¹' ω) x = cluster G ω (a x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (conn_aut_iff G h ω x z).mp hz
  · intro hy
    change Conn G ω (a x) y at hy
    refine ⟨a.symm y, ?_, by simp⟩
    exact (conn_aut_iff G h ω x (a.symm y)).mpr (by simpa only [Equiv.apply_symm_apply] using hy)

theorem infinite_cluster_aut [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x : V) :
    (law p).real {ω | (cluster G ω (a x)).Infinite} =
      (law p).real {ω | (cluster G ω x).Infinite} := by
  have he : {ω | (cluster G ω (a x)).Infinite} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | (cluster G ω x).Infinite} := by
    ext ω
    change (cluster G ω (a x)).Infinite ↔ (cluster G (b ⁻¹' ω) x).Infinite
    rw [← cluster_aut G h]
    exact Set.infinite_image_iff (fun _ _ _ _ hab => a.injective hab)
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_infinite_cluster G x), law_map_preimage_equiv]

 
theorem finite_open_probability (p : unitInterval) (s : Finset E) :
    (law p).real {ω | (s : Set E) ⊆ ω} = (p : ℝ) ^ s.card := by
  have he : {ω : Set E | (s : Set E) ⊆ ω} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹' {Set.univ} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => Set.eq_univ_of_forall fun e => h e.property,
      fun h e he => show (⟨e, he⟩ : (s : Set E)) ∈ (Subtype.val ⁻¹' ω) from
        h.symm ▸ Set.mem_univ _⟩
  unfold Measure.real
  rw [he, ← Measure.map_apply (measurable_set_restrict _) (by measurability),
    law_map_restrict]
  change (law p : Measure (Set (s : Set E))).real {Set.univ} = _
  simp [law, setBernoulli_real_singleton p (Set.Subset.refl _) (Set.toFinite _)]

theorem twoPoint_pos [Countable E] (G : BondGraph V E) (hG : Connected G)
    (p : unitInterval) (hp : 0 < p) (x y : V) : 0 < twoPoint G p x y := by
  obtain ⟨s, _, hs⟩ := finiteWitness_conn G x y Set.univ (conn_univ_of_connected G hG x y)
  have hpos : 0 < (law p).real {ω | (s : Set E) ⊆ ω} := by
    rw [finite_open_probability]
    exact pow_pos hp _
  apply lt_of_lt_of_le hpos
  exact measureReal_mono (fun _ hω => conn_mono G hω hs)

end Automorphisms

section UniquenessThreshold
attribute [local instance] Classical.propDecidable
variable [Countable V] [Countable E]

omit [Countable V] in
 
theorem association_infinite_conn (G : BondGraph V E) (p : unitInterval) (x y z : V) :
    (law p).real {ω | (cluster G ω x).Infinite} * twoPoint G p y z ≤
      (law p).real {ω | (cluster G ω x).Infinite ∧ Conn G ω y z} := by
  have h := association_decreasing p (clusterLarge G x) (fun _ => {ω | Conn G ω y z})
    (clusterLarge_antitone G x) antitone_const (clusterLarge_upper G x)
    (fun _ _ _ hsub hconn => conn_mono G hsub hconn) (finiteWitness_clusterLarge G x)
    (fun _ => finiteWitness_conn G y z)
  simpa only [← infinite_cluster_eq_iInter, Set.iInter_const, twoPoint, Measure.real, Set.inter_def, Set.mem_ofPred_eq] using h

omit [Countable V] in
theorem survival_pos_of_survival_pos (G : BondGraph V E) (hG : Connected G)
    (p : unitInterval) (hp : 0 < p) {x : V}
    (hx : 0 < (law p).real {ω | (cluster G ω x).Infinite}) (y : V) :
    0 < (law p).real {ω | (cluster G ω y).Infinite} := by
  apply lt_of_lt_of_le (mul_pos hx (twoPoint_pos G hG p hp x y))
  refine (association_infinite_conn G p x x y).trans (measureReal_mono ?_)
  rintro ω ⟨hi, hc⟩
  change (cluster G ω y).Infinite
  rwa [← cluster_eq_of_conn G ω hc]

omit [Countable V] [Countable E] in
theorem exists_infinite_cluster_iff (G : BondGraph V E) (ω : Set E) :
    (infiniteClusters G ω).Nonempty ↔ ∃ x, (cluster G ω x).Infinite := by
  constructor
  · rintro ⟨C, hi, x, rfl⟩
    exact ⟨x, hi⟩
  · rintro ⟨x, hx⟩
    exact ⟨cluster G ω x, hx, x, rfl⟩

omit [Countable V] [Countable E] in
theorem unique_infinite_cluster_iff (G : BondGraph V E) (ω : Set E) :
    (∃! C, C ∈ infiniteClusters G ω) ↔
      ∃ x, (cluster G ω x).Infinite ∧ ∀ y, (cluster G ω y).Infinite → Conn G ω x y := by
  constructor
  · rintro ⟨C, ⟨hi, x, rfl⟩, hu⟩
    refine ⟨x, hi, fun y hy => ?_⟩
    have he := hu (cluster G ω y) ⟨hy, y, rfl⟩
    have hm := mem_cluster_self G ω y
    rwa [he] at hm
  · rintro ⟨x, hx, hu⟩
    refine ⟨cluster G ω x, ⟨hx, x, rfl⟩, ?_⟩
    rintro C ⟨hi, y, rfl⟩
    exact (cluster_eq_of_conn G ω (hu y hi)).symm

theorem measurableSet_unique_infinite_cluster (G : BondGraph V E) :
    MeasurableSet {ω | ∃! C, C ∈ infiniteClusters G ω} := by
  have he : {ω | ∃! C, C ∈ infiniteClusters G ω} =
      ⋃ x, ({ω | (cluster G ω x).Infinite} ∩
        ⋂ y, ({ω | (cluster G ω y).Infinite}ᶜ ∪ {ω | Conn G ω x y})) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, unique_infinite_cluster_iff,
      imp_iff_not_or]
  rw [he]
  exact MeasurableSet.iUnion fun x => (measurableSet_infinite_cluster G x).inter
    (MeasurableSet.iInter fun y =>
      (measurableSet_infinite_cluster G y).compl.union (measurableSet_conn G x y))

theorem uniform_survival_pos (G : BondGraph V E) (hconn : Connected G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : 0 < p)
    (hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty}) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ x, θ ≤ (law p).real {ω | (cluster G ω x).Infinite} := by
  have hunion : {ω | (infiniteClusters G ω).Nonempty} =
      ⋃ x, {ω | (cluster G ω x).Infinite} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_infinite_cluster_iff]
  rw [hunion] at hpos
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hpos)
  have hxp : 0 < (law p).real {ω | (cluster G ω x).Infinite} :=
    ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)
  have hroot := survival_pos_of_survival_pos G hconn p hp hxp
  obtain ⟨s, hs⟩ := hqt
  have hsn : s.Nonempty := by obtain ⟨o, ho, _⟩ := hs x; exact ⟨o, ho⟩
  let vals := s.image (fun o => (law p).real {ω | (cluster G ω o).Infinite})
  have hv : vals.Nonempty := hsn.image _
  refine ⟨vals.min' hv, ?_, fun y => ?_⟩
  · obtain ⟨o, _, he⟩ := Finset.mem_image.mp (Finset.min'_mem vals hv)
    rw [← he]
    exact hroot o
  · obtain ⟨o, ho, a, b, ha, hay⟩ := hs y
    rw [← hay, infinite_cluster_aut G p ha]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨o, ho, rfl⟩)

 

theorem not_operatorBounded_of_unique [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hqt : QuasiTransitive G) (p : unitInterval)
    (hu : law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1) : ¬ OperatorBounded G p := by
  have hp : 0 < p := by
    by_contra h
    have hp0 : p = 0 := le_antisymm (not_lt.mp h) (bot_le)
    subst p
    simp [law] at hu
  have hpos : 0 < law p {ω | (infiniteClusters G ω).Nonempty} := by
    exact lt_of_lt_of_le (show 0 < law p {ω | ∃! C, C ∈ infiniteClusters G ω} by rw [hu]; exact zero_lt_one)
      (measure_mono fun ω hω => ⟨hω.choose, hω.choose_spec.1⟩)
  obtain ⟨θ, hθ, hroot⟩ := uniform_survival_pos G hconn hqt p hp hpos
  have hue : ∀ᵐ ω ∂law p, ∃! C, C ∈ infiniteClusters G ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_unique_infinite_cluster G)).mpr hu
  refine not_operatorBounded_of_positive_column G p (Classical.arbitrary V) (mul_pos hθ hθ)
    (fun x => ?_)
  refine (mul_le_mul (hroot x) (hroot (Classical.arbitrary V)) hθ.le measureReal_nonneg).trans
    ((association_infinite_cluster G p x (Classical.arbitrary V)).trans ?_)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hue] with ω hω
  intro hi
  obtain ⟨r, _, hconnr⟩ := (unique_infinite_cluster_iff G ω).mp hω
  exact conn_trans G ω (conn_symm G ω (hconnr x hi.1)) (hconnr _ hi.2)

 

theorem ptwo_le_pu [Infinite V] (G : BondGraph V E)
    (hconn : Connected G) (hqt : QuasiTransitive G) : ptwo G ≤ pu G := by
  unfold pu ptwo
  apply le_sInf
  intro p hp
  apply sSup_le
  intro q hq
  by_contra hqp
  have hb := operatorBounded_of_le G (le_of_lt (not_le.mp hqp)) hq
  exact not_operatorBounded_of_unique G hconn hqt p hp hb

end UniquenessThreshold

section DisjointWitness
attribute [local instance] Classical.propDecidable

 
def DisjointOccurrence (A B : Set (Set E)) : Set (Set E) :=
  {ω | ∃ s t : Finset E, (s : Set E) ⊆ ω ∧ (t : Set E) ⊆ ω ∧
    Disjoint s t ∧ (s : Set E) ∈ A ∧ (t : Set E) ∈ B}

theorem disjointOccurrence_upper (A B : Set (Set E)) : IsUpperSet (DisjointOccurrence A B) := by
  rintro ω η h ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs.trans h, ht.trans h, hd, ha, hb⟩

theorem finiteWitness_disjointOccurrence (A B : Set (Set E)) :
    FiniteWitness (DisjointOccurrence A B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  refine ⟨s ∪ t, ?_, s, t, ?_, ?_, hd, ha, hb⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · simp
  · simp

theorem disjointOccurrence_mono {A A' B B' : Set (Set E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩

 
def openSection (A : Set (Set E)) (e : E) : Set (Set E) := {ω | insert e ω ∈ A}

theorem openSection_upper {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    IsUpperSet (openSection A e) :=
  fun _ _ h hω => hA (Set.insert_subset_insert h) hω

theorem subset_openSection {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A ⊆ openSection A e := fun ω hω => hA (Set.subset_insert e ω) hω

 
theorem openSection_disjointOccurrence (A B : Set (Set E)) (_hA : IsUpperSet A)
    (hB : IsUpperSet B) (e : E) :
    openSection (DisjointOccurrence A B) e ⊆
      DisjointOccurrence (openSection A e) B ∪ DisjointOccurrence A (openSection B e) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  by_cases he : e ∈ s
  · left
    have het : e ∉ t := fun h => Finset.disjoint_left.mp hd he h
    refine ⟨s.erase e, t, ?_, ?_, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd, ?_, hb⟩
    · intro z hz
      exact (hs (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · intro z hz
      rcases ht hz with rfl | hz'
      · exact (het hz).elim
      · exact hz'
    · change insert e (↑(s.erase e) : Set E) ∈ A
      simpa only [← Finset.coe_insert, Finset.insert_erase he] using ha
  · right
    refine ⟨s, t.erase e, ?_, ?_, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd, ha, ?_⟩
    · intro z hz
      rcases hs hz with rfl | hz'
      · exact (he hz).elim
      · exact hz'
    · intro z hz
      exact (ht (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · apply hB ?_ hb
      intro z hz
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr (Finset.mem_erase.mpr ⟨hze, hz⟩)

 

noncomputable def finiteProbability (p : unitInterval) (s : Finset E) (A : Set (Set E)) : ℝ :=
  ∑ t ∈ s.powerset, if (t : Set E) ∈ A then
    (p : ℝ) ^ t.card * (1 - p : ℝ) ^ (s.card - t.card) else 0

theorem finiteProbability_nonneg (p : unitInterval) (s : Finset E) (A : Set (Set E)) :
    0 ≤ finiteProbability p s A := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_mono (p : unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbability p s A ≤ finiteProbability p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_union_add_inter (p : unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbability p s (A ∪ B) + finiteProbability p s (A ∩ B) =
      finiteProbability p s A + finiteProbability p s B := by
  simp only [finiteProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

@[simp] theorem finiteProbability_empty (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p ∅ A = if ∅ ∈ A then 1 else 0 := by
  simp [finiteProbability]

theorem finiteProbability_insert (p : unitInterval) (s : Finset E) (e : E) (he : e ∉ s)
    (A : Set (Set E)) :
    finiteProbability p (insert e s) A =
      (1 - p : ℝ) * finiteProbability p s A + (p : ℝ) * finiteProbability p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [finiteProbability, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
    rw [hexp, pow_succ]
    split_ifs <;> simp_all [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ,
      Finset.coe_insert, openSection, Set.mem_ofPred_eq]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable

@[simp] theorem empty_mem_disjointOccurrence (A B : Set (Set E)) :
    (∅ : Set E) ∈ DisjointOccurrence A B ↔ ∅ ∈ A ∧ ∅ ∈ B := by
  constructor
  · rintro ⟨s, t, hs, ht, _, ha, hb⟩
    have hse : (s : Set E) = ∅ := Set.subset_empty_iff.mp hs
    have hte : (t : Set E) = ∅ := Set.subset_empty_iff.mp ht
    exact ⟨hse ▸ ha, hte ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨∅, ∅, by simp, by simp, by simp, by simpa using ha, by simpa using hb⟩

 

theorem finiteProbability_disjointOccurrence_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbability p s (DisjointOccurrence A B) ≤
      finiteProbability p s A * finiteProbability p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbability_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s D10 + finiteProbability p s D01 - finiteProbability p s D00 := by
      have h1 := finiteProbability_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbability_mono p s hD
      have h3 := finiteProbability_union_add_inter p s D10 D01
      change finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbability_mono p s (subset_openSection hA e)
    have hb := finiteProbability_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p : ℝ) := by linarith
    have hdif : 0 ≤ ((p : ℝ) ^ 2) *
        (finiteProbability p s A1 - finiteProbability p s A) *
        (finiteProbability p s B1 - finiteProbability p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbability_insert p s e he, finiteProbability_insert p s e he,
      finiteProbability_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec p.2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 p.2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 p.2.1
    change (1 - (p : ℝ)) * finiteProbability p s D00 +
      (p : ℝ) * finiteProbability p s (openSection D00 e) ≤
      ((1 - (p : ℝ)) * finiteProbability p s A + (p : ℝ) * finiteProbability p s A1) *
      ((1 - (p : ℝ)) * finiteProbability p s B + (p : ℝ) * finiteProbability p s B1)
    nlinarith

end FiniteBK

section BKMeasure
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem finiteProbability_univ [Fintype E] (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p Finset.univ A = (law p).real A := by
  have he : (law p).real A = ∑ ω : Set E, if ω ∈ A then (law p).real {ω} else 0 := by
    have h := integral_fintype (μ := law p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbability]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t _
    rw [law, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem disjointOccurrence_image {F : Type*} (f : F ↪ E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B =
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    let s' := s.preimage f f.injective.injOn
    let t' := t.preimage f f.injective.injOn
    have hs' : (s' : Set F) = f ⁻¹' (s : Set E) := by simp [s']
    have ht' : (t' : Set F) = f ⁻¹' (t : Set E) := by simp [t']
    have hsI : f '' (s' : Set F) = (s : Set E) := by
      rw [hs', Set.image_preimage_eq_of_subset]
      exact hs.trans (Set.image_subset_range _ _)
    have htI : f '' (t' : Set F) = (t : Set E) := by
      rw [ht', Set.image_preimage_eq_of_subset]
      exact ht.trans (Set.image_subset_range _ _)
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs']
      exact (Set.preimage_mono hs).trans (by rw [Set.preimage_image_eq _ f.injective])
    · rw [ht']
      exact (Set.preimage_mono ht).trans (by rw [Set.preimage_image_eq _ f.injective])
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp hd (by simpa [s'] using hx) (by simpa [t'] using hy)
    · change f '' (s' : Set F) ∈ A
      rwa [hsI]
    · change f '' (t' : Set F) ∈ B
      rwa [htI]
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨s.map f, t.map f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_map] using Set.image_mono hs
    · simpa only [Finset.coe_map] using Set.image_mono ht
    · exact (Finset.disjoint_map f).mpr hd
    · simpa only [Finset.coe_map, Set.mem_preimage] using ha
    · simpa only [Finset.coe_map, Set.mem_preimage] using hb

theorem bk_finite_half [Fintype E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  simpa only [finiteProbability_univ] using
    finiteProbability_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_restricted_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (law p).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← law_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_finite_half p hp ((fun ω => f '' ω) ⁻¹' A)
    ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

 
theorem bk_finiteWitness_half [Countable E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_restricted_half p hp A B hA hB (edgeExhaustion n)

end BKMeasure

section ORLift
attribute [local instance] Classical.propDecidable

noncomputable def orParameter (q : unitInterval) (m : ℕ) : unitInterval :=
  ⟨1 - (1 - (q : ℝ)) ^ m,
    sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr q.2.2) (by linarith [q.2.1])),
    by linarith [pow_nonneg (sub_nonneg.mpr q.2.2) m]⟩

noncomputable abbrev bitLaw (q : unitInterval) : Measure Prop :=
  unitInterval.toNNReal q • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm q) • Measure.dirac False

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  infer_instance

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := inferInstance
  have hfalse : μ.real {False} = (1 - (q : ℝ)) ^ Fintype.card F := by
    change ((law q).map Set.Nonempty).real {False} = _
    simp only [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : Set.Nonempty ⁻¹' ({False} : Set Prop) = ({∅} : Set (Set F)) := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty]
    rw [he]
    change (law q).real {∅} = _
    rw [law, setBernoulli_real_singleton q (Set.empty_subset _) Set.finite_univ]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  have htrue : μ.real {True} = 1 - (1 - (q : ℝ)) ^ Fintype.card F := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hfalse]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (orParameter q (Fintype.card F))).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [htrue]
    simp [bitLaw, Measure.real, orParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hfalse]
    simp [bitLaw, Measure.real, orParameter]

 
theorem finite_image_lift {F : Type*} (f : F → E) {ω : Set F} (s : Finset E)
    (hs : (s : Set E) ⊆ f '' ω) :
    ∃ t : Finset F, (t : Set F) ⊆ ω ∧ f '' (t : Set F) = (s : Set E) := by
  have hex : ∃ t ⊆ f '' ω, t.Finite ∧ t = (s : Set E) :=
    ⟨s, hs, s.finite_toSet, rfl⟩
  obtain ⟨t, ht, htf, hti⟩ := Set.exists_subset_image_finite_and.mp hex
  exact ⟨htf.toFinset, by simpa using ht, by simpa using hti⟩

theorem finiteWitness_image_preimage {F : Type*} (f : F → E) (A : Set (Set E))
    (hA : FiniteWitness A) : FiniteWitness ((fun ω => f '' ω) ⁻¹' A) := by
  intro ω hω
  obtain ⟨s, hs, ha⟩ := hA (f '' ω) hω
  obtain ⟨t, ht, htI⟩ := finite_image_lift f s hs
  exact ⟨t, ht, by simpa only [Set.mem_preimage, htI] using ha⟩

theorem image_preimage_disjointOccurrence {F : Type*} (f : F → E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  obtain ⟨s', hs', hsI⟩ := finite_image_lift f s hs
  obtain ⟨t', ht', htI⟩ := finite_image_lift f t ht
  refine ⟨s', t', hs', ht', ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxs : f x ∈ (s : Set E) := hsI ▸ Set.mem_image_of_mem f hx
    have hxt : f x ∈ (t : Set E) := htI ▸ Set.mem_image_of_mem f hy
    exact Finset.disjoint_left.mp hd hxs hxt
  · simpa only [Set.mem_preimage, hsI] using ha
  · simpa only [Set.mem_preimage, htI] using hb

end ORLift

section ORLaw
attribute [local instance] Classical.propDecidable

theorem map_exists_bitLaw (q : unitInterval) (F : Type*) [Fintype F] :
    (Measure.infinitePi (fun _ : F => bitLaw q)).map (fun f : F → Prop => ∃ j, f j) =
      bitLaw (orParameter q (Fintype.card F)) := by
  have h := map_nonempty q F
  unfold law at h
  rw [setBernoulli_eq_map, Measure.map_map (Measurable.of_discrete) measurable_setOfPred] at h
  simpa only [Set.mem_univ, Function.comp_def, Set.Nonempty, Set.mem_ofPred_eq,
    bernoulliMeasure_def, bitLaw] using h

theorem measurable_image_fst (F : Type*) [Fintype F] :
    Measurable (fun ω : Set (E × F) => Prod.fst '' ω) := by
  have hm : Measurable (fun ω : Set (E × F) => fun e => ∃ j : F, (e,j) ∈ ω) := by
    apply Measurable.of_eval
    intro e
    apply measurableSet_setOfPred.mp
    have he : {ω : Set (E × F) | ∃ j : F, (e,j) ∈ ω} =
        ⋃ j : F, {ω : Set (E × F) | (e,j) ∈ ω} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (e,j)).comp MeasurableEquiv.setOfPred.symm.measurable)
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) =
      (fun f : E → Prop => {e | f e}) ∘ (fun ω e => ∃ j : F, (e,j) ∈ ω) := by
    funext ω
    ext e
    simp [Prod.exists]
  rw [he]
  exact measurable_setOfPred.comp hm

 
theorem law_map_image_fst (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set (E × F))).map (fun ω => Prod.fst '' ω) =
      law (orParameter q (Fintype.card F)) := by
  let c := MeasurableEquiv.curry E F Prop
  let b := fun f : E → F → Prop => fun e => ∃ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : F → Prop => ∃j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_image_fst F) measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) ∘ (fun f => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := by
    funext f
    ext e
    simp [b, c, Function.comp_def, Prod.exists]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ← Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × F => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : F) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  rw [map_exists_bitLaw q F]
  rw [setBernoulli_eq_map]
  rfl

 
theorem exists_orParameter (p : unitInterval) (hp : p < 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f (1/2)) := by
    rw [h0]
    refine ⟨p.2.1, ?_⟩
    dsimp [f]
    norm_num at hm ⊢
    linarith
  obtain ⟨q, hq, hqp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    hf.continuousOn hp'
  refine ⟨m, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  apply Subtype.ext
  exact hqp

end ORLaw

section BK
attribute [local instance] Classical.propDecidable

theorem disjointOccurrence_subset_inter (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) : DisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨s,t,hs,ht,_,ha,hb⟩
  exact ⟨hA hs ha, hB ht hb⟩

 

theorem bk [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  by_cases hp : p = 1
  · subst p
    by_cases hu : Set.univ ∈ DisjointOccurrence A B
    · have ha := (disjointOccurrence_subset_inter A B hA hB hu).1
      have hb := (disjointOccurrence_subset_inter A B hA hB hu).2
      simp [law, Measure.real, hu, ha, hb]
    · simp [law, Measure.real, hu]
      positivity
  · have hp' : p < 1 := lt_of_le_of_ne p.2.2 hp
    obtain ⟨m, q, hq, hqp⟩ := exists_orParameter p hp'
    let f : E × Fin m → E := Prod.fst
    let A' := (fun ω => f '' ω) ⁻¹' A
    let B' := (fun ω => f '' ω) ⁻¹' B
    have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
        (law p).real C = (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' C) := by
      have hh := law_map_image_fst (E := E) q (Fin m)
      simp only [Fintype.card_fin, hqp] at hh
      rw [← hh]
      simp only [Measure.real, Measure.map_apply (measurable_image_fst (Fin m)) hC]
      rfl
    calc
      (law p).real (DisjointOccurrence A B) =
          (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' DisjointOccurrence A B) :=
        hreal _ (measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
          (finiteWitness_disjointOccurrence A B))
      _ ≤ (law q).real (DisjointOccurrence A' B') :=
        measureReal_mono (image_preimage_disjointOccurrence f A B)
      _ ≤ (law q).real A' * (law q).real B' := bk_finiteWitness_half q hq A' B'
        (fun _ _ h hω => hA (Set.image_mono h) hω)
        (fun _ _ h hω => hB (Set.image_mono h) hω)
        (finiteWitness_image_preimage f A hfA) (finiteWitness_image_preimage f B hfB)
      _ = (law p).real A * (law p).real B := by
        rw [hreal A (measurableSet_finiteWitness A hA hfA),
          hreal B (measurableSet_finiteWitness B hB hfB)]

end BK

end Percolation

end OAI
