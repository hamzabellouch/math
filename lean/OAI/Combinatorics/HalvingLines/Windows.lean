import OAI.Combinatorics.HalvingLines.Partition

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval Classical

abbrev Window := Σ d : ℕ, Fin (2^d)

noncomputable def carrier (J : Window) : Set I := UniformPartition.cell (2^J.1) J.2

lemma measurable_carrier (J : Window) : MeasurableSet (carrier J) :=
  UniformPartition.cell_measurable _ _

noncomputable def time (R : ℕ) [NeZero R] (b : Fin R) : I :=
  ⟨((b : ℝ)+1/2)/(R : ℝ),by
    have hR : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
    constructor
    · positivity
    · apply (div_le_one hR).mpr
      have hb : (b : ℝ)+1 ≤ R := by exact_mod_cast b.isLt
      linarith⟩

lemma time_lt_one (R : ℕ) [NeZero R] (b : Fin R) : (time R b : ℝ)<1 := by
  apply (div_lt_one (Nat.cast_pos.mpr (NeZero.pos R))).mpr
  have hb : (b : ℝ)+1 ≤ R := by exact_mod_cast b.isLt
  linarith

lemma time_strictMono (R : ℕ) [NeZero R] : StrictMono (time R) := by
  intro b c hbc
  change ((b : ℝ)+1/2)/(R : ℝ)<((c : ℝ)+1/2)/(R : ℝ)
  have hh : (b : ℝ)<(c : ℝ) := by exact_mod_cast hbc
  exact div_lt_div_of_pos_right (by linarith only [hh])
    (Nat.cast_pos.mpr (NeZero.pos R))

noncomputable def cut {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) (x : α) : ℕ :=
  (Finset.univ.filter fun b => t b<x).card

lemma cut_le {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) (x : α) : cut t x ≤ R := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

lemma cut_mono {α : Type*} [LinearOrder α] {R : ℕ} (t : Fin R → α) : Monotone (cut t) := by
  intro x y hxy
  apply Finset.card_le_card
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hb).2).trans_le hxy⟩

lemma lt_cut_iff {α : Type*} [LinearOrder α] {R : ℕ} {t : Fin R → α}
    (ht : StrictMono t) (b : Fin R) (x : α) : b.val < cut t x ↔ t b < x := by
  constructor
  · intro h
    by_contra hbx
    have hsub : (Finset.univ.filter fun c => t c<x) ⊆ Finset.Iio b := by
      intro c hc
      apply Finset.mem_Iio.mpr
      apply ht.lt_iff_lt.mp
      exact ((Finset.mem_filter.mp hc).2).trans_le (le_of_not_gt hbx)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    exact (not_lt_of_ge hh) h
  · intro hb
    have hsub : Finset.Iic b ⊆ (Finset.univ.filter fun c => t c<x) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ht.monotone (Finset.mem_Iic.mp hc)).trans_lt hb⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    exact hh

noncomputable def start (R : ℕ) [NeZero R] (J : Window) : ℕ :=
  cut (time R) (UniformPartition.boundary (2^J.1) J.2.castSucc)
noncomputable def stop (R : ℕ) [NeZero R] (J : Window) : ℕ :=
  cut (time R) (UniformPartition.boundary (2^J.1) J.2.succ)

lemma start_le_stop (R : ℕ) [NeZero R] (J : Window) : start R J ≤ stop R J := by
  apply cut_mono
  change (J.2 : ℝ)/(2^J.1 : ℕ) ≤ ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.le_succ J.2.val
  · positivity

lemma stop_le (R : ℕ) [NeZero R] (J : Window) : stop R J ≤ R := cut_le _ _

lemma mem_carrier_iff (R : ℕ) [NeZero R] (J : Window) (b : Fin R) :
    time R b ∈ carrier J ↔ start R J ≤ b.val ∧ b.val < stop R J := by
  have hlo := lt_cut_iff (time_strictMono R) b (UniformPartition.boundary (2^J.1) J.2.castSucc)
  have hhi := lt_cut_iff (time_strictMono R) b (UniformPartition.boundary (2^J.1) J.2.succ)
  have hl : UniformPartition.boundary (2^J.1) J.2.castSucc ≤ time R b ↔ start R J ≤ b.val := by
    simpa only [not_lt,start] using (not_congr hlo).symm
  change time R b ∈ UniformPartition.cell (2^J.1) J.2 ↔ _
  rw [UniformPartition.cell]
  split_ifs with hj
  · have hu : UniformPartition.boundary (2^J.1) J.2.succ = (1 : I) := by
      apply Subtype.ext
      change ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)=1
      rw [hj,div_self (by positivity : ((2^J.1 : ℕ) : ℝ)≠0)]
    have hb : time R b < UniformPartition.boundary (2^J.1) J.2.succ := by
      rw [hu]; exact time_lt_one R b
    simp only [mem_Icc,hl,hb.le,and_true]
    exact (and_iff_left (hhi.mpr hb)).symm
  · exact and_congr hl hhi.symm

noncomputable def length (R : ℕ) [NeZero R] (J : Window) : ℕ := stop R J-start R J
lemma start_add_length (R : ℕ) [NeZero R] (J : Window) : start R J+length R J=stop R J :=
  Nat.add_sub_of_le (start_le_stop R J)

lemma length_card (R : ℕ) [NeZero R] (J : Window) :
    length R J = (Finset.univ.filter fun b : Fin R => time R b ∈ carrier J).card := by
  have he : (Finset.univ.filter fun b : Fin R => time R b ∈ carrier J) =
      (Finset.univ.filter fun b : Fin R => b.val < stop R J) \
        (Finset.univ.filter fun b : Fin R => b.val < start R J) := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,not_lt,
      mem_carrier_iff,and_comm]
  rw [he,Finset.card_sdiff_of_subset]
  · have hcard (c : ℕ) (hc : c ≤ R) : (Finset.univ.filter fun b : Fin R => b.val<c).card=c := by
      by_cases h : c=R
      · subst c
        simp only [Fin.is_lt,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
      · have hc' : c<R := lt_of_le_of_ne hc h
        convert Fin.card_Iio (⟨c,hc'⟩ : Fin R) using 1
        congr 1
        ext b
        simp [Fin.lt_def]
    rw [hcard _ (stop_le R J),hcard _ ((start_le_stop R J).trans (stop_le R J))]
    rfl
  · intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hb).2).trans_le (start_le_stop R J)⟩

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open MeasureTheory Set
open scoped NNReal ENNReal Classical

lemma weightedAtoms_apply_finset {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) {U : Set X} (hU : MeasurableSet U) :
    (weightedAtoms w x U : ℝ) = (w : ℝ) * ((Finset.univ.filter fun i => x i ∈ U).card : ℝ) := by
  classical
  have h := integral_weightedAtoms w x (U.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const 1 hU] at h
  simpa only [smul_eq_mul,mul_one,measureReal_def,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_toReal,Set.indicator_apply,Finset.sum_boole] using h

end PlanarHalving.Limits

namespace PlanarHalving.Batches
open MeasureTheory Set Limits
open scoped NNReal ENNReal Classical
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.vertexMeasure (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : FiniteMeasure X :=
  weightedAtoms (n : ℝ≥0)⁻¹ (fun v : ↥S.vertices => z v.val)

noncomputable def System.endpointMeasure (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) (E : ℝ≥0) : FiniteMeasure X :=
  weightedAtoms E⁻¹ (fun e : ↥S.edges => z e.val.1)

lemma System.vertexMeasure_apply (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X)
    {U : Set X} (hU : MeasurableSet U) :
    (S.vertexMeasure z U : ℝ) = ((S.vertices.filter fun v => z v ∈ U).card : ℝ)/(n : ℝ) := by
  classical
  rw [System.vertexMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter fun v : ↥S.vertices => z v.val ∈ U).card =
      (S.vertices.filter fun v => z v ∈ U).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
    · intro v _ w _ h; exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,by simpa using (Finset.mem_filter.mp hv).2,rfl⟩
  rw [he]
  simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]

lemma System.endpointMeasure_apply (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X)
    (E : ℝ≥0) {U : Set X} (hU : MeasurableSet U) :
    (S.endpointMeasure z E U : ℝ) = ((S.edges.filter fun e => z e.1 ∈ U).card : ℝ)/(E : ℝ) := by
  classical
  rw [System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter fun e : ↥S.edges => z e.val.1 ∈ U).card =
      (S.edges.filter fun e => z e.1 ∈ U).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      exact Finset.mem_filter.mpr ⟨e.property,(Finset.mem_filter.mp he).2⟩
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he
      exact ⟨⟨e,(Finset.mem_filter.mp he).1⟩,by simpa using (Finset.mem_filter.mp he).2,rfl⟩
  rw [he]
  simp only [NNReal.coe_inv,div_eq_inv_mul]

theorem System.atomic_cubed_bound (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Fin n → X) {E : ℝ≥0} (hE : 0 < E) {U : Set X} (hU : MeasurableSet U) :
    (S.endpointMeasure z E U : ℝ)^3 ≤
      (4608 * (a : ℝ)^2 * n^4 / (E : ℝ)^3) *
        ((S.vertices.card : ℝ)/(n : ℝ))^3 * (S.vertexMeasure z U : ℝ) +
      13824 * (S.vertices.card : ℝ)^3 / (E : ℝ)^3 := by
  classical
  let F := S.vertices.filter fun v => z v ∈ U
  have hF : F ⊆ S.vertices := Finset.filter_subset _ _
  have hc := S.localized_crossing hP F hF
  have he : S.edges.filter (fun e => e.1 ∈ F) = S.edges.filter (fun e => z e.1 ∈ U) := by
    ext e
    simp only [Finset.mem_filter,F]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(S.edge_ends h.1).1,h.2⟩⟩
  rw [he] at hc
  rw [S.endpointMeasure_apply z E hU,S.vertexMeasure_apply z hU]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hER : 0 < (E : ℝ) := hE
  have hc' := div_le_div_of_nonneg_right hc (le_of_lt (pow_pos hER 3))
  convert hc' using 1
  all_goals
    try dsimp only [F]
    try field_simp [hn,ne_of_gt hER]
    try ring
    try rfl

end PlanarHalving.Batches

namespace PlanarHalving.TimeWindows
open Set Filter
open scoped unitInterval Topology

lemma cut_time_error (R : ℕ) [NeZero R] (x : I) :
    |(cut (time R) x : ℝ)-(R : ℝ)*(x : ℝ)| ≤ 1 := by
  have hR : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have hc := cut_le (time R) x
  apply abs_le.mpr
  constructor
  · by_cases h : cut (time R) x=R
    · rw [h]
      have hx := mul_le_mul_of_nonneg_left x.property.2 hR.le
      linarith
    · have hc' : cut (time R) x<R := lt_of_le_of_ne hc h
      let b : Fin R := ⟨cut (time R) x,hc'⟩
      have hb : ¬ time R b<x := by
        rw [← lt_cut_iff (time_strictMono R)]
        exact Nat.lt_irrefl _
      have hx : (x : ℝ)≤((b : ℝ)+1/2)/(R : ℝ) := le_of_not_gt hb
      have hh := (le_div_iff₀ hR).mp hx
      change (x : ℝ)*(R : ℝ) ≤ (cut (time R) x : ℝ)+1/2 at hh
      nlinarith
  · by_cases h : cut (time R) x=0
    · rw [h,Nat.cast_zero,zero_sub]
      have hx := mul_nonneg hR.le x.property.1
      linarith
    · have hc0 : 0<cut (time R) x := Nat.pos_of_ne_zero h
      let b : Fin R := ⟨cut (time R) x-1,by omega⟩
      have hb : time R b<x := (lt_cut_iff (time_strictMono R) b x).mp (by dsimp [b]; omega)
      have hx : ((b : ℝ)+1/2)/(R : ℝ)<(x : ℝ) := hb
      have hh := (div_lt_iff₀ hR).mp hx
      have hv : (b : ℝ)+1=(cut (time R) x : ℝ) := by
        exact_mod_cast (show b.val+1=cut (time R) x by dsimp [b]; omega)
      nlinarith

lemma length_error (R : ℕ) [NeZero R] (J : Window) :
    |(length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)| ≤ 2/(R : ℝ) := by
  have hlo := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.castSucc)
  have hhi := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.succ)
  have hn : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have he : (length R J : ℝ)=(stop R J : ℝ)-(start R J : ℝ) :=
    Nat.cast_sub (start_le_stop R J)
  have hbound : |(length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ)|≤2 := by
    rw [he]
    have hid : (stop R J : ℝ)-(start R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ) =
        ((stop R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.succ : ℝ)) -
        ((start R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.castSucc : ℝ)) := by
      simp only [UniformPartition.boundary,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by simpa only [start,stop,one_add_one_eq_two] using add_le_add hhi hlo)
  have hid : (length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)=
      ((length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ))/(R : ℝ) := by field_simp
  rw [hid,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right hbound hn.le

lemma length_tendsto (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    Tendsto (fun n => (length (R n) J : ℝ)/(R n : ℝ)) atTop (𝓝 (1/(2^J.1 : ℕ) : ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using length_error (R n) J)
  have hn : Tendsto (fun n => (R n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp hn).const_mul 2

lemma eventually_length_pos (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    ∀ᶠ n in atTop, 0<length (R n) J := by
  have ht := (tendsto_order.mp (length_tendsto R hR J)).1 (0 : ℝ) (by positivity)
  filter_upwards [ht] with n hn
  have hh := (div_pos_iff.mp hn)
  rcases hh with hh|hh
  · exact_mod_cast hh.1
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg (length (R n) J)) hh.1)

end PlanarHalving.TimeWindows

namespace PlanarHalving.Directions
open MeasureTheory Set Filter
open scoped Topology

lemma measure_zero_of_null_gaps (μ : Measure ℝ) [NullSingletonClass μ]
    (S : Set ℝ) (hb : Bornology.IsBounded S)
    (hgap : ∀ s ∈ S, ∀ t ∈ S, s<t → μ (Ioo s t)=0) : μ S=0 := by
  by_cases he : S.Nonempty
  · have hsub : S ⊆ μ.supportᶜ ∪ ({sInf S,sSup S} : Set ℝ) := by
      intro t ht
      by_cases ht0 : t=sInf S
      · exact Or.inr (by simp [ht0])
      by_cases ht1 : t=sSup S
      · exact Or.inr (by simp [ht1])
      apply Or.inl
      intro hts
      have hlo : sInf S<t := lt_of_le_of_ne (csInf_le hb.bddBelow ht) (Ne.symm ht0)
      have hhi : t<sSup S := lt_of_le_of_ne (le_csSup hb.bddAbove ht) ht1
      obtain ⟨a,ha,hat⟩ := exists_lt_of_csInf_lt he hlo
      obtain ⟨b,hb,htb⟩ := exists_lt_of_lt_csSup he hhi
      have hh := (Measure.mem_support_iff_forall t).mp hts (Ioo a b) (Ioo_mem_nhds hat htb)
      rw [hgap a ha b hb (hat.trans htb)] at hh
      exact lt_irrefl _ hh
    exact measure_mono_null hsub (measure_union_null Measure.measure_compl_support (((Set.finite_singleton _).insert _).measure_zero μ))
  · rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty]

lemma interval_has_rat_interior {S : Set ℝ} (hS : Convex ℝ S) (hn : ¬ S.Subsingleton) :
    ∃ q : ℚ, (q : ℝ) ∈ interior S := by
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hn
  wlog halt : a<b generalizing a b
  · exact this b hb a ha hab.symm (lt_of_le_of_ne (le_of_not_gt halt) hab.symm)
  obtain ⟨q,hqa,hqb⟩ := exists_rat_btwn halt
  refine ⟨q,?_⟩
  have hs : Ioo a b ⊆ S := fun _ hx => hS.ordConnected.out ha hb ⟨hx.1.le,hx.2.le⟩
  exact (isOpen_Ioo.subset_interior_iff.mpr hs) ⟨hqa,hqb⟩

lemma ae_subsingleton (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (D : ℝ → Set ℝ)
    (hc : ∀ t ∈ K, Convex ℝ (D t))
    (hd : ∀ s ∈ K, ∀ t ∈ K, s<t → 0<μ (Ioo s t) → Disjoint (D s) (D t)) :
    μ {t | t∈K ∧ ¬ (D t).Subsingleton}=0 := by
  let S (q : ℚ) : Set ℝ := {t | t∈K ∧ (q : ℝ)∈interior (D t)}
  have hz (q : ℚ) : μ (S q)=0 := by
    apply measure_zero_of_null_gaps μ (S q) (hK.subset (fun _ ht => ht.1))
    intro s hs t ht hst
    apply le_antisymm _ zero_le
    by_contra h
    have hp : 0<μ (Ioo s t) := lt_of_not_ge h
    exact Set.disjoint_left.mp (hd s hs.1 t ht.1 hst hp)
      (interior_subset hs.2) (interior_subset ht.2)
  apply measure_mono_null (t := ⋃ q : ℚ, S q)
  · intro t ht
    obtain ⟨q,hq⟩ := interval_has_rat_interior (hc t ht.1) ht.2
    exact mem_iUnion.mpr ⟨q,ht.1,hq⟩
  · exact measure_iUnion_null hz

theorem exists_three_singletons (μ : Measure ℝ) [NullSingletonClass μ]
    (K : Set ℝ) (hK : Bornology.IsBounded K) (hpos : 0<μ K) (D : ℝ → Set ℝ)
    (hne : ∀ t ∈ K, (D t).Nonempty) (hc : ∀ t ∈ K, Convex ℝ (D t))
    (hd : ∀ s ∈ K, ∀ t ∈ K, s<t → 0<μ (Ioo s t) → Disjoint (D s) (D t)) :
    ∃ t₁ t₂ t₃ d₁ d₂ d₃ : ℝ,
      t₁∈K ∧ t₂∈K ∧ t₃∈K ∧ t₁<t₂ ∧ t₂<t₃ ∧
      D t₁={d₁} ∧ D t₂={d₂} ∧ D t₃={d₃} ∧
      d₁≠d₂ ∧ d₂≠d₃ ∧ d₁≠d₃ := by
  let B : Set ℝ := {t | t∈K ∧ ¬ (D t).Subsingleton}
  let G := (K \ B) ∩ μ.support
  have hz : μ B=0 := ae_subsingleton μ K hK D hc hd
  have hg : 0<μ G := by
    rw [show G=(K \ B) ∩ μ.support from rfl,measure_inter_conull Measure.measure_compl_support,
      measure_sdiff_null hz]
    exact hpos
  have hi : G.Infinite := by
    by_contra h
    have hh := (Set.not_infinite.mp h).measure_zero μ
    exact (ne_of_gt hg) hh
  obtain ⟨F,hFG,hF⟩ := hi.exists_subset_card_eq 5
  let t : Fin 5 → ℝ := F.orderEmbOfFin hF
  have ht : StrictMono t := (F.orderEmbOfFin hF).strictMono
  have hmem (i : Fin 5) : t i∈G := hFG (F.orderIsoOfFin hF i).property
  have hsub (i : Fin 5) : (D (t i)).Subsingleton := by
    by_contra hn
    exact (hmem i).1.2 ⟨(hmem i).1.1,hn⟩
  obtain ⟨d₁,hd₁⟩ := hne (t 0) (hmem 0).1.1
  obtain ⟨d₂,hd₂⟩ := hne (t 2) (hmem 2).1.1
  obtain ⟨d₃,hd₃⟩ := hne (t 4) (hmem 4).1.1
  have h02 : 0<μ (Ioo (t 0) (t 2)) :=
    (Measure.mem_support_iff_forall _).mp (hmem 1).2 _ (Ioo_mem_nhds (ht (by decide)) (ht (by decide)))
  have h24 : 0<μ (Ioo (t 2) (t 4)) :=
    (Measure.mem_support_iff_forall _).mp (hmem 3).2 _ (Ioo_mem_nhds (ht (by decide)) (ht (by decide)))
  have h04 : 0<μ (Ioo (t 0) (t 4)) := h02.trans_le (measure_mono (Ioo_subset_Ioo_right (ht (by decide)).le))
  refine ⟨t 0,t 2,t 4,d₁,d₂,d₃,(hmem 0).1.1,(hmem 2).1.1,(hmem 4).1.1,
    ht (by decide),ht (by decide),(hsub 0).eq_singleton_of_mem hd₁,
    (hsub 2).eq_singleton_of_mem hd₂,(hsub 4).eq_singleton_of_mem hd₃,?_,?_,?_⟩
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 0).1.1 _ (hmem 2).1.1 (ht (by decide)) h02) hd₁ (h.symm ▸ hd₂)
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 2).1.1 _ (hmem 4).1.1 (ht (by decide)) h24) hd₂ (h.symm ▸ hd₃)
  · intro h
    exact Set.disjoint_left.mp (hd _ (hmem 0).1.1 _ (hmem 4).1.1 (ht (by decide)) h04) hd₁ (h.symm ▸ hd₃)

end PlanarHalving.Directions

namespace PlanarHalving.Batches
open Set TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

noncomputable def System.timeWindow (S : @System n R k a P) [NeZero R] (J : Window) :
    @System n (length R J) k a P :=
  S.window (start R J) (length R J) (by rw [start_add_length]; exact stop_le R J)

lemma System.timeWindow_edges (S : @System n R k a P) [NeZero R] (J : Window) :
    (S.timeWindow J).edges ⊆ S.edges := S.window_edges _ _ _

noncomputable def System.edgeTime (S : @System n R k a P) [NeZero R] [NeZero a] (e : ↥S.edges) : I :=
  time R (S.trace e.property).batch

lemma System.timeWindow_mem (S : @System n R k a P) [NeZero R] [NeZero a]
    (J : Window) (e : ↥S.edges) : e.val ∈ (S.timeWindow J).edges ↔ S.edgeTime e ∈ carrier J := by
  classical
  rw [System.edgeTime,mem_carrier_iff]
  constructor
  · intro he
    obtain ⟨b,hl,hg⟩ := ((S.timeWindow J).mem_edges e.val).mp he
    have hb := S.batch_unique (b := ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩)
      ⟨hl,hg⟩ ⟨(S.trace e.property).loss,(S.trace e.property).gain⟩
    have heq := congrArg Fin.val hb
    have hbl := b.isLt
    have hs := start_add_length R J
    dsimp at heq
    omega
  · intro h
    let b : Fin (length R J) := ⟨(S.trace e.property).batch.val-start R J,by
      have := start_add_length R J
      omega⟩
    apply ((S.timeWindow J).mem_edges e.val).mpr
    refine ⟨b,?_,?_⟩
    all_goals
      have heq : (⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩ : Fin R) =
          (S.trace e.property).batch := by
        apply Fin.ext
        dsimp [b]
        omega
    · change e.val.1 ∈ S.loss ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩
      rw [heq]
      exact (S.trace e.property).loss
    · change e.val.2 ∈ S.gain ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩
      rw [heq]
      exact (S.trace e.property).gain

lemma System.edgeTime_distribution (S : @System n R k a P) [NeZero R] [NeZero a]
    (b : Fin R) :
    (Finset.univ.filter fun e : ↥S.edges => (S.trace e.property).batch=b).card=a^2 := by
  classical
  have he : (Finset.univ.filter fun e : ↥S.edges => (S.trace e.property).batch=b).card =
      ((S.loss b).product (S.gain b)).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      have hh := (Finset.mem_filter.mp he).2
      exact Finset.mem_product.mpr (hh ▸ ⟨(S.trace e.property).loss,(S.trace e.property).gain⟩)
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he
      have hm : e∈S.edges := (S.mem_edges e).mpr ⟨b,Finset.mem_product.mp he⟩
      refine ⟨⟨e,hm⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      exact S.batch_unique ⟨(S.trace hm).loss,(S.trace hm).gain⟩ (Finset.mem_product.mp he)
  rw [he]
  calc
    _ = (S.loss b).card * (S.gain b).card := Finset.card_product _ _
    _ = a^2 := by rw [S.card_loss,S.card_gain,pow_two]

end PlanarHalving.Batches

end OAI
