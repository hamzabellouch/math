import OAI.Probability.DirectionalWalk.Radii

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def heightEnvelope {Ω : Type*} (s : ℕ → Ω → ℝ) (c C b : ℝ) : Set Ω :=
  {x | ∀ k : ℕ, c*k-b ≤ s k x ∧ s k x ≤ C*k+b}

lemma measurableSet_heightEnvelope {Ω : Type*} [MeasurableSpace Ω]
    (s : ℕ → Ω → ℝ) (hs : ∀ k, Measurable (s k)) (c C b : ℝ) :
    MeasurableSet (heightEnvelope s c C b) := by
  unfold heightEnvelope
  simp only [Set.ofPred_forall,Set.ofPred_and]
  exact MeasurableSet.iInter (fun k => (measurableSet_le measurable_const (hs k)).inter
    (measurableSet_le (hs k) measurable_const))

lemma heightEnvelope_mono {Ω : Type*} (s : ℕ → Ω → ℝ) (c C : ℝ) :
    Monotone (heightEnvelope s c C) := by
  intro a b hab x hx k
  obtain ⟨hl,hu⟩ := hx k
  constructor <;> linarith

lemma exists_heightEnvelope_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → Ω → ℝ)
    (hs : ∀ k, Measurable (s k)) {m c C : ℝ}
    (hm : ∀ᵐ x ∂P, Tendsto (fun n : ℕ => s n x / n) atTop (𝓝 m))
    (hc : c < m) (hC : m < C) {q : ℝ} (hq : q < 1) :
    ∃ b : ℝ, 0 ≤ b ∧ q < P.real (heightEnvelope s c C b) := by
  have hcover : P (⋃ b : ℕ, heightEnvelope s c C b) = 1 := by
    apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (fun b : ℕ =>
      measurableSet_heightEnvelope s hs c C b))).mp
    filter_upwards [hm] with x hx
    obtain ⟨b,_,hb⟩ := linear_envelope_of_tendsto (fun n => s n x) hx hc hC
    obtain ⟨k,hk⟩ := exists_nat_ge b
    exact Set.mem_iUnion.mpr ⟨k,heightEnvelope_mono s c C hk hb⟩
  have ht := tendsto_measure_iUnion_atTop (μ := P)
    (show Monotone (fun b : ℕ => heightEnvelope s c C b) from
      fun i j hij => heightEnvelope_mono s c C (Nat.cast_le.mpr hij))
  rw [hcover] at ht
  have htr : Tendsto (fun b : ℕ => P.real (heightEnvelope s c C b)) atTop (𝓝 1) := by
    simpa only [ENNReal.toReal_one,Function.comp_def,Measure.real] using (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp ht
  have hev : ∀ᶠ b : ℕ in atTop, q < P.real (heightEnvelope s c C b) :=
    htr.eventually (eventually_gt_nhds hq)
  obtain ⟨b,hb⟩ := hev.exists
  exact ⟨b,Nat.cast_nonneg _,hb⟩

lemma indepFun_initial_block {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (f : ℕ → Ω → α) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f P) (n : ℕ) :
    IndepFun (fun x (i : Fin n) => f i x) (f n) P := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hh := hind.indepFun_finset (Finset.range n) {n} hd hf
  exact hh.comp (Measurable.of_eval (f := fun v (i : Fin n) =>
    v ⟨i,Finset.mem_range.mpr i.isLt⟩) (fun _ => measurable_pi_apply _))
    (measurable_pi_apply ⟨n,by simp⟩)

noncomputable def prefixSum {α : Type*} {n : ℕ} (f : α → ℝ) (v : Fin n → α) (k : ℕ) : ℝ :=
  ∑ j : Fin n, if (j : ℕ) < k then f (v j) else 0

lemma prefixSum_eq {α : Type*} (f : α → ℝ) (v : ℕ → α) {k n : ℕ} (hk : k ≤ n) :
    prefixSum f (fun i : Fin n => v i) k = ∑ j ∈ Finset.range k, f (v j) := by
  classical
  unfold prefixSum
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then f (v j) else 0),← Finset.sum_filter]
  have he : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he]

lemma initial_block_factorization {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (f : ℕ → Ω → α) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun f P) (n : ℕ) (A : Set (Fin n → α)) (B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    P.real ({x | (fun i : Fin n => f i x) ∈ A} ∩ {x | f n x ∈ B}) =
      P.real {x | (fun i : Fin n => f i x) ∈ A} * P.real {x | f n x ∈ B} := by
  have hh := (indepFun_initial_block P f hf hind n).measure_inter_preimage_eq_mul A B hA hB
  exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul

def goodRadiusTuple {d m : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) :
    Set (Fin m → Word d) :=
  {γ | ∀ k : ℕ, k ≤ m → c*k-b ≤ prefixSum (slabWidth v) γ k ∧
    prefixSum (slabWidth v) γ k ≤ C*k+b ∧ prefixSum slabRadius γ k ≤ a*k}

def goodRadiusPrefix {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) : Set (Path d) :=
  {X | (fun i : Fin m => slabs v X i) ∈ goodRadiusTuple v a c C b}

lemma goodRadiusPrefix_iff {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) (X : Path d) :
    X ∈ goodRadiusPrefix v a c C b m ↔ ∀ k : ℕ, k ≤ m →
      c*k-b ≤ slabHeightSum v X k ∧ slabHeightSum v X k ≤ C*k+b ∧
      slabRadiusSum v X k ≤ a*k := by
  simp only [goodRadiusPrefix,goodRadiusTuple,Set.mem_ofPred_eq]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  rw [prefixSum_eq _ _ hk,prefixSum_eq _ _ hk]
  rfl

lemma measurableSet_goodRadiusPrefix {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) (m : ℕ) :
    MeasurableSet (goodRadiusPrefix v a c C b m) :=
  (Set.to_countable _).measurableSet.preimage (Measurable.of_eval (fun i =>
    (measurable_pi_apply (i : ℕ)).comp (measurable_slabs v)))

lemma goodRadiusPrefix_mono {d : ℕ} (v : Fin d → ℝ) (a c C b : ℝ) {m n : ℕ}
    (hmn : m ≤ n) : goodRadiusPrefix v a c C b n ⊆ goodRadiusPrefix v a c C b m := by
  intro X hX
  rw [goodRadiusPrefix_iff] at hX ⊢
  exact fun k hk => hX k (hk.trans hmn)

lemma slab_truncated_average_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n) :
    (conditioned μ v).real {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a*k < slabRadiusSum v X k} ≤
      2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a := by
  let := conditioned_probability μ v hp
  have hh := stationary_truncated_average_bound (conditioned μ v) (cutSuffix v)
    (cutSuffix_measurePreserving μ hell v hv hp) (fun X => slabRadius (firstWord v X))
    ((measurable_of_countable slabRadius).comp (measurable_firstWord v))
    (fun _ => slabRadius_nonneg _) a ha n hn
  have hi := (slabs_identDistrib μ hell v hv hp 0).comp
    (measurable_of_countable (fun γ => min (slabRadius γ) (a*n)))
  have he : truncatedMoment (conditioned μ v) (fun X => slabRadius (firstWord v X)) (a*n) =
      truncatedMoment (slabLaw μ v) slabRadius (a*n) := hi.integral_eq
  simpa only [initialAverageBad,slabs,slabRadiusSum,he] using hh

lemma goodRadiusPrefix_probability {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 0 < n) :
    (conditioned μ v).real (heightEnvelope (fun k X => slabHeightSum v X k) c C b) -
      2*truncatedMoment (slabLaw μ v) slabRadius (a*n)/a ≤
      (conditioned μ v).real (goodRadiusPrefix v a c C b n) := by
  let := conditioned_probability μ v hp
  let B : Set (Path d) := {X | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ a*k < slabRadiusSum v X k}
  have hsub : heightEnvelope (fun k X => slabHeightSum v X k) c C b ⊆
      goodRadiusPrefix v a c C b n ∪ B := by
    intro X hX
    by_cases hB : X ∈ B
    · exact Or.inr hB
    · left
      rw [goodRadiusPrefix_iff]
      intro k hk
      refine ⟨(hX k).1,(hX k).2,?_⟩
      by_cases hk0 : k = 0
      · simp [hk0,slabRadiusSum]
      · exact le_of_not_gt (fun h => hB ⟨k,Nat.pos_of_ne_zero hk0,hk,h⟩)
  have hu := (measureReal_mono (μ := conditioned μ v) hsub (measure_ne_top _ _)).trans
    (measureReal_union_le (μ := conditioned μ v) _ _)
  have hb := slab_truncated_average_bound μ hell v hv hp a ha n hn
  change (conditioned μ v).real B ≤ _ at hb
  linarith

lemma goodRadiusPrefix_current_factorization {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (a c C b : ℝ) (n : ℕ)
    (G : Set (Word d)) :
    (conditioned μ v).real (goodRadiusPrefix v a c C b n ∩ {X | slabs v X n ∈ G}) =
      (conditioned μ v).real (goodRadiusPrefix v a c C b n) * (slabLaw μ v).real G := by
  have hh := initial_block_factorization (conditioned μ v) (fun i X => slabs v X i)
    (fun i => (measurable_pi_apply i).comp (measurable_slabs v))
    (slabs_iid μ hell v hv hp) n (goodRadiusTuple v a c C b) G
    (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
  have he : (conditioned μ v).real {X | slabs v X n ∈ G} = (slabLaw μ v).real G := by
    apply congrArg ENNReal.toReal
    rw [← slabs_marginal μ hell v hv hp n]
    exact (Measure.map_apply ((measurable_pi_apply n).comp (measurable_slabs v))
      (Set.to_countable G).measurableSet).symm
  simpa only [goodRadiusPrefix,he] using hh

lemma truncatedMoment_sub_le_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) :
    truncatedMoment P f (t+D)-truncatedMoment P f t ≤ D*P.real {x | t < f x} := by
  have hS : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hfm
  have hi := (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD)).sub
    (integrable_min_const P f hfm hf t ht)
  have hb : ∀ x, min (f x) (t+D)-min (f x) t ≤
      Set.indicator {x | t < f x} (fun _ => D) x := by
    intro x
    by_cases h : t < f x
    · rw [Set.indicator_of_mem (s := {x | t < f x}) h,min_eq_right h.le]
      linarith [min_le_right (f x) (t+D)]
    · have he : f x ≤ t := le_of_not_gt h
      rw [Set.indicator_of_notMem (s := {x | t < f x}) h,min_eq_left he,
        min_eq_left (he.trans (le_add_of_nonneg_right hD))]
      linarith
  have hh := integral_mono hi ((integrable_const D).indicator hS) hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD))
      (integrable_min_const P f hfm hf t ht),integral_indicator_const D hS,
    smul_eq_mul,mul_comm (P.real _) D] at hh
  exact hh

lemma mul_tail_le_truncatedMoment_sub {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {t D : ℝ} (ht : 0 ≤ t) (hD : 0 ≤ D) :
    D*P.real {x | t+D < f x} ≤ truncatedMoment P f (t+D)-truncatedMoment P f t := by
  have hS : MeasurableSet {x | t+D < f x} := measurableSet_lt measurable_const hfm
  have hi := (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD)).sub
    (integrable_min_const P f hfm hf t ht)
  have hb : ∀ x, Set.indicator {x | t+D < f x} (fun _ => D) x ≤
      min (f x) (t+D)-min (f x) t := by
    intro x
    by_cases h : t+D < f x
    · rw [Set.indicator_of_mem (s := {x | t+D < f x}) h,min_eq_right h.le,
        min_eq_right ((le_add_of_nonneg_right hD).trans h.le)]
      linarith
    · rw [Set.indicator_of_notMem (s := {x | t+D < f x}) h]
      exact sub_nonneg.mpr (min_le_min_left _ (le_add_of_nonneg_right hD))
  have hh := integral_mono ((integrable_const D).indicator hS) hi hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_min_const P f hfm hf (t+D) (add_nonneg ht hD))
      (integrable_min_const P f hfm hf t ht),integral_indicator_const D hS,
    smul_eq_mul,mul_comm (P.real _) D] at hh
  exact hh

lemma truncatedMoment_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    truncatedMoment P f 0 = 0 := by
  simp [truncatedMoment, min_eq_right (hf _)]

lemma tail_sum_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) (l n : ℕ) :
    truncatedMoment P f (a*(l+n))-truncatedMoment P f (a*l) ≤
      a*∑ i ∈ Finset.range n, P.real {x | a*(l+i) < f x} := by
  have hi (i : ℕ) := truncatedMoment_sub_le_tail P f hfm hf
    (t := a*(l+i)) (D := a) (mul_nonneg ha.le (by positivity)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hi i)
  have he (i : ℕ) : a*(l+i)+a = a*((l+(i+1) : ℕ) : ℝ) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum] at hsum
  have htel := Finset.sum_range_sub (fun i : ℕ => truncatedMoment P f (a*(l+i))) n
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at htel hsum
  rw [htel] at hsum
  exact hsum

lemma tail_sum_upper {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    a*∑ i ∈ Finset.range n, P.real {x | a*(i+1) < f x} ≤
      truncatedMoment P f (a*n) := by
  have hi (i : ℕ) := mul_tail_le_truncatedMoment_sub P f hfm hf
    (t := a*i) (D := a) (mul_nonneg ha.le (Nat.cast_nonneg _)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hi i)
  have he (i : ℕ) : a*i+a = a*((i+1 : ℕ) : ℝ) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum,Finset.sum_range_sub (fun i : ℕ => truncatedMoment P f (a*i)) n] at hsum
  simpa [truncatedMoment_zero P f hf] using hsum

lemma summable_real_tail_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f P) :
    Summable (fun n : ℕ => P.real {x | (n+1 : ℝ) < f x}) := by
  apply summable_of_sum_range_le (fun _ => measureReal_nonneg) (c := ∫ x, f x ∂P)
  intro n
  have hb := tail_sum_upper P f hfm hf (a := 1) zero_lt_one n
  simp only [one_mul] at hb
  apply hb.trans
  exact integral_mono (integrable_min_const P f hfm hf n (Nat.cast_nonneg _)) hfi
    (fun x => min_le_left _ _)

lemma union_lower_of_pair_bounds {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (A G : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hAG : ∀ i, A i ⊆ G i)
    (hpair : ∀ i j, i ≠ j → P.real (G i ∩ G j) ≤ P.real (G i)*P.real (G j))
    (s : Finset ι) :
    (∑ i ∈ s, P.real (A i)) ≤ P.real (⋃ i ∈ s, A i) + (∑ i ∈ s, P.real (G i))^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    let L := ∑ j ∈ s, P.real (G j)
    have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
    have hp : 0 ≤ P.real (G i) := measureReal_nonneg
    have hU : MeasurableSet U := MeasurableSet.biUnion (Finset.countable_toSet s) (fun j _ => hA j)
    have hu : P.real (A i ∪ U) + P.real (A i ∩ U) = P.real (A i)+P.real U :=
      measureReal_union_add_inter₀ hU.nullMeasurableSet (measure_ne_top _ _) (measure_ne_top _ _)
    have hsub : A i ∩ U ⊆ ⋃ j ∈ s, G i ∩ G j := by
      rintro x ⟨hx,hy⟩
      obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨j,hj,hAG i hx,hAG j hxj⟩
    have hint : P.real (A i ∩ U) ≤ P.real (G i)*L := by
      apply (measureReal_mono hsub (measure_ne_top _ _)).trans
      apply (measureReal_biUnion_finset_le s _).trans
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj => hpair i j (fun hij => hi (hij ▸ hj)))
    simp only [Finset.sum_insert hi,Finset.set_biUnion_insert]
    change P.real (A i) + ∑ j ∈ s, P.real (A j) ≤ P.real (A i ∪ U) + (P.real (G i)+L)^2
    change (∑ j ∈ s, P.real (A j)) ≤ P.real U + L^2 at ih
    nlinarith

lemma controlled_occurrence_lower {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (R G : ι → Set Ω)
    (hR : ∀ i, MeasurableSet (R i)) (hG : ∀ i, MeasurableSet (G i))
    (hind : ∀ i, P.real (R i ∩ G i) = P.real (R i)*P.real (G i))
    (hpair : ∀ i j, i ≠ j → P.real (G i ∩ G j) ≤ P.real (G i)*P.real (G j))
    (s : Finset ι) (q : ℝ) (hq : ∀ i ∈ s, q ≤ P.real (R i)) :
    q*(∑ i ∈ s, P.real (G i)) - (∑ i ∈ s, P.real (G i))^2 ≤
      P.real (⋃ i ∈ s, R i ∩ G i) := by
  have hu := union_lower_of_pair_bounds P (fun i => R i ∩ G i) G
    (fun i => (hR i).inter (hG i)) (fun _ => Set.inter_subset_right) hpair s
  have hl : q*(∑ i ∈ s, P.real (G i)) ≤ ∑ i ∈ s, P.real (R i ∩ G i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [hind]
    exact mul_le_mul_of_nonneg_right (hq i hi) measureReal_nonneg
  linarith

lemma truncatedMoment_add_measure {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] (f : Ω → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    truncatedMoment (P+Q) f t = truncatedMoment P f t + truncatedMoment Q f t :=
  integral_add_measure (integrable_min_const P f hfm hf t ht)
    (integrable_min_const Q f hfm hf t ht)

lemma tail_sum_Ico_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 < a) {l n : ℕ} (hln : l ≤ n) :
    truncatedMoment P f (a*(n+1))-truncatedMoment P f (a*(l+1)) ≤
      a*∑ i ∈ Finset.Ico l n, P.real {x | a*(i+1) < f x} := by
  have hi (i : ℕ) := truncatedMoment_sub_le_tail P f hfm hf
    (t := a*(i+1)) (D := a) (mul_nonneg ha.le (by positivity)) ha.le
  have hsum := Finset.sum_le_sum (s := Finset.Ico l n) (fun i _ => hi i)
  have he (i : ℕ) : a*(i+1)+a = a*((i+1 : ℕ)+1) := by push_cast; ring
  simp_rw [he] at hsum
  rw [← Finset.mul_sum,Finset.sum_Ico_sub (fun i : ℕ => truncatedMoment P f (a*(i+1))) hln] at hsum
  exact hsum

def largeRadiusWord {Ω : Type*} (R L : Ω → ℝ) (a : ℝ) (i : ℕ) : Set Ω :=
  {x | a*(i+1) < R x ∧ L x ≤ i+1}

lemma largeRadius_mass_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (R L : Ω → ℝ) (hR : Measurable R)
    (hRn : ∀ x, 0 ≤ R x) {a : ℝ} (ha : 0 < a) {l n : ℕ} (hln : l ≤ n) :
    (truncatedMoment P R (a*(n+1))-truncatedMoment P R (a*(l+1)))/a -
        (∑ i ∈ Finset.Ico l n, P.real {x | (i+1 : ℝ) < L x}) ≤
        ∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L a i) ∧
      (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L a i)) ≤
        truncatedMoment P R (a*n)/a := by
  have hu (i : ℕ) : P.real (largeRadiusWord R L a i) ≤ P.real {x | a*(i+1) < R x} :=
    measureReal_mono (fun _ h => h.1) (measure_ne_top _ _)
  have hl (i : ℕ) : P.real {x | a*(i+1) < R x} ≤
      P.real (largeRadiusWord R L a i) + P.real {x | (i+1 : ℝ) < L x} := by
    have hs : {x | a*(i+1) < R x} ⊆ largeRadiusWord R L a i ∪ {x | (i+1 : ℝ) < L x} := by
      intro x hx
      by_cases h : L x ≤ i+1
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (lt_of_not_ge h)
    exact (measureReal_mono hs (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  constructor
  · have hsum := Finset.sum_le_sum (s := Finset.Ico l n) (fun i _ => hl i)
    rw [Finset.sum_add_distrib] at hsum
    have hh := tail_sum_Ico_lower P R hR hRn ha hln
    have hh' : (truncatedMoment P R (a*(n+1))-truncatedMoment P R (a*(l+1)))/a ≤
        ∑ i ∈ Finset.Ico l n, P.real {x | a*(i+1) < R x} :=
      (div_le_iff₀ ha).mpr (by nlinarith only [hh])
    linarith
  · apply (Finset.sum_le_sum (fun i _ => hu i)).trans
    have hs : Finset.Ico l n ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
    apply (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => measureReal_nonneg)).trans
    apply (le_div_iff₀ ha).mpr
    nlinarith only [tail_sum_upper P R hR hRn ha n]

lemma largeRadius_mass_pair_lower {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (R L K : Ω → ℝ) (hR : Measurable R) (hRn : ∀ x, 0 ≤ R x)
    {a B η : ℝ} (ha : 0 < a) (hB : 1 ≤ B) (hη : 0 < η) {l n : ℕ} (hln : l ≤ n)
    (hscale : η*a ≤ truncatedMoment (P+Q) R (a*n))
    (hsmall : truncatedMoment (P+Q) R (B*a*(l+1)) < η*a/4)
    (hwidth : (∑ i ∈ Finset.Ico l n, P.real {x | (i+1 : ℝ) < L x}) +
      (∑ i ∈ Finset.Ico l n, Q.real {x | (i+1 : ℝ) < K x}) < η/(4*B)) :
    η/(2*B) ≤ (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L (B*a) i)) +
      (∑ i ∈ Finset.Ico l n, Q.real (largeRadiusWord R K (B*a) i)) := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBa : 0 < B*a := mul_pos hB0 ha
  have hp := (largeRadius_mass_bounds P R L hR hRn hBa hln).1
  have hq := (largeRadius_mass_bounds Q R K hR hRn hBa hln).1
  have hadd1 := truncatedMoment_add_measure P Q R hR hRn
    (t := B*a*(n+1)) (by positivity)
  have hadd2 := truncatedMoment_add_measure P Q R hR hRn
    (t := B*a*(l+1)) (by positivity)
  have hmono : truncatedMoment (P+Q) R (a*n) ≤ truncatedMoment (P+Q) R (B*a*(n+1)) := by
    apply truncatedMoment_mono _ _ hR hRn (by positivity)
    have hh := mul_le_mul_of_nonneg_right hB (show 0 ≤ a*((n : ℝ)+1) by positivity)
    nlinarith only [hh,ha]
  have hlow : η*a ≤ truncatedMoment (P+Q) R (B*a*(n+1)) := hscale.trans hmono
  have hd : η/(2*B) + η/(4*B) = (η*a-η*a/4)/(B*a) := by field_simp; ring
  rw [hadd1] at hlow
  rw [hadd2] at hsmall
  have htot : (η*a-η*a/4)/(B*a) ≤
      (truncatedMoment P R (B*a*(n+1))-truncatedMoment P R (B*a*(l+1)))/(B*a) +
      (truncatedMoment Q R (B*a*(n+1))-truncatedMoment Q R (B*a*(l+1)))/(B*a) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hBa.le
  linarith

lemma largeRadius_mass_pair_upper {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (R L K : Ω → ℝ) (hR : Measurable R) (hRn : ∀ x, 0 ≤ R x)
    {a B η : ℝ} (ha : 0 < a) (hB : 1 ≤ B) {l n : ℕ} (hln : l ≤ n)
    (hscale : truncatedMoment (P+Q) R (a*n) < 2*η*a) :
    (∑ i ∈ Finset.Ico l n, P.real (largeRadiusWord R L (B*a) i)) +
      (∑ i ∈ Finset.Ico l n, Q.real (largeRadiusWord R K (B*a) i)) < 2*η := by
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBa : 0 < B*a := mul_pos hB0 ha
  have hp := (largeRadius_mass_bounds P R L hR hRn hBa hln).2
  have hq := (largeRadius_mass_bounds Q R K hR hRn hBa hln).2
  have hadd := truncatedMoment_add_measure P Q R hR hRn (t := B*a*n) (by positivity)
  have hmul := truncatedMoment_mul_le (P+Q) R hR hRn (t := a*n) (by positivity) hB
  rw [← mul_assoc] at hmul
  have hh : truncatedMoment (P+Q) R (B*a*n)/(B*a) < 2*η := by
    apply (div_lt_iff₀ hBa).mpr
    have hs := mul_lt_mul_of_pos_left hscale hB0
    nlinarith only [hmul,hs]
  rw [hadd,add_div] at hh
  linarith

lemma slabs_event_measureReal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (i : ℕ) (G : Set (Word d)) :
    (conditioned μ v).real {X | slabs v X i ∈ G} = (slabLaw μ v).real G := by
  apply congrArg ENNReal.toReal
  rw [← slabs_marginal μ hell v hv hp i]
  exact (Measure.map_apply ((measurable_pi_apply i).comp (measurable_slabs v))
    (Set.to_countable G).measurableSet).symm

lemma slabs_pair_event_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) {i j : ℕ} (hij : i ≠ j)
    (G H : Set (Word d)) :
    (conditioned μ v).real ({X | slabs v X i ∈ G} ∩ {X | slabs v X j ∈ H}) =
      (slabLaw μ v).real G * (slabLaw μ v).real H := by
  have hh := ((slabs_iid μ hell v hv hp).indepFun hij).measure_inter_preimage_eq_mul
    G H (Set.to_countable G).measurableSet (Set.to_countable H).measurableSet
  have hh' := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_mul] at hh'
  change (conditioned μ v).real ({X | slabs v X i ∈ G} ∩ {X | slabs v X j ∈ H}) =
    (conditioned μ v).real {X | slabs v X i ∈ G} * (conditioned μ v).real {X | slabs v X j ∈ H} at hh'
  rwa [slabs_event_measureReal μ hell v hv hp i G,slabs_event_measureReal μ hell v hv hp j H] at hh'

end DirectionalZeroOne

end OAI
