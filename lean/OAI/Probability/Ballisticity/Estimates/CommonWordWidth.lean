import Mathlib
import OAI.Probability.Ballisticity.Estimates.FixedPairSuffix

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma recordCount_eq_height_at_record {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (X : Path d)
    (hstep : ∀ n, height (X (n+1)) ≤ height (X n)+1) {n : ℕ}
    (hn : StrictRecord ℓ X n) :
    height (X n) = height (X 0) + (recordCount ℓ X n : ℤ) := by
  obtain ⟨hb,j,hj,he⟩ := recordCount_integer_height ℓ height hproj X hstep n
  by_cases hjn : j = n
  · simpa only [hjn] using he
  · have hh := hn j (lt_of_le_of_ne hj hjn)
    rw [hproj,hproj] at hh
    have hlt : height (X j) < height (X n) := by exact_mod_cast hh
    have := hb n le_rfl
    omega

lemma independent_conditioned_true_at_index_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) {r : ℕ} (hr : 0 < r) :
    (annealedLaw ν (NoDrop ℓ 0))^2 ≤ independentConditionedPairLaw ν ℓ
      {P | ∃ n m, CommonTrueRecord ℓ P n m ∧ recordCount ℓ P.1 n = r} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let A : Set (Path d) := {X | ∃ n, 0 < n ∧ TrueRecord ℓ X n ∧ recordCount ℓ X n = r}
  have hlow : annealedLaw ν (NoDrop ℓ 0) ≤ conditionedLaw ν ℓ A :=
    conditioned_true_at_index_lower ν ℓ htrans hr
  calc
    (annealedLaw ν (NoDrop ℓ 0))^2 ≤ (conditionedLaw ν ℓ A)^2 := pow_le_pow_left' hlow 2
    _ = independentConditionedPairLaw ν ℓ (A ×ˢ A) := by
      rw [independentConditionedPairLaw,Measure.prod_prod,pow_two]
    _ ≤ _ := by
      apply measure_mono_ae
      have hac := conditionedLaw_absolutelyContinuous ν ℓ
      have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
      have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
      filter_upwards [h0,hNN] with P h0 hNN hP
      obtain ⟨n,_,hn,hnr⟩ := hP.1
      obtain ⟨m,_,hm,hmr⟩ := hP.2
      have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
        obtain ⟨e,he⟩ := hNN.1 j
        rw [he]; exact hstep _ _
      have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
        obtain ⟨e,he⟩ := hNN.2 j
        rw [he]; exact hstep _ _
      have he1 := recordCount_eq_height_at_record ℓ height hproj P.1 hs1 hn.1
      have he2 := recordCount_eq_height_at_record ℓ height hproj P.2 hs2 hm.1
      refine ⟨n,m,⟨hn,hm,?_⟩,hnr⟩
      rw [hproj,hproj,he1,he2,h0.1,h0.2,hnr,hmr]

noncomputable def commonWordWidth {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : ℕ := wordRecordCount ℓ wv.1

lemma commonWordWidth_positive {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : 0 < commonWordWidth ℓ wv := by
  have hr : StrictRecord ℓ (wordPath 0 wv.1) wv.1.length :=
    (strictRecord_congr_prefix ℓ le_rfl hP.2.1.1).mp hP.2.2.2.2.1.1.1
  simpa only [commonWordWidth,wordRecordCount,recordCount_zero] using
    recordCount_lt_of_strictRecord ℓ (wordPath 0 wv.1) hP.2.2.1 hr

lemma independent_commonWordWidth_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => (commonWordWidth ℓ (firstPairWord ℓ P) : ℝ))
      (independentConditionedPairLaw ν ℓ) ∧
    (∫ P, (commonWordWidth ℓ (firstPairWord ℓ P) : ℝ) ∂independentConditionedPairLaw ν ℓ) ≤
      1 / ((annealedLaw ν).real (NoDrop ℓ 0))^2 := by
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ (ne_of_gt hp)
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ (ne_of_gt hp)
  let S : ℕ → (Path d × Path d) → ℕ := fun n P => commonWordWidth ℓ (commonWords ℓ P n)
  have hm : Measurable (commonWordWidth ℓ) := measurable_of_countable _
  have hS (n : ℕ) : Measurable (S n) := hm.comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))
  have hind : iIndepFun S (independentConditionedPairLaw ν ℓ) :=
    (common_words_independent ν ℓ htrans height hproj hstep).comp (fun _ => commonWordWidth ℓ) (fun _ => hm)
  have hid (n : ℕ) : IdentDistrib (S n) (S 0) (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) :=
    (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp hm
  have hall := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  have hpos : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n, 0 < S n P := by
    filter_upwards [hall] with P hP n
    exact commonWordWidth_positive ℓ _ _ (hP n)
  have hp' : 0 < ((annealedLaw ν).real (NoDrop ℓ 0))^2 :=
    sq_pos_of_pos (ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top _ _))
  apply renewal_mean_bound (independentConditionedPairLaw ν ℓ) S hS hind hid hpos hp'
  intro r hr
  have hlow := independent_conditioned_true_at_index_lower ν ℓ htrans height hproj hstep hr
  change (annealedLaw ν (NoDrop ℓ 0)).toReal ^ 2 ≤ _
  rw [← ENNReal.toReal_pow]
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hlow).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  filter_upwards [hall,h0] with P hP h0 hR
  obtain ⟨j,k,hjk,hcount⟩ := hR
  obtain ⟨n,hn⟩ := commonTrueRecord_eq_commonTimes ℓ P h0.1 h0.2 hP hjk
  refine ⟨n,?_⟩
  change (∑ i ∈ Finset.range n, wordRecordCount ℓ (commonWords ℓ P i).1) = r
  rw [← recordCount_commonTimes ℓ P h0.1 h0.2 hP,hn]
  exact hcount

lemma singleCommonIndex_exists_bound {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    ∃ n, (firstPairWord ℓ P).1.length ≤ regenerationTimes ℓ P.1 n ∨
      (firstPairWord ℓ P).1.length < n :=
  ⟨(firstPairWord ℓ P).1.length+1,Or.inr (Nat.lt_succ_self _)⟩

open scoped Classical in
noncomputable def singleCommonIndex {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) : ℕ :=
  Nat.find (singleCommonIndex_exists_bound ℓ P)

lemma measurable_singleCommonIndex {d : ℕ} (ℓ : Vector d) : Measurable (singleCommonIndex ℓ (d := d)) := by
  classical
  have hlen : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).1.length) :=
    (measurable_of_countable (fun wv : List (Direction d) × List (Direction d) => wv.1.length)).comp
      (measurable_firstPairWord ℓ)
  apply measurable_find
  intro n
  exact (measurableSet_le hlen ((measurable_regenerationTime ℓ n).comp measurable_fst)).union
    (measurableSet_lt hlen measurable_const)

lemma singleCommonIndex_time {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    regenerationTimes ℓ P.1 (singleCommonIndex ℓ P) = (firstPairWord ℓ P).1.length := by
  have hmono := regenerationTimes_strictMono ℓ P.1 hX
  obtain ⟨n,hn⟩ := trueRecord_eq_regenerationTime ℓ P.1 h0 hX hP.2.2.2.2.1.1
  have hN : singleCommonIndex ℓ P ≤ n := Nat.find_min' _ (Or.inl hn.ge)
  apply le_antisymm ((hmono.monotone hN).trans hn.le)
  rcases Nat.find_spec (singleCommonIndex_exists_bound ℓ P) with h | h
  · exact h
  · exact h.le.trans hmono.le_apply

lemma singleCommonIndex_le_width {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    singleCommonIndex ℓ P ≤ commonWordWidth ℓ (firstPairWord ℓ P) := by
  have hs := recordCount_regenerationTimes ℓ P.1 h0 hX (singleCommonIndex ℓ P)
  rw [singleCommonIndex_time ℓ P h0 hX hP,
    recordCount_congr_prefix ℓ hP.2.1.1] at hs
  calc
    singleCommonIndex ℓ P = ∑ _i ∈ Finset.range (singleCommonIndex ℓ P), 1 := by simp
    _ ≤ ∑ i ∈ Finset.range (singleCommonIndex ℓ P), wordRecordCount ℓ (regenerationWords ℓ P.1 i) := by
      exact Finset.sum_le_sum fun i _ => wordRecordCount_positive ℓ _
        (regeneration_word_admissible ℓ P.1 hX i)
    _ = _ := hs.symm

lemma commonWordRadius_le_single_sum {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) :
    wordRadius (firstPairWord ℓ P).1 ≤
      ∑ i ∈ Finset.range (singleCommonIndex ℓ P), wordRadius (regenerationWords ℓ P.1 i) := by
  obtain ⟨j,hj,he⟩ := wordRadius_attained (firstPairWord ℓ P).1
  rw [he,← hP.2.1.1 j hj]
  apply regeneration_prefix_radius ℓ P.1 h0 hX
  rwa [singleCommonIndex_time ℓ P h0 hX hP]

lemma finite_prefix_sum_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) {j k : ℕ} (hk : k ≤ j) :
    (∑ i : Fin j, if (i : ℕ) < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) j]
  calc
    _ = ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i _ hi
      simp only [Finset.mem_range] at hi
      exact ite_eq_right hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ite_eq_left (Finset.mem_range.mp hi)

def NoCommonInPrefix {d : ℕ} (ℓ : Vector d) {j : ℕ}
    (w : Fin j → List (Direction d)) (Y : Path d) : Prop :=
  ∀ k : Fin j, ¬ ∃ m, TrueRecord ℓ Y m ∧
    dot (realPosition (Y m)) ℓ = ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (w i) else 0

lemma measurableSet_noCommonInPrefix {d : ℕ} (ℓ : Vector d) (j : ℕ) :
    MeasurableSet {p : (Fin j → List (Direction d)) × Path d | NoCommonInPrefix ℓ p.1 p.2} := by
  simp only [NoCommonInPrefix, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  change MeasurableSet ({x : (Fin j → List (Direction d)) × Path d | ∃ m,
    TrueRecord ℓ x.2 m ∧ dot (realPosition (x.2 m)) ℓ =
      ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (x.1 i) else 0}ᶜ)
  apply MeasurableSet.compl
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro m
  apply ((measurableSet_trueRecord ℓ m).preimage measurable_snd).inter
  apply measurableSet_eq_fun
  · exact (measurable_of_countable (fun z : Lattice d => dot (realPosition z) ℓ)).comp
      ((measurable_pi_apply m).comp measurable_snd)
  · exact ((measurable_of_countable (fun w : Fin j → List (Direction d) =>
      ∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (w i) else 0)).comp measurable_fst)

lemma singleCommonIndex_gt_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n))
    (hP : P ∈ FirstPairWordEvent ℓ (firstPairWord ℓ P)) (j : ℕ) :
    j < singleCommonIndex ℓ P ↔
      NoCommonInPrefix ℓ (fun k : Fin j => regenerationWords ℓ P.1 k) P.2 := by
  have htime := singleCommonIndex_time ℓ P h0 hX hP
  have hmono := regenerationTimes_strictMono ℓ P.1 hX
  have hfirst := hP.2.2
  change FirstCommonTrueRecord ℓ P (firstPairWord ℓ P).1.length (firstPairWord ℓ P).2.length at hfirst
  have hlevel (k : Fin j) :
      (∑ i : Fin j, if (i : ℕ) < k+1 then wordHeightGain ℓ (regenerationWords ℓ P.1 i) else 0) =
        dot (realPosition (P.1 (regenerationTimes ℓ P.1 (k+1)))) ℓ := by
    rw [finite_prefix_sum_eq (fun n => wordHeightGain ℓ (regenerationWords ℓ P.1 n))
      (j := j) (k := (k : ℕ)+1) (by omega)]
    exact (regeneration_height_sum ℓ P.1 h0 hX (k+1)).symm
  constructor
  · intro hj k hk
    obtain ⟨m,hm,he⟩ := hk
    rw [hlevel] at he
    have hkpos : 0 < regenerationTimes ℓ P.1 (k+1) := by
      simpa only [regenerationTimes_zero] using hmono (show 0 < (k : ℕ)+1 by omega)
    have hkn : regenerationTimes ℓ P.1 (k+1) < (firstPairWord ℓ P).1.length := by
      rw [← htime]
      exact hmono (by omega)
    have hc : CommonTrueRecord ℓ P (regenerationTimes ℓ P.1 (k+1)) m :=
      ⟨regenerationTimes_true ℓ P.1 h0 hX _,hm,he.symm⟩
    have hmpos : 0 < m := by
      by_contra hm0
      have hm0 : m = 0 := by omega
      have hh := hc.1.1 0 hkpos
      rw [h0,he.symm,hm0,h0'] at hh
      exact (lt_irrefl _ hh)
    exact hfirst.2.2.2 _ _ hkpos hkn hmpos
      ((commonTrueRecord_time_order ℓ P hc hfirst.2.2.1).mp hkn) hc
  · intro hno
    by_contra hj
    have hNj : singleCommonIndex ℓ P ≤ j := by omega
    have hNpos : 0 < singleCommonIndex ℓ P := by
      by_contra hn
      have hn : singleCommonIndex ℓ P = 0 := by omega
      rw [hn,regenerationTimes_zero] at htime
      have := hfirst.1
      omega
    let k : Fin j := ⟨singleCommonIndex ℓ P-1,by omega⟩
    apply hno k
    refine ⟨(firstPairWord ℓ P).2.length,hfirst.2.2.1.2.1,?_⟩
    rw [hlevel,show (k : ℕ)+1 = singleCommonIndex ℓ P by dsimp only [k]; omega,htime]
    exact hfirst.2.2.1.2.2.symm

lemma indepFun_past_product {Ω Ω' α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → α) (g : Ω → β) (hf : Measurable f) (hg : Measurable g)
    (hi : IndepFun f g μ) :
    IndepFun (fun p : Ω × Ω' => f p.1) (fun p : Ω × Ω' => (g p.1,p.2)) (μ.prod ν) := by
  have hp : MeasurePreserving (fun x => (f x,g x)) μ ((μ.map f).prod (μ.map g)) :=
    ⟨hf.prodMk hg, hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have ht := (measurePreserving_prodAssoc (μ.map f) (μ.map g) ν).comp
    (hp.prod (MeasurePreserving.id ν))
  apply indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop) |>.mpr
  have hleft : (μ.prod ν).map (fun p => f p.1) = μ.map f := by
    rw [← Function.comp_def, ← Measure.map_map hf measurable_fst, Measure.map_fst_prod,
      measure_univ,one_smul]
  have hright : (μ.prod ν).map (fun p => (g p.1,p.2)) = (μ.map g).prod ν := by
    have h := Measure.map_prod_map μ ν hg (measurable_id : Measurable (id : Ω' → Ω'))
    rw [Measure.map_id] at h
    exact h.symm
  rw [hleft,hright]
  exact ht.map_eq

lemma tsum_nat_lt_ennreal (f : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑' i, if i < n then f i else 0) = ∑ i ∈ Finset.range n, f i := by
  classical
  rw [tsum_eq_sum (s := Finset.range n) (fun i hi => by
    have hi' : ¬ i < n := by simpa using hi
    simp only [ite_eq_right hi'])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ite_eq_left (Finset.mem_range.mp hi)]

lemma lintegral_stopped_iid_sum {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hid : ∀ i, IdentDistrib (W i) (W 0) μ μ) (N : Ω → ℕ) (hN : Measurable N)
    (hind : ∀ i, IndepFun (W i) (fun x => if i < N x then (1 : ℝ≥0∞) else 0) μ)
    (F : β → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∑ i ∈ Finset.range (N x), F (W i x) ∂μ) =
      (∫⁻ x, (N x : ℝ≥0∞) ∂μ) * (∫⁻ x, F (W 0 x) ∂μ) := by
  classical
  let E := fun i x => if i < N x then (1 : ℝ≥0∞) else 0
  have hE (i : ℕ) : Measurable (E i) := measurable_const.ite
    (measurableSet_lt measurable_const hN) measurable_const
  have he (x : Ω) : (∑ i ∈ Finset.range (N x), F (W i x)) =
      ∑' i, E i x * F (W i x) := by
    simp only [E,ite_mul,one_mul,zero_mul,tsum_nat_lt_ennreal]
  have hn (x : Ω) : (∑' i, E i x) = (N x : ℝ≥0∞) := by
    simp only [E,tsum_nat_lt_ennreal,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  simp_rw [he]
  rw [lintegral_tsum (f := fun i x => E i x * F (W i x))
    (fun i => ((hE i).mul (hF.comp (hW i))).aemeasurable)]
  have hf (i : ℕ) : (∫⁻ x, E i x * F (W i x) ∂μ) =
      (∫⁻ x, E i x ∂μ) * (∫⁻ x, F (W 0 x) ∂μ) := by
    calc
      _ = (∫⁻ x, E i x ∂μ) * (∫⁻ x, F (W i x) ∂μ) := by
        simpa only [Pi.mul_apply, Function.comp_apply] using
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hE i)
            (hF.comp (hW i)) ((hind i).symm.comp measurable_id hF)
      _ = _ := congrArg (fun a => (∫⁻ x, E i x ∂μ) * a) ((hid i).comp hF).lintegral_eq
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right,← lintegral_tsum (fun i => (hE i).aemeasurable)]
  simp_rw [hn]

lemma independent_conditioned_singleCommonIndex_indep {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (j : ℕ) :
    IndepFun (fun P : Path d × Path d => regenerationWords ℓ P.1 j)
      (fun P => if j < singleCommonIndex ℓ P then (1 : ℝ≥0∞) else 0)
      (independentConditionedPairLaw ν ℓ) := by
  classical
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := inferInstanceAs (IsProbabilityMeasure μ)
  have hpast := (independent_past_current μ (fun n X => regenerationWords ℓ X n)
    (measurable_regenerationWord ℓ) (regenerationWords_independent ν ℓ htrans) j).symm
  have hpi : Measurable (fun X : Path d => fun k : Fin j => regenerationWords ℓ X k) := by
    exact Measurable.of_eval (fun k => measurable_regenerationWord ℓ k)
  have hind := indepFun_past_product μ μ (fun X => regenerationWords ℓ X j)
    (fun X => fun k : Fin j => regenerationWords ℓ X k) (measurable_regenerationWord ℓ j) hpi hpast
  let E := fun p : (Fin j → List (Direction d)) × Path d =>
    if NoCommonInPrefix ℓ p.1 p.2 then (1 : ℝ≥0∞) else 0
  have hE : Measurable E := measurable_const.ite (measurableSet_noCommonInPrefix ℓ j) measurable_const
  have hi := hind.comp measurable_id hE
  apply hi.congr ae_eq_rfl
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  change E ((fun k : Fin j => regenerationWords ℓ P.1 k),P.2) = _
  dsimp only [E]
  rw [← singleCommonIndex_gt_iff ℓ P h0.1 h0.2 hX (hP 0) j]
  by_cases hh : j < singleCommonIndex ℓ P <;> simp only [hh,ite_true,ite_false]

lemma independent_singleCommonIndex_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => (singleCommonIndex ℓ P : ℝ)) (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  apply (independent_commonWordWidth_integrable ν ℓ htrans height hproj hstep).1.mono'
    (((measurable_of_countable ((↑) : ℕ → ℝ)).comp (measurable_singleCommonIndex ℓ)).aestronglyMeasurable)
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, P.1 0 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  change ‖(singleCommonIndex ℓ P : ℝ)‖ ≤ _
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast singleCommonIndex_le_width ℓ P h0 hX (hP 0)

lemma identDistrib_fst {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → β) (hf : Measurable f)
    (hg : Measurable g) (hid : IdentDistrib f g μ μ) :
    IdentDistrib (fun p : Ω × Ω => f p.1) (fun p : Ω × Ω => g p.1) (μ.prod μ) (μ.prod μ) := by
  refine ⟨(hf.comp measurable_fst).aemeasurable,(hg.comp measurable_fst).aemeasurable,?_⟩
  rw [show (fun p : Ω × Ω => f p.1) = f ∘ Prod.fst from rfl,
    show (fun p : Ω × Ω => g p.1) = g ∘ Prod.fst from rfl,
    ← Measure.map_map hf measurable_fst,← Measure.map_map hg measurable_fst,
    Measure.map_fst_prod,measure_univ,one_smul]
  exact hid.map_eq

lemma independent_commonWordRadius_fst_integrable {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    Integrable (fun P => wordRadius (firstPairWord ℓ P).1) (independentConditionedPairLaw ν ℓ) := by
  classical
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := inferInstanceAs (IsProbabilityMeasure μ)
  have hW (i : ℕ) : Measurable (fun P : Path d × Path d => regenerationWords ℓ P.1 i) :=
    (measurable_regenerationWord ℓ i).comp measurable_fst
  have hid (i : ℕ) : IdentDistrib (fun P : Path d × Path d => regenerationWords ℓ P.1 i)
      (fun P => regenerationWords ℓ P.1 0) (independentConditionedPairLaw ν ℓ)
      (independentConditionedPairLaw ν ℓ) :=
    identDistrib_fst μ (fun X => regenerationWords ℓ X i) (firstWord ℓ)
      (measurable_regenerationWord ℓ i) (measurable_firstWord ℓ)
      (regenerationWords_identDistrib ν ℓ htrans i)
  have hwal := lintegral_stopped_iid_sum (independentConditionedPairLaw ν ℓ)
    (fun i P => regenerationWords ℓ P.1 i) hW hid (singleCommonIndex ℓ)
    (measurable_singleCommonIndex ℓ)
    (independent_conditioned_singleCommonIndex_indep ν ℓ htrans height hproj hstep)
    (fun w => ENNReal.ofReal (wordRadius w)) (measurable_of_countable _)
  have hNi := independent_singleCommonIndex_integrable ν ℓ htrans height hproj hstep
  have hRi := (measurePreserving_fst (μ := μ) (ν := μ)).integrable_comp_of_integrable
    (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans)
  have hNfin : (∫⁻ P, (singleCommonIndex ℓ P : ℝ≥0∞) ∂independentConditionedPairLaw ν ℓ) < ∞ := by
    have hh := hNi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hh
    · simpa using hh
    · exact Filter.Eventually.of_forall fun P => Nat.cast_nonneg _
  have hRfin : (∫⁻ P, ENNReal.ofReal (wordRadius (regenerationWords ℓ P.1 0))
      ∂independentConditionedPairLaw ν ℓ) < ∞ := by
    have hh := hRi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal] at hh
    · exact hh
    · exact Filter.Eventually.of_forall fun P => wordRadius_nonneg _
  refine ⟨((measurable_of_countable (fun wv : List (Direction d) × List (Direction d) =>
    wordRadius wv.1)).comp (measurable_firstPairWord ℓ)).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun P => wordRadius_nonneg _)]
  apply lt_of_le_of_lt _ (ENNReal.mul_lt_top hNfin hRfin)
  rw [← hwal]
  apply lintegral_mono_ae
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, P.1 0 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))
  have hX : ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ n,
      ((renewSuffix ℓ)^[n] P.1) ∈ FirstWordEvent ℓ (regenerationWords ℓ P.1 n) :=
    Measure.quasiMeasurePreserving_fst.ae (conditioned_all_firstWords ν ℓ htrans)
  have hP := independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep
  filter_upwards [h0,hX,hP] with P h0 hX hP
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => wordRadius_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (commonWordRadius_le_single_sum ℓ P h0 hX (hP 0))

end DirectionalTransience
end
end

end OAI
