import Mathlib
import OAI.Probability.Ballisticity.Geometry.WordCoordinate

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma conditioned_word_spatial_strong_laws {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    ∀ᵐ X ∂conditionedLaw ν ℓ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, wordCoordinate e (regenerationWords ℓ X i))/n)
        atTop (𝓝 (∫ Y, wordCoordinate e (firstWord ℓ Y) ∂conditionedLaw ν ℓ)) ∧
      Tendsto (fun n : ℕ => wordRadius (regenerationWords ℓ X n)/n) atTop (𝓝 0) := by
  have hi := regenerationWords_independent ν ℓ htrans
  have hd := regenerationWords_identDistrib ν ℓ htrans
  have hmc : Measurable (wordCoordinate e) := measurable_of_countable _
  have hc := strong_law_ae_real (fun n X => wordCoordinate e (regenerationWords ℓ X n))
    (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans e)
    (fun i j hij => (hi.indepFun hij).comp hmc hmc) (fun i => (hd i).comp hmc)
  have hr := strong_law_ae_real (fun n X => wordRadius (regenerationWords ℓ X n))
    (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans)
    (fun i j hij => (hi.indepFun hij).comp measurable_wordRadius measurable_wordRadius)
    (fun i => (hd i).comp measurable_wordRadius)
  filter_upwards [hc,hr] with X hX hR
  exact ⟨hX, increment_sublinear_of_average _ _ hR⟩

lemma increasing_cuts_index_tendsto (T K : ℕ → ℕ) (hT : StrictMono T)
    (hK : ∀ n, T (K n) ≤ n ∧ n < T (K n+1)) : Tendsto K atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (T M)] with n hn
  by_contra hm
  have hh := hT.monotone (show K n+1 ≤ M by omega)
  exact (not_lt_of_ge (hh.trans hn)) (hK n).2

lemma scalar_cut_interpolation (T : ℕ → ℕ) (hT : StrictMono T) (hT0 : T 0 = 0)
    (Y f R : ℕ → ℝ) (m : ℝ) (hm : 0 < m)
    (hY : ∀ n, Y (T n) = ∑ i ∈ Finset.range n, f i)
    (herr : ∀ k n, T k ≤ n → n < T (k+1) → |Y n-Y (T k)| ≤ R k)
    (hf : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i)/n) atTop (𝓝 m))
    (hR : Tendsto (fun n : ℕ => R n/n) atTop (𝓝 0)) : Tendsto Y atTop atTop := by
  choose K hK using increasing_cuts_cover T hT hT0
  have hKt := increasing_cuts_index_tendsto T K hT hK
  have hh := (hf.sub hR).comp hKt
  simp only [sub_zero] at hh
  have hmul := hh.pos_mul_atTop hm (tendsto_natCast_atTop_atTop.comp hKt)
  apply tendsto_atTop_mono' _ _ hmul
  filter_upwards [hKt.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  have hk : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have he := neg_le_of_abs_le (herr (K n) n (hK n).1 (hK n).2)
  simp only [Function.comp_apply, sub_mul, div_mul_cancel₀ _ hk]
  rw [← hY]
  linarith only [he]

lemma regeneration_coordinate_sum {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (X : Path d) (hX : X ∈ RegenerationSupport ℓ) (n : ℕ) :
    signedCoordinate e (X (regenerationTimes ℓ X n)) =
      ∑ i ∈ Finset.range n, wordCoordinate e (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [hX.1, signedCoordinate]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X hX.1 hX.2 n _ (by rfl),
      signedCoordinate_add, ih, Finset.sum_range_succ, wordCoordinate]

lemma conditioned_coordinate_transience {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto (fun n => signedCoordinate e (X n)) atTop atTop := by
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans,
    conditioned_word_spatial_strong_laws ν hue ℓ hℓ htrans e] with X hX hlim
  apply scalar_cut_interpolation (regenerationTimes ℓ X)
    (regenerationTimes_strictMono ℓ X hX.2) (regenerationTimes_zero ℓ X)
    (fun n => signedCoordinate e (X n)) (fun n => wordCoordinate e (regenerationWords ℓ X n))
    (fun n => wordRadius (regenerationWords ℓ X n)) _ he
    (regeneration_coordinate_sum ℓ e X hX) _ hlim.1 hlim.2
  intro k n hlo hhi
  have hnk : n = regenerationTimes ℓ X k+(n-regenerationTimes ℓ X k) := by omega
  have hlen : n-regenerationTimes ℓ X k ≤ (regenerationWords ℓ X k).length := by
    rw [regenerationTimes_succ] at hhi
    omega
  have hh := regeneration_span ℓ X hX.1 hX.2 k _ hlen
  rw [← hnk] at hh
  rw [hh, signedCoordinate_add, add_sub_cancel_left]
  exact (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ hlen)

lemma conditioned_to_annealed_transience {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ u : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (hu : ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ TransientPaths u) : DirectionallyTransient ν u := by
  let B := NoDrop ℓ 0 ∩ (TransientPaths u)ᶜ
  have hB : MeasurableSet B := (measurableSet_noDrop ℓ 0).inter (measurableSet_transientPaths u).compl
  have hBD : B ⊆ NoDrop ℓ 0 := Set.inter_subset_left
  have hcB : conditionedLaw ν ℓ B = 0 :=
    measure_mono_null Set.inter_subset_right (ae_iff.mp hu)
  have haB : annealedLaw ν B = 0 := by
    rw [conditionedLaw_apply_of_subset ν ℓ B hB hBD] at hcB
    exact (mul_eq_zero.mp hcB).resolve_left (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  have hwords : ∀ᵐ X ∂annealedLaw ν, ∀ w : List (Direction d),
      (∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
        dot (realPosition (wordPath 0 w w.length)) ℓ) →
      X ∈ wordCylinder 0 w →
      (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ B := by
    apply ae_all_iff.mpr
    intro w
    by_cases hw : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ
    · have hz := annealed_record_suffix ν ℓ w hw B hB hBD
      rw [haB, mul_zero] at hz
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with X hX _ hcy
      exact fun hh => hX ⟨hh,hcy⟩
    · exact Filter.Eventually.of_forall fun _ h _ => (hw h).elim
  filter_upwards [annealed_initial ν, annealed_nearest_neighbor ν,
    annealed_trueRecords_unbounded ν ℓ htrans, hwords] with X h0 hnn hrec hwords
  obtain ⟨n,_,hn⟩ := hrec 0
  obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hnn n
  rw [h0] at hcy
  have hwend : wordPath 0 w w.length = X n := by rw [← hw]; exact (hcy _ le_rfl).symm
  have hwrec : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    rw [← hcy j hj.le, hwend]
    exact hn.1 j (by omega)
  have hnot := hwords w hwrec hcy
  have hD : (fun j => X (w.length+j)-wordPath 0 w w.length) ∈ NoDrop ℓ 0 := by
    intro j
    rw [hwend, hw, dot_realPosition_sub]
    have hh := hn.2 j
    simpa only [dot, realPosition, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
      sub_nonneg] using hh
  have ht : (fun j => X (n+j)-X n) ∈ TransientPaths u := by
    by_contra hh
    apply hnot
    refine ⟨hD, ?_⟩
    change (fun j => X (w.length+j)-wordPath 0 w w.length) ∉ TransientPaths u
    rw [hwend, hw]
    exact hh
  have hraw : (fun j => X (n+j)) ∈ TransientPaths u := by
    change (fun j => X (n+j)) ∈ (fun Z : Path d => fun j => Z j-X n) ⁻¹' TransientPaths u at ht
    rwa [transientPaths_translation] at ht
  change Tendsto (fun j => dot (realPosition (X j)) u) atTop atTop
  change Tendsto (fun j => dot (realPosition (X (n+j))) u) atTop atTop at hraw
  exact (tendsto_add_atTop_iff_nat n).mp (by simpa only [Nat.add_comm] using hraw)

lemma dot_comm {d : ℕ} (v w : Vector d) : dot v w = dot w v := by
  simp only [dot, mul_comm]

lemma dot_signed_direction {d : ℕ} (e : Direction d) (x : Lattice d) :
    dot (realPosition x) (realPosition (step e)) = signedCoordinate e x := by
  rw [dot_comm, dot_step]
  rfl

lemma signed_direction_unit {d : ℕ} (e : Direction d) :
    dot (realPosition (step e)) (realPosition (step e)) = 1 := by
  rw [dot_step]
  simp only [realPosition,step,ite_true,Int.cast_ite,Int.cast_one,Int.cast_neg]
  cases e.2 <;> norm_num

lemma exists_transient_signed_coordinate {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) : ∃ e : Direction d,
      DirectionallyTransient ν (realPosition (step e)) := by
  obtain ⟨e,he⟩ := conditioned_coordinate_positive_mean ν hue ℓ hℓ htrans
  refine ⟨e, conditioned_to_annealed_transience ν ℓ (realPosition (step e)) htrans ?_⟩
  have hh := conditioned_coordinate_transience ν hue ℓ hℓ htrans e he
  simpa only [TransientPaths, Set.mem_ofPred_eq, dot_signed_direction] using hh

noncomputable def fixedQuenchedKernel {d : ℕ} (x : Lattice d) :
    Kernel (Environment d) (Path d) :=
  quenchedKernel.comap (fun ω => (ω,x)) (measurable_id.prodMk measurable_const)

instance fixedQuenchedKernel_markov {d : ℕ} (x : Lattice d) :
    IsMarkovKernel (fixedQuenchedKernel x) := by unfold fixedQuenchedKernel; infer_instance

noncomputable def sharedPairKernel {d : ℕ} (x y : Lattice d) :
    Kernel (Environment d) (Path d × Path d) :=
  (fixedQuenchedKernel x).prod (fixedQuenchedKernel y)

instance sharedPairKernel_markov {d : ℕ} (x y : Lattice d) :
    IsMarkovKernel (sharedPairKernel x y) := by unfold sharedPairKernel; infer_instance

noncomputable def sharedPairLaw {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d) :
    Measure (Path d × Path d) := sharedPairKernel x y ∘ₘ environmentLaw ν

instance sharedPairLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) : IsProbabilityMeasure (sharedPairLaw ν x y) := by
  unfold sharedPairLaw
  infer_instance

noncomputable def sharedNoDropMass {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : ℝ≥0∞ :=
  ∫⁻ ω, noDropQuenched ℓ x ω * noDropQuenched ℓ y ω ∂environmentLaw ν

lemma sharedPairLaw_rectangle {d : ℕ} (ν : Measure (Row d)) (x y : Lattice d)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    sharedPairLaw ν x y (A ×ˢ B) =
      ∫⁻ ω, quenchedKernel (ω,x) A * quenchedKernel (ω,y) B ∂environmentLaw ν := by
  rw [sharedPairLaw, Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro ω
  rw [sharedPairKernel, Kernel.prod_apply, Measure.prod_prod]
  rfl

lemma sharedNoDropMass_eq {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) (x y : Lattice d) :
    sharedNoDropMass ν ℓ x y = sharedPairLaw ν x y (NoDrop ℓ x ×ˢ NoDrop ℓ y) :=
  (sharedPairLaw_rectangle ν x y _ _ (measurableSet_noDrop ℓ x) (measurableSet_noDrop ℓ y)).symm

lemma sharedNoDropMass_le_one {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) : sharedNoDropMass ν ℓ x y ≤ 1 := by
  rw [sharedNoDropMass_eq]
  exact prob_le_one

lemma sharedNoDropMass_uniform_positive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ x y : Lattice d, c ≤ sharedNoDropMass ν ℓ x y := by
  obtain ⟨s,hs,_,hsmall⟩ := positive_random_small_set (environmentLaw ν) (noDropQuenched ℓ 0)
    (measurable_noDropQuenched ℓ 0)
    ((quenched_noDrop_positive_of_directionallyTransient ν hue ℓ hℓ htrans).mono fun _ h => h 0)
  refine ⟨(s : ℝ≥0∞)^2 / 2, ENNReal.div_pos (pow_ne_zero _ (by exact_mod_cast hs.ne')) (by norm_num), ?_⟩
  intro x y
  let μ := environmentLaw ν
  let A := {ω | noDropQuenched ℓ x ω ≤ 2*(s : ℝ≥0∞)}
  let B := {ω | noDropQuenched ℓ y ω ≤ 2*(s : ℝ≥0∞)}
  have hA : MeasurableSet A := measurableSet_le (measurable_noDropQuenched ℓ x) measurable_const
  have hB : MeasurableSet B := measurableSet_le (measurable_noDropQuenched ℓ y) measurable_const
  have hsa : μ A < 1/4 := by
    rw [show μ A = environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2*(s : ℝ≥0∞)} from
      noDropQuenched_small_translation ν ℓ x _]
    exact hsmall
  have hsb : μ B < 1/4 := by
    rw [show μ B = environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2*(s : ℝ≥0∞)} from
      noDropQuenched_small_translation ν ℓ y _]
    exact hsmall
  have hsa' : μ.real A < 1/4 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ A) (by norm_num)).mpr hsa
    norm_num at hh
    exact hh
  have hsb' : μ.real B < 1/4 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ B) (by norm_num)).mpr hsb
    norm_num at hh
    exact hh
  have hgood : (1 : ℝ≥0∞)/2 ≤ μ (A ∪ B)ᶜ := by
    apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top μ _)).mp
    change ((1 : ℝ≥0∞)/2).toReal ≤ μ.real (A ∪ B)ᶜ
    rw [probReal_compl_eq_one_sub (hA.union hB)]
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    linarith only [measureReal_union_le (μ := μ) A B, hsa', hsb']
  have hsub : (A ∪ B)ᶜ ⊆ {ω | (s : ℝ≥0∞)^2 ≤
      noDropQuenched ℓ x ω * noDropQuenched ℓ y ω} := by
    intro ω hω
    have hx : ¬noDropQuenched ℓ x ω ≤ 2*(s : ℝ≥0∞) := fun h => hω (Or.inl h)
    have hy : ¬noDropQuenched ℓ y ω ≤ 2*(s : ℝ≥0∞) := fun h => hω (Or.inr h)
    have hs2 : (s : ℝ≥0∞) ≤ 2*(s : ℝ≥0∞) := by
      simpa only [one_mul] using mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) (s : ℝ≥0∞)
    rw [pow_two]
    exact mul_le_mul' (hs2.trans (le_of_not_ge hx)) (hs2.trans (le_of_not_ge hy))
  calc
    (s : ℝ≥0∞)^2/2 = (s : ℝ≥0∞)^2 * (1/2) := by rw [div_eq_mul_inv, one_div]
    _ ≤ (s : ℝ≥0∞)^2 * μ {ω | (s : ℝ≥0∞)^2 ≤
          noDropQuenched ℓ x ω * noDropQuenched ℓ y ω} :=
      mul_le_mul_right (hgood.trans (measure_mono hsub)) _
    _ ≤ sharedNoDropMass ν ℓ x y :=
      mul_meas_ge_le_lintegral₀
        ((measurable_noDropQuenched ℓ x).mul (measurable_noDropQuenched ℓ y)).aemeasurable _

noncomputable def sharedConditionedPairLaw {d : ℕ} (ν : Measure (Row d))
    (ℓ : Vector d) (x y : Lattice d) : Measure (Path d × Path d) :=
  (sharedNoDropMass ν ℓ x y)⁻¹ •
    (sharedPairLaw ν x y).restrict (NoDrop ℓ x ×ˢ NoDrop ℓ y)

lemma sharedConditionedPairLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (hp : sharedNoDropMass ν ℓ x y ≠ 0) :
    IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ x y) := by
  constructor
  simp only [sharedConditionedPairLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, ← sharedNoDropMass_eq]
  exact ENNReal.inv_mul_cancel hp (ne_of_lt ((sharedNoDropMass_le_one ν ℓ x y).trans_lt (by simp)))

noncomputable def annealedFrom {d : ℕ} (ν : Measure (Row d)) (x : Lattice d) :
    Measure (Path d) := fixedQuenchedKernel x ∘ₘ environmentLaw ν

instance annealedFrom_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x : Lattice d) : IsProbabilityMeasure (annealedFrom ν x) := by
  unfold annealedFrom
  infer_instance

lemma annealedFrom_apply {d : ℕ} (ν : Measure (Row d)) (x : Lattice d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    annealedFrom ν x A = ∫⁻ ω, quenchedKernel (ω,x) A ∂environmentLaw ν := by
  rw [annealedFrom, Measure.bind_apply hA (Kernel.aemeasurable _)]
  rfl

lemma annealedFrom_noDrop {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) :
    annealedFrom ν x (NoDrop ℓ x) = annealedLaw ν (NoDrop ℓ 0) := by
  rw [annealedFrom_apply ν x _ (measurableSet_noDrop ℓ x)]
  exact annealed_noDrop_translation ν ℓ x

noncomputable def conditionedFrom {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x : Lattice d) : Measure (Path d) :=
  (annealedLaw ν (NoDrop ℓ 0))⁻¹ • (annealedFrom ν x).restrict (NoDrop ℓ x)

lemma conditionedFrom_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (conditionedFrom ν ℓ x) := by
  constructor
  simp only [conditionedFrom, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, annealedFrom_noDrop]
  exact ENNReal.inv_mul_cancel hp (measure_ne_top _ _)

lemma sharedConditionedPairLaw_fst_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    sharedConditionedPairLaw ν ℓ x y (Prod.fst ⁻¹' A) ≤
      (sharedNoDropMass ν ℓ x y)⁻¹ * annealedLaw ν (NoDrop ℓ 0) *
        conditionedFrom ν ℓ x A := by
  rw [sharedConditionedPairLaw, Measure.smul_apply,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' A ∩ (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      (A ∩ NoDrop ℓ x) ×ˢ NoDrop ℓ y := by
    ext z
    exact and_assoc.symm
  rw [he, sharedPairLaw_rectangle ν x y _ _ (hA.inter (measurableSet_noDrop ℓ x))
    (measurableSet_noDrop ℓ y)]
  simp only [smul_eq_mul, conditionedFrom, Measure.smul_apply,
    Measure.restrict_apply hA]
  rw [← mul_assoc, mul_assoc _ (annealedLaw ν (NoDrop ℓ 0)),
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _), mul_one]
  apply mul_le_mul_right
  rw [annealedFrom_apply ν x _ (hA.inter (measurableSet_noDrop ℓ x))]
  exact lintegral_mono fun ω => mul_le_of_le_one_right' prob_le_one

lemma sharedConditionedPairLaw_snd_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (A : Set (Path d)) (hA : MeasurableSet A)
    (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    sharedConditionedPairLaw ν ℓ x y (Prod.snd ⁻¹' A) ≤
      (sharedNoDropMass ν ℓ x y)⁻¹ * annealedLaw ν (NoDrop ℓ 0) *
        conditionedFrom ν ℓ y A := by
  rw [sharedConditionedPairLaw, Measure.smul_apply,
    Measure.restrict_apply (hA.preimage measurable_snd)]
  have he : Prod.snd ⁻¹' A ∩ (NoDrop ℓ x ×ˢ NoDrop ℓ y) =
      NoDrop ℓ x ×ˢ (A ∩ NoDrop ℓ y) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  rw [he, sharedPairLaw_rectangle ν x y _ _ (measurableSet_noDrop ℓ x)
    (hA.inter (measurableSet_noDrop ℓ y))]
  simp only [smul_eq_mul, conditionedFrom, Measure.smul_apply,
    Measure.restrict_apply hA]
  rw [← mul_assoc, mul_assoc _ (annealedLaw ν (NoDrop ℓ 0)),
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _), mul_one]
  apply mul_le_mul_right
  rw [annealedFrom_apply ν y _ (hA.inter (measurableSet_noDrop ℓ y))]
  exact lintegral_mono fun ω => mul_le_of_le_one_left' prob_le_one

lemma shared_pair_word_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) (w v : List (Direction d)) (T : Set (Lattice d))
    (hx : wordPath x w w.length ∈ T) (hy : wordPath y v v.length ∈ T)
    (hdis : Disjoint ((wordDepartures x w : Set (Lattice d)) ∪ wordDepartures y v) T)
    (A B : Set (Path d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAT : A ⊆ Stay T) (hBT : B ⊆ Stay T) :
    sharedPairLaw ν x y
      (((fun X : Path d => fun j => X (w.length+j)) ⁻¹' A ∩ wordCylinder x w) ×ˢ
       ((fun X : Path d => fun j => X (v.length+j)) ⁻¹' B ∩ wordCylinder y v)) =
      sharedPairLaw ν x y (wordCylinder x w ×ˢ wordCylinder y v) *
        sharedPairLaw ν (wordPath x w w.length) (wordPath y v v.length) (A ×ˢ B) := by
  let S : Set (Lattice d) := (wordDepartures x w : Set (Lattice d)) ∪ wordDepartures y v
  have hmA : MeasurableSet ((fun X : Path d => fun j => X (w.length+j)) ⁻¹' A ∩
      wordCylinder x w) := (hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder x w)
  have hmB : MeasurableSet ((fun X : Path d => fun j => X (v.length+j)) ⁻¹' B ∩
      wordCylinder y v) := (hB.preimage (by fun_prop)).inter (measurableSet_wordCylinder y v)
  have hw (ω : Environment d) : quenchedKernel (ω,x)
      ((fun X : Path d => fun j => X (w.length+j)) ⁻¹' A ∩ wordCylinder x w) =
      ENNReal.ofReal (wordWeight ω x w) * quenchedKernel (ω, wordPath x w w.length) A := by
    rw [show wordCylinder x w = pathCylinder (wordPath x w) w.length from rfl,
      quenched_prefix_future ω x (wordPath x w) (wordPath_zero x w) w.length hA]
    rw [show pathCylinder (wordPath x w) w.length = wordCylinder x w from rfl,
      quenched_wordCylinder]
  have hv (ω : Environment d) : quenchedKernel (ω,y)
      ((fun X : Path d => fun j => X (v.length+j)) ⁻¹' B ∩ wordCylinder y v) =
      ENNReal.ofReal (wordWeight ω y v) * quenchedKernel (ω, wordPath y v v.length) B := by
    rw [show wordCylinder y v = pathCylinder (wordPath y v) v.length from rfl,
      quenched_prefix_future ω y (wordPath y v) (wordPath_zero y v) v.length hB]
    rw [show pathCylinder (wordPath y v) v.length = wordCylinder y v from rfl,
      quenched_wordCylinder]
  rw [sharedPairLaw_rectangle ν x y _ _ hmA hmB]
  simp_rw [hw,hv, mul_mul_mul_comm]
  have hind := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hdis)
    (((measurable_wordWeight_on x w (fun _ hz => Or.inl hz)).ennreal_ofReal).mul
      ((measurable_wordWeight_on y v (fun _ hz => Or.inr hz)).ennreal_ofReal))
    ((measurable_quenched_stay_event_rows T _ hx A hA hAT).mul
      (measurable_quenched_stay_event_rows T _ hy B hB hBT))
  simp only [Pi.mul_apply] at hind
  rw [hind]
  rw [sharedPairLaw_rectangle ν x y _ _ (measurableSet_wordCylinder x w)
    (measurableSet_wordCylinder y v),
    sharedPairLaw_rectangle ν (wordPath x w w.length) (wordPath y v v.length) _ _ hA hB]
  simp only [quenched_wordCylinder]

lemma noDrop_real_integral_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (x : Lattice d) :
    (∫ ω, (noDropQuenched ℓ x ω).toReal ∂environmentLaw ν) =
      ∫ ω, (noDropQuenched ℓ 0 ω).toReal ∂environmentLaw ν := by
  conv_lhs => enter [2, ω]; rw [noDropQuenched_translation ℓ ω x]
  have h := integral_map (μ := environmentLaw ν)
    (show AEMeasurable (fun ω : Environment d => fun a => ω (x + a)) (environmentLaw ν) from
      (by fun_prop : Measurable (fun ω : Environment d => fun a => ω (x + a))).aemeasurable)
    ((measurable_noDropQuenched ℓ 0).ennreal_toReal.aestronglyMeasurable)
  rw [environment_translation] at h
  exact h.symm

end DirectionalTransience
end
end

end OAI
