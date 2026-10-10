import Mathlib
import OAI.Probability.Ballisticity.Renewal.Regeneration

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma ratio_hit_geometric {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (u : Direction d) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (b a D H ε : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D)
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Set (Path d)) (hA : MeasurableSet A) (hp : ε ≤ (annealedLaw ν).real A)
    (hcontrol : ∀ Z ∈ A, ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) (j : ℕ) :
    (annealedLaw ν).real (RatioHit ℓ u b a H (1+j*(2*b+1+D))) ≤ (1-ε)^j := by
  induction j with
  | zero => simp [measureReal_le_one]
  | succ j ih =>
    have ht : 0 < 1+(j : ℝ)*(2*b+1+D) := by positivity
    have hc := ratio_threshold_contraction ν ℓ u hℓ b a D H _ hb ha hD ht A hA hcontrol
    have hcoef : 0 ≤ 1-(annealedLaw ν).real A := sub_nonneg.mpr measureReal_le_one
    have hmul := mul_le_mul_of_nonneg_left ih hcoef
    have hpow := mul_le_mul_of_nonneg_right (show 1-(annealedLaw ν).real A ≤ 1-ε by linarith)
      (pow_nonneg (by linarith : 0 ≤ 1-ε) j)
    have he : 1+(j+1 : ℕ)*(2*b+1+D) = (1+(j : ℝ)*(2*b+1+D))+(2*b+1+D) := by
      push_cast; ring
    rw [he,pow_succ]
    nlinarith

lemma forwardTemplate_probability_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (c C C0 a : ℝ) (K M : ℕ)
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e)
    (hg : (4/5 : ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a K)) :
    (κ : ℝ)^M*(annealedLaw ν).real (NoDrop ℓ 0)*(4/5) ≤
      (annealedLaw ν).real (ForwardTemplate ℓ e c C C0 a K M) := by
  have heq := congrArg ENNReal.toReal (forwardTemplate_probability ν ℓ htrans e he c C C0 a K M)
  simp only [ENNReal.toReal_mul] at heq
  change _ ≤ (annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M)).toReal
  rw [heq]
  have hlo := ENNReal.toReal_mono (measure_ne_top _ _)
    (annealed_wordCylinder_lower ν κ hκ (List.replicate M e))
  simp only [List.length_replicate, ENNReal.toReal_pow, ENNReal.coe_toReal] at hlo
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hlo measureReal_nonneg) hg (by norm_num)
    (mul_nonneg measureReal_nonneg measureReal_nonneg)

lemma ratio_hit_union_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (b a D H ε : ℝ)
    (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : Set (Path d)) (hA : MeasurableSet A) (hp : ε ≤ (annealedLaw ν).real A)
    (hcontrol : ∀ u Z, Z ∈ A → ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) (j : ℕ) :
    (annealedLaw ν).real (⋃ u : Direction d, RatioHit ℓ u b a H (1+j*(2*b+1+D))) ≤
      (2*d : ℕ)*(1-ε)^j := by
  classical
  have h := measureReal_iUnion_fintype_le (μ := annealedLaw ν)
    (fun u : Direction d => RatioHit ℓ u b a H (1+j*(2*b+1+D)))
  refine h.trans ?_
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    ratio_hit_geometric ν ℓ u hℓ b a D H ε hb ha hD hε hε1 A hA hp (hcontrol u) j)
  simpa [Direction, Fintype.card_prod, mul_comm] using hs

lemma annealed_ge_noDrop_mul_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν).real (NoDrop ℓ 0)*(conditionedLaw ν ℓ).real A ≤ (annealedLaw ν).real A := by
  have hh : annealedLaw ν (NoDrop ℓ 0)*conditionedLaw ν ℓ A = annealedLaw ν (A ∩ NoDrop ℓ 0) := by
    rw [conditionedLaw,Measure.smul_apply,Measure.restrict_apply hA,smul_eq_mul,
      ← mul_assoc,ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  have he : (annealedLaw ν).real (NoDrop ℓ 0)*(conditionedLaw ν ℓ).real A =
      (annealedLaw ν).real (A ∩ NoDrop ℓ 0) := by
    simpa only [measureReal_def,ENNReal.toReal_mul] using congrArg ENNReal.toReal hh
  rw [he]
  exact measureReal_mono Set.inter_subset_left

lemma large_excursion_ratio {d : ℕ} (ℓ : Vector d) (X : Path d)
    (h0 : X 0 = 0) (hNN : ∀ n, ∃ e : Direction d, X (n+1) = X n+step e)
    (b a C B t : ℝ) (hb : 0 ≤ b) (ha : 0 < a) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hB : (d : ℝ)*t*(C+3) ≤ B-1) (i N n : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N)
    (hn : (B-1)*a*i < ‖latticeVector (X n)‖)
    (hh : ∀ j ≤ n, 0 ≤ dot (realPosition (X j)) ℓ ∧ dot (realPosition (X j)) ℓ ≤ (C+2)*i) :
    X ∈ ⋃ u : Direction d, RatioHit ℓ u b a ((C+2)*N) t := by
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hM := runningHeight_le ℓ X n ((C+2)*i) (by positivity) (fun j hj => (hh j hj).2)
  have hden : 1+runningHeight ℓ X n ≤ (C+3)*i := by nlinarith
  have hbound : (d : ℝ)*(t*(a*(1+runningHeight ℓ X n))) ≤ (B-1)*a*i := by
    calc
      _ = ((d : ℝ)*t*a)*(1+runningHeight ℓ X n) := by ring
      _ ≤ ((d : ℝ)*t*a)*((C+3)*i) := mul_le_mul_of_nonneg_left hden (by positivity)
      _ = ((d : ℝ)*t*(C+3))*(a*i) := by ring
      _ ≤ (B-1)*(a*i) := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = _ := by ring
  obtain ⟨u,hu⟩ := exists_large_signedCoordinate (X n) _ (hbound.trans_lt hn)
  apply Set.mem_iUnion.mpr
  refine ⟨u,Set.mem_iUnion.mpr ⟨n,?_,?_⟩⟩
  · exact ⟨⟨h0,fun j _ => hNN j⟩,fun j hj => ⟨(hh j hj).1,
      (hh j hj).2.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hiN) (by linarith))⟩⟩
  · change t < tiltedCoordinate ℓ u b a (X n)/(a*(1+runningHeight ℓ X n))
    apply (lt_div_iff₀ (mul_pos ha (by linarith [runningHeight_nonneg ℓ X n]))).mpr
    have hz := mul_nonneg (mul_nonneg hb ha.le) (hh n le_rfl).1
    dsimp only [tiltedCoordinate]
    linarith

lemma conditioned_polynomial_ratio_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (c C C0 a B η b t : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 < B)
    (hη : 0 < η) (hηsmall : η ≤ 1/10) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hthreshold : (d : ℝ)*t*(C+3) ≤ B-1)
    (m N : ℕ) (hm : 1 ≤ m)
    (hC0 : ∀ i ∈ Finset.Ico m (N+1), C*(i-1)+C0+i ≤ (C+2)*i)
    (hg : (4/5 : ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a N))
    (hlow : η/(2*B) ≤ ∑ i ∈ Finset.Ico m (N+1),
      (conditionedLaw ν ℓ).real {X | B*a*i < wordRadius (firstWord ℓ X) ∧
        wordHeightGain ℓ (firstWord ℓ X) ≤ i})
    (hupper : (∑ i ∈ Finset.Ico m (N+1),
      (conditionedLaw ν ℓ).real {X | B*a*i < wordRadius (firstWord ℓ X) ∧
        wordHeightGain ℓ (firstWord ℓ X) ≤ i}) ≤ 2*η) :
    (annealedLaw ν).real (NoDrop ℓ 0)*η/(4*B) ≤
      (annealedLaw ν).real (⋃ u : Direction d, RatioHit ℓ u b a ((C+2)*N) t) := by
  let T := ⋃ u : Direction d, RatioHit ℓ u b a ((C+2)*N) t
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hlo := conditioned_rare_word_template_lower ν ℓ htrans c C C0 a B η hB hη hηsmall
    m N hm hg hlow hupper
  have hmono : μ.real {X | ∃ i ∈ Finset.Ico m (N+1),
      B*a*i < wordRadius (regenerationWords ℓ X (i-1)) ∧
      wordHeightGain ℓ (regenerationWords ℓ X (i-1)) ≤ i ∧
      X ∈ WordTemplate ℓ c C C0 a (i-1)} ≤ μ.real T := by
    apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [conditioned_regenerationSupport ν ℓ htrans,
      (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_nearest_neighbor ν)] with X hX hNN
    rintro ⟨i,hi,hR,hL,hT⟩
    have him : m ≤ i := (Finset.mem_Ico.mp hi).1
    obtain ⟨n,hn,hh⟩ := large_regeneration_word_excursion ℓ X hX.1 hX.2 c C C0 a B ha.le
      i (hm.trans him) hR hL hT (hC0 i hi)
    exact large_excursion_ratio ℓ X hX.1 hNN b a C B t hb ha hC ht hthreshold i N n
      (hm.trans him) (by have := (Finset.mem_Ico.mp hi).2; omega) hn hh
  have hh := annealed_ge_noDrop_mul_conditioned ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) T
    (MeasurableSet.iUnion fun u => measurableSet_ratioHit ℓ u b a ((C+2)*N) t)
  have hmul := mul_le_mul_of_nonneg_left (hlo.trans hmono)
    (measureReal_nonneg (μ := annealedLaw ν) (s := NoDrop ℓ 0))
  dsimp only [T,μ] at hh hmul
  calc
    _ = (annealedLaw ν).real (NoDrop ℓ 0)*(η/(4*B)) := by ring
    _ ≤ _ := hmul.trans hh

lemma firstWord_height_nonneg {d : ℕ} (ℓ : Vector d) (X : Path d) :
    0 ≤ wordHeightGain ℓ (firstWord ℓ X) := by
  by_cases h : firstWord ℓ X = []
  · simp [h,wordHeightGain,dot,realPosition]
  · have hm := (firstWord_eq_iff ℓ X _ h).mp rfl
    exact (wordHeightGain_positive ℓ _
      ((firstTrueWord_characterization ℓ _ X hm.2.1).mp ⟨hm.1,hm.2.2⟩).1).le

lemma geometric_beats_affine (q k L M r : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hr : 0 < r) :
    ∃ j : ℕ, k*(L+M*j)*q^j < r := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have hnp := tendsto_pow_const_mul_const_pow_of_lt_one 1 hq hq1
  have ht : Tendsto (fun j : ℕ => k*(L+M*j)*q^j) atTop (𝓝 0) := by
    convert (hp.const_mul (k*L)).add (hnp.const_mul (k*M)) using 1
    · ext j
      simp only [pow_one]
      ring
    · ring_nf
  exact (ht.eventually (Iio_mem_nhds hr)).exists

lemma nonintegrable_radius_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R L : Ω → ℝ)
    (hR : Measurable R) (hRn : ∀ x, 0 ≤ R x) (hinf : ¬ Integrable R μ)
    (hL : Measurable L) (hLn : ∀ x, 0 ≤ L x) (hLint : Integrable L μ)
    (B η Amin : ℝ) (hB : 1 ≤ B) (hη : 0 < η) (C0 : ℕ) :
    ∃ (A : ℝ) (m N : ℕ), 1 ≤ A ∧ Amin ≤ A ∧ 1 ≤ m ∧ C0 ≤ m ∧ m ≤ N ∧ 2 ≤ N ∧
      truncatedMean μ R (A*N) < 2*η*A ∧
      η/(2*B) ≤ (∑ i ∈ Finset.Ico m (N+1), μ.real {x | B*A*i < R x ∧ L x ≤ (i:ℝ)}) ∧
      (∑ i ∈ Finset.Ico m (N+1), μ.real {x | B*A*i < R x ∧ L x ≤ (i:ℝ)}) < 2*η := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have htail := positive_tail_sums_eventually_small μ L hL hLn hLint
    (show 0 < η/(4*B) by positivity)
  obtain ⟨m,hmTail,hmBig⟩ := (htail.and (eventually_ge_atTop (max 1 C0))).exists
  have hm : 1 ≤ m := (le_max_left _ _).trans hmBig
  have hmC0 : C0 ≤ m := (le_max_right _ _).trans hmBig
  have hbase := (truncatedMean_ratio_tendsto_zero μ R hR hRn (B*m) (by positivity)).eventually
    (Iio_mem_nhds (show 0 < η/4 by positivity))
  have hNlarge := truncation_threshold_eventually_large μ R hR hRn η hη (max m 2)
  obtain ⟨a0,ha0⟩ := exists_nat_ge Amin
  obtain ⟨a,haBase,haN,haBound⟩ := (hbase.and (hNlarge.and (eventually_ge_atTop a0))).exists
  let A : ℝ := (a : ℝ)+1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hA1 : 1 ≤ A := by dsimp only [A]; linarith only [Nat.cast_nonneg a (α := ℝ)]
  have hAmin : Amin ≤ A := ha0.trans ((Nat.cast_le.mpr haBound).trans (by dsimp only [A]; linarith))
  obtain ⟨N,hN,hI,hmin⟩ := exists_minimal_truncation_scale μ R hR hRn hinf η A hη hA
  have hNmax : max m 2 < N := haN N hI
  have hmN : m ≤ N := le_of_lt ((le_max_left _ _).trans_lt hNmax)
  have hN2 : 2 ≤ N := le_of_lt ((le_max_right _ _).trans_lt hNmax)
  have hIhi := minimal_truncation_scale_upper μ R hR hRn η A hA.le hN2 hmin
  have hIbase : truncatedMean μ R (B*A*m) < η*A/4 := by
    have hb' := (div_lt_iff₀ hA).mp haBase
    change truncatedMean μ R ((B*m)*A) < (η/4)*A at hb'
    rwa [show B*A*(m:ℝ) = (B*m)*A by ring, show η*A/4 = (η/4)*A by ring]
  obtain ⟨hintenlo,hintenhi⟩ := restricted_large_word_intensity μ R L hR hRn hA hB hm
    (by omega : m ≤ N+1) hI hIhi hIbase (hmTail (N+1))
  exact ⟨A,m,N,hA1,hAmin,hm,hmC0,hmN,hN2,hIhi,hintenlo,hintenhi⟩

lemma radius_integrable_of_template_constants {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (ℓ : Vector d)
    (htrans : DirectionallyTransient ν ℓ) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (e : Direction d) (he : 0 < dot (realPosition (step e)) ℓ)
    (κ : ℝ≥0) (hκ : 0 < κ)
    (hκenv : ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e)
    (c C : ℝ) (_hc : 0 < c) (hC : 0 < C) (C0 : ℕ)
    (hheight : (19/20 : ℝ) < (conditionedLaw ν ℓ).real {X | ∀ k : ℕ,
      c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
      (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0})
    (C1 : ℕ) (hC1 : 1 ≤ C1) (hC1large : C+2 < c*C1)
    (b : ℝ) (hb : 0 < b) (hbc : 1 ≤ b*c) (M : ℕ)
    (hM : 0 ≤ (M : ℝ)*dot (realPosition (step e)) ℓ-C0)
    (hconst : 0 < b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1)
    (D : ℝ) (hD : (M : ℝ)+1 ≤ D) (hDc : 1 ≤ D*c)
    (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1/10) (hsmall : 4*C1*η < 1/10) :
    Integrable (fun X => wordRadius (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
  by_contra hinf
  let μ := conditionedLaw ν ℓ
  have hp0 := noDrop_positive_of_directionallyTransient ν ℓ htrans
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ (ne_of_gt hp0)
  let R := fun X : Path d => wordRadius (firstWord ℓ X)
  let L := fun X : Path d => wordHeightGain ℓ (firstWord ℓ X)
  have hR : Measurable R := measurable_wordRadius.comp (measurable_firstWord ℓ)
  have hRn : ∀ X, 0 ≤ R X := fun X => wordRadius_nonneg _
  have hL : Measurable L := (measurable_of_countable (wordHeightGain ℓ)).comp (measurable_firstWord ℓ)
  have hLn : ∀ X, 0 ≤ L X := firstWord_height_nonneg ℓ
  have hLint : Integrable L μ := (conditioned_wordHeightGain_moments ν ℓ hℓ htrans).1
  let p : ℝ := (annealedLaw ν).real (NoDrop ℓ 0)
  have hp : 0 < p := ENNReal.toReal_pos (ne_of_gt hp0) (measure_ne_top _ _)
  have hp1 : p ≤ 1 := measureReal_le_one
  have hκ1 : (κ : ℝ) ≤ 1 := by
    obtain ⟨ω,hω⟩ := hκenv.exists
    exact_mod_cast (hω 0 e).trans (row_entry_le_one _ e)
  have hκ0 : (0 : ℝ) < κ := hκ
  let ε : ℝ := (κ : ℝ)^M*p*(4/5)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    have hpow : (κ : ℝ)^M ≤ 1 := pow_le_one₀ κ.coe_nonneg hκ1
    have hkp : (κ : ℝ)^M*p ≤ 1 := calc
      (κ : ℝ)^M*p ≤ 1*p := mul_le_mul_of_nonneg_right hpow hp.le
      _ ≤ 1 := by simpa only [one_mul] using hp1
    dsimp only [ε]
    nlinarith only [hkp, mul_nonneg (pow_nonneg κ.coe_nonneg M) hp.le]
  let K := 2*b+1+D
  have hD0 : 0 ≤ D := by linarith [Nat.cast_nonneg M (α := ℝ)]
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨j,hj⟩ := geometric_beats_affine (1-ε) (2*d : ℕ)
    (2+(d : ℝ)*(C+3)) ((d : ℝ)*(C+3)*K) (p*η/4)
    (by linarith) (by linarith) (by positivity)
  let t : ℝ := 1+j*K
  have ht : 0 < t := by dsimp only [t]; positivity
  let B : ℝ := 2+(d : ℝ)*(C+3)*t
  have hB1 : 1 ≤ B := by
    have hn : 0 ≤ (d : ℝ)*(C+3)*t := by positivity
    dsimp only [B]; linarith only [hn]
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hthreshold : (d : ℝ)*t*(C+3) ≤ B-1 := by dsimp only [B]; nlinarith only []
  have hjB : (2*d : ℕ)*B*(1-ε)^j < p*η/4 := by
    convert hj using 1; dsimp only [B,t]; ring
  let Q := b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1
  have hQ : 0 < Q := hconst
  obtain ⟨A,m,N,hA1,hAmin,hm,hmC0,hmN,hN2,hIhi,hintenlo,hintenhi⟩ :=
    nonintegrable_radius_scale μ R L hR hRn hinf hL hLn hLint B η
      (max ((M : ℝ)/Q) (1/(b*dot (realPosition (step e)) ℓ))) hB1 hη C0
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hAM : (M : ℝ) ≤ A*Q := (div_le_iff₀ hQ).mp ((le_max_left _ _).trans hAmin)
  have hAdelta : 1 ≤ b*A*dot (realPosition (step e)) ℓ := by
    have hh := (div_le_iff₀ (mul_pos hb he)).mp ((le_max_right _ _).trans hAmin)
    nlinarith only [hh]
  have htemplate := controlled_template_probability ν ℓ htrans c C C0 η A hA C1 N hC1
    hheight hsmall hIhi
  have htemplateN : (4/5 : ℝ) ≤ μ.real (WordTemplate ℓ c C C0 A N) :=
    htemplate.le.trans (measureReal_mono (wordTemplate_antitone ℓ c C C0 A
      (show N ≤ C1*N by simpa only [one_mul] using Nat.mul_le_mul_right N hC1)))
  have hlo := conditioned_polynomial_ratio_lower ν ℓ htrans c C C0 A B η b t hA hC.le hB
    hη hηsmall hb.le ht.le hthreshold m N hm (by
      intro i hi
      have hmi := (Finset.mem_Ico.mp hi).1
      have hci : (C0 : ℝ) ≤ i := Nat.cast_le.mpr (hmC0.trans hmi)
      linarith only [hci, hC]) htemplateN hintenlo hintenhi.le
  let F := ForwardTemplate ℓ e c C C0 A (C1*N) M
  have hF : MeasurableSet F := measurableSet_forwardTemplate ℓ e c C C0 A (C1*N) M
  have hprob : ε ≤ (annealedLaw ν).real F :=
    forwardTemplate_probability_lower ν ℓ htrans e he c C C0 A (C1*N) M κ hκenv htemplate.le
  have hgeom : ∀ u Z, Z ∈ F → ∀ k, (0 ≤ tiltedCoordinate ℓ u b A (Z k) ∧
      signedCoordinate u (Z k) ≤ A*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      (C+2)*N < dot (realPosition (Z k)) ℓ := by
    intro u Z hZ k
    apply (forwardTemplate_control ℓ u e c C C0 A b D ((C+2)*N) (C1*N) M hA1 hb.le he.le
      hbc hM hAM ?_ hD hDc ?_ hZ k).2
    · have hstep := signedCoordinate_abs_le_norm u (step e)
      rw [latticeVector_step_norm] at hstep
      have hlow := neg_le_of_abs_le hstep
      dsimp only [tiltedCoordinate]
      have hh := hAdelta
      change 1 ≤ b*A*dot (realPosition (step e)) ℓ at hh
      linarith only [hlow, hh]
    · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
      have hh := mul_lt_mul_of_pos_right hC1large hNpos
      push_cast
      nlinarith only [hh, hM]
  have hup := ratio_hit_union_bound ν ℓ hℓ b A D ((C+2)*N) ε hb.le hA1 hD0 hε.le hε1
    F hF hprob hgeom j
  change p*η/(4*B) ≤ (annealedLaw ν).real (⋃ u : Direction d,
    RatioHit ℓ u b A ((C+2)*N) (1+j*(2*b+1+D))) at hlo
  have hbnd := hlo.trans hup
  have hprod := (div_le_iff₀ (show 0 < 4*B by positivity)).mp hbnd
  nlinarith only [hprod, hjB]

lemma unit_direction_coordinate_bound {d : ℕ} (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1) :
    ∀ i, |ℓ i| ≤ 1 := by
  intro i
  have hh : ℓ i*ℓ i ≤ ∑ j : Fin d, ℓ j*ℓ j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (ℓ j)) (Finset.mem_univ i)
  change ℓ i*ℓ i ≤ dot ℓ ℓ at hh
  rw [hℓ] at hh
  nlinarith [sq_abs (ℓ i),abs_nonneg (ℓ i)]

lemma conditioned_wordRadius_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => wordRadius (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
  have hcoord := unit_direction_coordinate_bound ℓ hℓ
  obtain ⟨e,he⟩ := exists_positive_step ℓ hℓ
  obtain ⟨κ,hκ,hκenv⟩ := environment_uniform_elliptic ν hue
  obtain ⟨c,C,hc,hC,C0,hheight⟩ := conditioned_height_template ν ℓ hcoord htrans (1/20) (by norm_num)
  norm_num only at hheight
  obtain ⟨C1,hC1'⟩ := exists_nat_gt (max 1 ((C+2)/c))
  have hC1r : (1 : ℝ) < C1 := (le_max_left _ _).trans_lt hC1'
  have hC1 : 1 ≤ C1 := by exact_mod_cast hC1r.le
  have hC1large : C+2 < c*C1 := by
    have hh := (div_lt_iff₀ hc).mp ((le_max_right _ _).trans_lt hC1')
    linarith
  let b : ℝ := 2/c
  have hb : 0 < b := by dsimp only [b]; positivity
  have hbc : b*c = 2 := by dsimp only [b]; field_simp
  obtain ⟨M,hM'⟩ := exists_nat_gt (((C0 : ℝ)+2/b)/dot (realPosition (step e)) ℓ)
  have hMdelta : (C0 : ℝ)+2/b < (M : ℝ)*dot (realPosition (step e)) ℓ :=
    (div_lt_iff₀ he).mp hM'
  have hM : 0 ≤ (M : ℝ)*dot (realPosition (step e)) ℓ-C0 := by
    linarith [div_pos (show (0 : ℝ) < 2 by norm_num) hb]
  have hconst : 0 < b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1 := by
    have hh := mul_lt_mul_of_pos_left hMdelta hb
    have heq : b*(2/b) = 2 := by field_simp
    nlinarith
  let D : ℝ := (M : ℝ)+1+1/c
  have hD : (M : ℝ)+1 ≤ D := by dsimp only [D]; linarith only [one_div_pos.mpr hc]
  have hDc : 1 ≤ D*c := by
    have heq : D*c = ((M : ℝ)+1)*c+1 := by dsimp only [D]; field_simp
    rw [heq]
    linarith only [mul_nonneg (show (0:ℝ) ≤ (M:ℝ)+1 by positivity) hc.le]
  let η : ℝ := 1/(100*(C1 : ℝ))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηsmall : η ≤ 1/10 := by
    dsimp only [η]
    apply (div_le_iff₀ (show 0 < 100*(C1 : ℝ) by positivity)).mpr
    nlinarith
  have hsmall : 4*C1*η < 1/10 := by
    have heq : (C1 : ℝ)*η = 1/100 := by dsimp only [η]; field_simp
    nlinarith
  exact radius_integrable_of_template_constants ν ℓ htrans hcoord e he κ hκ hκenv
    c C hc hC C0 hheight C1 hC1 hC1large b hb (by linarith) M hM hconst D hD hDc
    η hη hηsmall hsmall

lemma increment_sublinear_of_average (f : ℕ → ℝ) (m : ℝ)
    (h : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, f i) / n) atTop (𝓝 m)) :
    Tendsto (fun n : ℕ => f n / n) atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ)+1)/n) atTop (𝓝 1) := by
    have hh := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_one, inv_div] using hh
  have hh := ((h.comp (tendsto_add_atTop_nat 1)).mul hr).sub h
  simp only [mul_one, sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hnp : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

noncomputable def wordCoordinate {d : ℕ} (e : Direction d) (w : List (Direction d)) : ℝ :=
  signedCoordinate e (wordPath 0 w w.length)

lemma wordCoordinate_abs_le_radius {d : ℕ} (e : Direction d) (w : List (Direction d)) :
    |wordCoordinate e w| ≤ wordRadius w :=
  (signedCoordinate_abs_le_norm _ _).trans (wordRadius_bound _ (by rfl))

lemma conditioned_wordCoordinate_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (e : Direction d) :
    Integrable (fun X => wordCoordinate e (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
  apply (conditioned_wordRadius_integrable ν hue ℓ hℓ htrans).mono'
    (((measurable_of_countable (wordCoordinate e)).comp (measurable_firstWord ℓ)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun X => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using wordCoordinate_abs_le_radius e (firstWord ℓ X)

lemma conditioned_coordinate_positive_mean {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) : ∃ e : Direction d,
      0 < ∫ X, wordCoordinate e (firstWord ℓ X) ∂conditionedLaw ν ℓ := by
  let μ := conditionedLaw ν ℓ
  have hint (i : Fin d) : Integrable (fun X =>
      wordCoordinate (i,true) (firstWord ℓ X) * ℓ i) μ :=
    (conditioned_wordCoordinate_integrable ν hue ℓ hℓ htrans (i,true)).mul_const _
  have hid : (∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂μ) =
      ∑ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂μ) * ℓ i := by
    change (∫ X, ∑ i : Fin d, wordCoordinate (i,true) (firstWord ℓ X) * ℓ i ∂μ) = _
    rw [integral_finsetSum _ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_mul_const _ _
  have hpos := (conditioned_wordHeightGain_moments ν ℓ
    (unit_direction_coordinate_bound ℓ hℓ) htrans).2.1
  change 0 < ∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂μ at hpos
  rw [hid] at hpos
  have hex : ∃ i : Fin d, (∫ X, wordCoordinate (i,true) (firstWord ℓ X) ∂μ) ≠ 0 := by
    by_contra! hn
    simp only [hn, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hpos
  obtain ⟨i,hi⟩ := hex
  rcases lt_or_gt_of_ne hi with hi | hi
  · refine ⟨(i,false), ?_⟩
    have he : (fun X => wordCoordinate (i,false) (firstWord ℓ X)) =
        fun X => -wordCoordinate (i,true) (firstWord ℓ X) := by
      ext X; simp [wordCoordinate, signedCoordinate]
    rw [he, integral_neg]
    exact neg_pos.mpr hi
  · exact ⟨(i,true), hi⟩

end DirectionalTransience
end
end

end OAI
