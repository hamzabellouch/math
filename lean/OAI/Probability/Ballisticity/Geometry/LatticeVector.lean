import Mathlib
import OAI.Probability.Ballisticity.Geometry.WordHeightGain

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma stationary_initial_average_truncated_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    a * μ.real {x | ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ≤
      2 * truncatedMean μ f (a*K) := by
  let g : Ω → ℝ := fun x => min (f x) (a*K)
  have hg : Measurable g := hf.min measurable_const
  have hgn (x : Ω) : 0 ≤ g x := le_min (hfn x) (mul_nonneg ha.le (Nat.cast_nonneg _))
  have hgi : Integrable g μ := integrable_min_nonneg μ f hf hfn _
    (mul_nonneg ha.le (Nat.cast_nonneg _))
  have hsub : {x | ∃ k, 0 < k ∧ k ≤ K ∧
        a * (k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} ⊆
      {x | ∃ k, 0 < k ∧ k ≤ K ∧
        (a/2) * (k : ℝ) < ∑ j ∈ Finset.range k, g (T^[j] x)} := by
    intro x hx
    obtain ⟨k,hk,hkK,hs⟩ := hx
    refine ⟨k,hk,hkK,?_⟩
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    by_cases ht : ∀ j ∈ Finset.range k, f (T^[j] x) ≤ a*K
    · have he : (∑ j ∈ Finset.range k, g (T^[j] x)) =
          ∑ j ∈ Finset.range k, f (T^[j] x) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact min_eq_left (ht j hj)
      rw [he]
      nlinarith
    · obtain ⟨j,hj,hjt⟩ : ∃ j ∈ Finset.range k, a*K < f (T^[j] x) := by
        simpa only [not_forall, not_le, exists_prop] using ht
      have hle : a*(k : ℝ) ≤ ∑ j ∈ Finset.range k, g (T^[j] x) := by
        calc
          _ ≤ a*K := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkK) ha.le
          _ = g (T^[j] x) := (min_eq_right hjt.le).symm
          _ ≤ _ := Finset.single_le_sum (fun i (_ : i ∈ Finset.range k) => hgn (T^[i] x)) hj
      nlinarith
  have hme := measureReal_mono (μ := μ) hsub
  have hb := stationary_initial_average_bound μ T hT g hg hgi hgn K (a/2) (by linarith)
  change (a/2) * _ ≤ truncatedMean μ f (a*K) at hb
  have hm := mul_le_mul_of_nonneg_left hme (show 0 ≤ a/2 by linarith)
  linarith

lemma truncatedMean_ratio_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => truncatedMean μ f (c*(n+1)) / (n+1)) atTop (𝓝 0) := by
  have hpt (x : Ω) : Tendsto (fun n : ℕ => min (f x) (c*(n+1)) / (n+1)) atTop (𝓝 0) := by
    have hz : Tendsto (fun n : ℕ => f x / (n+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ)+1 by linarith)
        tendsto_natCast_atTop_atTop)
    apply squeeze_zero (fun n => div_nonneg (le_min (hfn x) (mul_nonneg hc (by positivity)))
      (by positivity)) (fun n => div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hz
  have hdom := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n : ℕ => fun x : Ω => min (f x) (c*(n+1)) / (n+1))
    (f := fun _ : Ω => (0 : ℝ)) (fun _ : Ω => c)
    (fun n => ((hf.min measurable_const).div_const _).aestronglyMeasurable)
    (integrable_const c) (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (le_min (hfn x) (mul_nonneg hc (by positivity))) (by positivity))]
      exact (div_le_iff₀ (show (0 : ℝ) < n+1 by positivity)).mpr (min_le_right _ _))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_div, integral_zero, truncatedMean] using hdom

lemma real_integrable_of_scaled_truncation_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {c B : ℝ} (hc : 0 < c)
    (hB : ∀ K : ℕ, truncatedMean μ f (c*K) ≤ B) : Integrable f μ := by
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    have he (x : Ω) : ENNReal.ofReal (f x) =
        ⨆ K : ℕ, ENNReal.ofReal (min (f x) (c*K)) := by
      apply le_antisymm
      · obtain ⟨K,hK⟩ := exists_nat_ge (f x / c)
        have hle : f x ≤ c*K := by
          have := (div_le_iff₀ hc).mp hK
          linarith
        exact le_iSup_of_le K (by rw [min_eq_left hle])
      · exact iSup_le fun K => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    simp_rw [he]
    rw [lintegral_iSup (f := fun K x => ENNReal.ofReal (min (f x) (c*K)))
      (fun K => (hf.min measurable_const).ennreal_ofReal)
      (fun i j hij x => ENNReal.ofReal_le_ofReal
        (min_le_min_left _ (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) hc.le)))]
    apply iSup_le
    intro K
    have hi := integrable_min_nonneg μ f hf hfn (c*K) (mul_nonneg hc.le (Nat.cast_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => le_min (hfn x) (mul_nonneg hc.le (Nat.cast_nonneg _)))]
    exact ENNReal.ofReal_le_ofReal (hB K)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfn)]
  exact hbound.trans_lt ENNReal.ofReal_lt_top

lemma exists_minimal_truncation_scale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hinf : ¬ Integrable f μ)
    (η a : ℝ) (hη : 0 < η) (ha : 0 < a) :
    ∃ N : ℕ, 0 < N ∧ η*a ≤ truncatedMean μ f (a*N) ∧
      ∀ k < N, truncatedMean μ f (a*k) < η*a := by
  have hex : ∃ N : ℕ, η*a ≤ truncatedMean μ f (a*N) := by
    by_contra h
    have hb : ∀ N : ℕ, truncatedMean μ f (a*N) ≤ η*a := by
      intro N
      have := not_exists.mp h N
      exact le_of_lt (lt_of_not_ge this)
    exact hinf (real_integrable_of_scaled_truncation_bound μ f hf hfn ha hb)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra h
    have he : Nat.find hex = 0 := by omega
    have hh := Nat.find_spec hex
    rw [he, Nat.cast_zero, mul_zero, truncatedMean] at hh
    have he' : (fun x => min (f x) 0) = fun _ => (0 : ℝ) :=
      funext fun x => min_eq_right (hfn x)
    rw [he', integral_zero] at hh
    exact (not_le_of_gt (mul_pos hη ha)) hh
  · intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)

lemma minimal_truncation_scale_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (η a : ℝ) (ha : 0 ≤ a) {N : ℕ} (hN : 2 ≤ N)
    (hmin : ∀ k < N, truncatedMean μ f (a*k) < η*a) :
    truncatedMean μ f (a*N) < 2*η*a := by
  have hlt := hmin (N-1) (by omega)
  calc
    _ ≤ truncatedMean μ f (2*(a*(N-1 : ℕ))) :=
      truncatedMean_mono μ f hf hfn (mul_nonneg ha (Nat.cast_nonneg _))
        (by have hn : (N : ℝ) ≤ 2*(N-1 : ℕ) := by exact_mod_cast (show N ≤ 2*(N-1) by omega)
            nlinarith)
    _ ≤ 2*truncatedMean μ f (a*(N-1 : ℕ)) :=
      truncatedMean_mul_le μ f hf hfn (mul_nonneg ha (Nat.cast_nonneg _)) (by norm_num)
    _ < 2*η*a := by linarith

noncomputable def latticeVector {d : ℕ} (x : Lattice d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (realPosition x)

@[simp] lemma latticeVector_zero {d : ℕ} : latticeVector (0 : Lattice d) = 0 := by
  ext i
  simp [latticeVector, realPosition]

lemma latticeVector_add {d : ℕ} (x y : Lattice d) :
    latticeVector (x+y) = latticeVector x + latticeVector y := by
  ext i
  simp [latticeVector, realPosition]

lemma latticeVector_sub {d : ℕ} (x y : Lattice d) :
    latticeVector (x-y) = latticeVector x - latticeVector y := by
  ext i
  simp [latticeVector, realPosition]

lemma latticeVector_step_norm {d : ℕ} (e : Direction d) : ‖latticeVector (step e)‖ = 1 := by
  have hs : ‖latticeVector (step e)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [latticeVector, realPosition, step,
      Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
    simp
  nlinarith [norm_nonneg (latticeVector (step e))]

noncomputable def wordRadius {d : ℕ} (w : List (Direction d)) : ℝ := by
  classical
  exact (Finset.range (w.length+1)).sup' (Finset.nonempty_range_iff.mpr (by omega))
    (fun j => ‖latticeVector (wordPath 0 w j)‖)

lemma wordRadius_bound {d : ℕ} (w : List (Direction d)) {j : ℕ} (hj : j ≤ w.length) :
    ‖latticeVector (wordPath 0 w j)‖ ≤ wordRadius w := by
  classical
  exact Finset.le_sup' (fun j => ‖latticeVector (wordPath 0 w j)‖)
    (Finset.mem_range.mpr (by omega))

lemma wordRadius_nonneg {d : ℕ} (w : List (Direction d)) : 0 ≤ wordRadius w := by
  have hh := wordRadius_bound w (j := 0) (by omega)
  simpa only [wordPath_zero, latticeVector_zero, norm_zero] using hh

lemma wordRadius_attained {d : ℕ} (w : List (Direction d)) :
    ∃ j ≤ w.length, wordRadius w = ‖latticeVector (wordPath 0 w j)‖ := by
  classical
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr
    (show w.length+1 ≠ 0 by omega)) (fun j => ‖latticeVector (wordPath 0 w j)‖)
  exact ⟨j, by have := Finset.mem_range.mp hj; omega, he⟩

lemma wordRadius_le_length {d : ℕ} (w : List (Direction d)) : wordRadius w ≤ w.length := by
  classical
  have hb (j : ℕ) : ‖latticeVector (wordPath 0 w j)‖ ≤ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rcases wordPath_step_or_stay 0 w j with he | ⟨e,he⟩
      · rw [he, Nat.cast_add, Nat.cast_one]; linarith
      · rw [he, latticeVector_add, Nat.cast_add, Nat.cast_one]
        exact (norm_add_le _ _).trans (by rw [latticeVector_step_norm]; linarith)
  apply Finset.sup'_le
  intro j hj
  exact (hb j).trans (Nat.cast_le.mpr (by have := Finset.mem_range.mp hj; omega))

lemma measurable_wordRadius {d : ℕ} : Measurable (wordRadius (d := d)) := measurable_of_countable _

lemma conditioned_radius_initial_average_bound {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (K : ℕ) (a : ℝ) (ha : 0 < a) :
    a * (conditionedLaw ν ℓ).real {X | ∃ k, 0 < k ∧ k ≤ K ∧
      a * (k : ℝ) < ∑ j ∈ Finset.range k, wordRadius (regenerationWords ℓ X j)} ≤
      2 * truncatedMean (conditionedLaw ν ℓ)
        (fun X => wordRadius (firstWord ℓ X)) (a*K) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact stationary_initial_average_truncated_bound _ _
    (renewSuffix_preserves_conditioned ν ℓ htrans) _
    (measurable_wordRadius.comp (measurable_firstWord ℓ)) (fun X => wordRadius_nonneg _) K a ha

lemma affine_envelope_of_average_limit (H : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun n : ℕ => H n / n) atTop (𝓝 L)) :
    ∃ C0 : ℕ, ∀ n : ℕ, (L/2)*n-C0 ≤ H n ∧ H n ≤ (2*L)*n+C0 := by
  have hevent : ∀ᶠ n : ℕ in atTop, L/2 < H n / n ∧ H n / n < 2*L :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨N,hN⟩ := (eventually_atTop.1 hevent)
  let M := max N 1
  let B : ℝ := (∑ j ∈ Finset.range M, |H j|) + 2*L*M
  obtain ⟨C0,hC0⟩ := exists_nat_ge B
  refine ⟨C0, fun n => ?_⟩
  by_cases hn : M ≤ n
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by dsimp [M] at hn; omega)
    obtain ⟨hl,hu⟩ := hN n (by dsimp [M] at hn; omega)
    have hl' := (lt_div_iff₀ hn0).mp hl
    have hu' := (div_lt_iff₀ hn0).mp hu
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) C0]
  · have hn' : n ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have hnM : (n : ℝ) ≤ M := Nat.cast_le.mpr (by omega)
    have hs : |H n| ≤ ∑ j ∈ Finset.range M, |H j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (H j)) hn'
    have hs0 : 0 ≤ ∑ j ∈ Finset.range M, |H j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg (H j)
    dsimp only [B] at hC0
    constructor <;> nlinarith [le_abs_self (H n), neg_abs_le (H n),
      Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) M]

lemma uniform_affine_envelope_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => H n x / n) atTop (𝓝 L))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C0 : ℕ, 1-ε < μ.real {x | ∀ n : ℕ, (L/2)*n-C0 ≤ H n x ∧
      H n x ≤ (2*L)*n+C0} := by
  let E : ℕ → Set Ω := fun C0 => {x | ∀ n : ℕ, (L/2)*n-C0 ≤ H n x ∧
    H n x ≤ (2*L)*n+C0}
  have hmono : Monotone E := by
    intro i j hij x hx n
    have hi := hx n
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    constructor <;> linarith
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ C0, E C0 := by
    filter_upwards [hlim] with x hx
    obtain ⟨C0,hC0⟩ := affine_envelope_of_average_limit (fun n => H n x) L hL hx
    exact Set.mem_iUnion.mpr ⟨C0,hC0⟩
  have hme : μ (⋃ C0, E C0) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [hae] with x hx
    exact propext (iff_true_intro hx)
  have ht := (ENNReal.tendsto_toReal (measure_ne_top μ (⋃ C0, E C0))).comp
    (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  rw [hme, ENNReal.toReal_one] at ht
  have he := ht.eventually (Ioi_mem_nhds (show 1-ε < 1 by linarith))
  obtain ⟨C0,hC0⟩ := he.exists
  exact ⟨C0,hC0⟩

lemma conditioned_height_template {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hℓ : ∀ i, |ℓ i| ≤ 1) (htrans : DirectionallyTransient ν ℓ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ C0 : ℕ,
      1-ε < (conditionedLaw ν ℓ).real {X | ∀ k : ℕ,
        c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
        (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0} := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  obtain ⟨hint,hpositive,_⟩ := conditioned_wordHeightGain_moments ν ℓ hℓ htrans
  let L := ∫ X, wordHeightGain ℓ (firstWord ℓ X) ∂conditionedLaw ν ℓ
  have hmeas : Measurable (wordHeightGain ℓ) := measurable_of_countable _
  have hlim : ∀ᵐ X ∂conditionedLaw ν ℓ, Tendsto
      (fun k : ℕ => (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) / k)
      atTop (𝓝 L) := by
    exact strong_law_ae_real _ hint
      (fun i j hij => ((regenerationWords_independent ν ℓ htrans).indepFun hij).comp hmeas hmeas)
      (fun i => (regenerationWords_identDistrib ν ℓ htrans i).comp hmeas)
  obtain ⟨C0,hC0⟩ := uniform_affine_envelope_probability (conditionedLaw ν ℓ)
    (fun k X => ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j))
    L hpositive hlim ε hε
  exact ⟨L/2,2*L,by linarith,by linarith,C0,hC0⟩

lemma truncation_threshold_eventually_large {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∀ᶠ a : ℕ in atTop, ∀ N : ℕ,
      η*(a+1) ≤ truncatedMean μ f ((a+1)*N) → M < N := by
  have ht := truncatedMean_ratio_tendsto_zero μ f hf hfn (M : ℝ) (Nat.cast_nonneg _)
  have he := ht.eventually (Iio_mem_nhds hη)
  filter_upwards [he] with a ha N hN
  by_contra hNM
  have hNM' : (N : ℝ) ≤ M := Nat.cast_le.mpr (by omega)
  have hb := truncatedMean_mono μ f hf hfn
    (show 0 ≤ ((a : ℝ)+1)*N by positivity)
    (mul_le_mul_of_nonneg_left hNM' (by positivity : 0 ≤ (a : ℝ)+1))
  have ha' := (div_lt_iff₀ (show 0 < (a : ℝ)+1 by positivity)).mp ha
  rw [mul_comm ((a : ℝ)+1) (M : ℝ)] at hb
  linarith

lemma truncated_template_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (η a : ℝ) (ha : 0 < a) (C1 N : ℕ) (hC1 : 1 ≤ C1)
    (hI : truncatedMean μ f (a*N) < 2*η*a) :
    μ.real {x | ∃ k, 0 < k ∧ k ≤ C1*N ∧
      a*(k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} < 4*C1*η := by
  have hb := stationary_initial_average_truncated_bound μ T hT f hf hfn (C1*N) a ha
  have hc : (1 : ℝ) ≤ C1 := by exact_mod_cast hC1
  have hs := truncatedMean_mul_le μ f hf hfn
    (mul_nonneg ha.le (Nat.cast_nonneg N)) hc
  have he : a*(C1*N : ℕ) = (C1 : ℝ)*(a*N) := by push_cast; ring
  rw [he] at hb
  have hC1pos : (0 : ℝ) < C1 := lt_of_lt_of_le zero_lt_one hc
  have hmul := mul_lt_mul_of_pos_left hI hC1pos
  have hh : a * μ.real {x | ∃ k, 0 < k ∧ k ≤ C1*N ∧
      a*(k : ℝ) < ∑ j ∈ Finset.range k, f (T^[j] x)} < a*(4*C1*η) := by
    nlinarith
  exact (mul_lt_mul_iff_right₀ ha).mp hh

lemma restricted_union_lower_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (p : ι → ℝ) (q : ℝ)
    (hfirst : ∀ i ∈ S, q*p i ≤ μ.real (E i))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → μ.real (E i ∩ E j) ≤ p i * p j) :
    q * (∑ i ∈ S, p i) - (∑ i ∈ S, p i)^2 / 2 ≤ μ.real (⋃ i ∈ S, E i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfirstS : ∀ i ∈ S, q*p i ≤ μ.real (E i) := fun i hi => hfirst i (by simp [hi])
    have hpairS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → μ.real (E i ∩ E j) ≤ p i * p j :=
      fun i hi j hj hij => hpair i (by simp [hi]) j (by simp [hj]) hij
    have hold := ih hfirstS hpairS
    have hnew := hfirst a (Finset.mem_insert_self a S)
    have hcross : μ.real (E a ∩ ⋃ i ∈ S, E i) ≤ p a * (∑ i ∈ S, p i) := by
      rw [Set.inter_iUnion]
      simp_rw [Set.inter_iUnion]
      calc
        _ ≤ ∑ i ∈ S, μ.real (E a ∩ E i) := measureReal_biUnion_finset_le S _
        _ ≤ ∑ i ∈ S, p a * p i := by
          apply Finset.sum_le_sum
          intro i hi
          exact hpair a (by simp) i (by simp [hi]) (by intro he; subst i; contradiction)
        _ = _ := by rw [Finset.mul_sum]
    have hidentity := measureReal_union_add_inter₀' (μ := μ) (hE a).nullMeasurableSet
      (s := E a) (t := ⋃ i ∈ S, E i) (h₂ := measure_ne_top μ _)
    simp only [Finset.sum_insert ha, Finset.set_biUnion_insert]
    nlinarith [sq_nonneg (p a)]

lemma independent_rare_words_lower_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset ι) (A G : ι → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hG : ∀ i, MeasurableSet (G i)) (q : ℝ)
    (hprev : ∀ i ∈ S, q*μ.real (A i) ≤ μ.real (A i ∩ G i))
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      μ.real (A i ∩ A j) = μ.real (A i) * μ.real (A j)) :
    q * (∑ i ∈ S, μ.real (A i)) - (∑ i ∈ S, μ.real (A i))^2 / 2 ≤
      μ.real {x | ∃ i ∈ S, x ∈ A i ∧ x ∈ G i} := by
  have hh := restricted_union_lower_bound μ S (fun i => A i ∩ G i)
    (fun i => (hA i).inter (hG i)) (fun i => μ.real (A i)) q hprev (by
      intro i hi j hj hij
      calc
        μ.real ((A i ∩ G i) ∩ (A j ∩ G j)) ≤ μ.real (A i ∩ A j) :=
          measureReal_mono (μ := μ) (fun _ hx => ⟨hx.1.1,hx.2.1⟩)
        _ = _ := hpair i hi j hj hij)
  have he : (⋃ i ∈ S, A i ∩ G i) = {x | ∃ i ∈ S, x ∈ A i ∧ x ∈ G i} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    aesop
  rwa [he] at hh

lemma annealed_avoiding_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (w : List (Direction d))
    (hnew : wordPath 0 w w.length ∉ wordDepartures 0 w)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (havoid : ∀ X ∈ A, ∀ j, wordPath 0 w w.length + X j ∉ wordDepartures 0 w) :
    annealedLaw ν ((fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * annealedLaw ν A := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w)
  let T : Set (Lattice d) := Sᶜ
  let B : Set (Path d) := (fun X : Path d => fun j => X j - y) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hBT : B ⊆ Stay T := by
    intro X hX j
    have h := havoid (fun k => X k-y) hX j
    have he : wordPath 0 w w.length + (X j-y) = X j := by dsimp only [y]; abel
    rw [he] at h
    exact h
  have hST : Disjoint S T := disjoint_compl_right
  have hw (ω : Environment d) : quenchedKernel (ω, 0)
      ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * quenchedKernel (ω, y) B := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length hB
    change quenchedKernel (ω, 0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω, 0) (wordCylinder 0 w) * quenchedKernel (ω, y) B at hh
    rwa [quenched_wordCylinder] at hh
  rw [annealed_apply ν ((hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder 0 w))]
  change (∫⁻ ω, quenchedKernel (ω, 0)
    ((fun X : Path d => fun j => X (w.length + j) - y) ⁻¹' A ∩ wordCylinder 0 w)
    ∂environmentLaw ν) = _
  simp_rw [hw]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((measurable_wordWeight_on 0 w (fun _ hz => hz)).ennreal_ofReal)
    (measurable_quenched_stay_event_rows T y hnew B hB hBT)]
  rw [← annealed_wordCylinder, annealed_event_translation ν y A hA]

end DirectionalTransience
end
end

end OAI
