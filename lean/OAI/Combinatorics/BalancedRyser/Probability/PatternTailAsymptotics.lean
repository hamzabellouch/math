import OAI.Combinatorics.BalancedRyser.Probability.PatternFiniteExposure
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentTails

namespace OAI

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Balanced.PatternTails

universe u v w

theorem polynomial_union_tail_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω)
    (q : ℝ) (hq : 0 < q) (d k : ℕ) (A C : ℝ) (hC : 0 ≤ C)
    (hcard : (Fintype.card ι : ℝ) ≤ A * q ^ d)
    (htail : ∀ i, μ.real (E i) ≤ C / q ^ (d + k)) :
    μ.real (⋃ i, E i) ≤ A * C / q ^ k := by
  calc
    μ.real (⋃ i, E i) ≤ ∑ i, μ.real (E i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, C / q ^ (d + k) := Finset.sum_le_sum (fun i _ => htail i)
    _ = (Fintype.card ι : ℝ) * (C / q ^ (d + k)) := by simp
    _ ≤ (A * q ^ d) * (C / q ^ (d + k)) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hC (pow_nonneg hq.le _))
    _ = A * C / q ^ k := by
      rw [pow_add]
      field_simp

theorem tendsto_zero_of_uniform_inverse_bound
    {X : ℕ → Type*} (p : ∀ q, X q → ℝ)
    (hp : ∀ q x, 0 ≤ p q x)
    (hbound : ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x, p q x ≤ C / (q : ℝ))
    (x : ∀ q, X q) :
    Tendsto (fun q => p q (x q)) atTop (𝓝 0) := by
  obtain ⟨C, q₀, hC⟩ := hbound
  apply squeeze_zero' (Eventually.of_forall (fun q => hp q (x q)))
  · filter_upwards [eventually_ge_atTop q₀] with q hq
    exact hC q hq (x q)
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C

theorem polynomial_union_tendsto_zero
    {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (I : ℕ → Type v) [∀ n, Fintype (I n)] (E : ∀ n, I n → Set (Ω n))
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (d : ℕ) (A C : ℝ) (hC : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n) : ℝ) ≤ A * (q n : ℝ) ^ d)
    (htail : ∀ᶠ n in atTop, ∀ i, (μ n).real (E n i) ≤ C / (q n : ℝ) ^ (d + 1)) :
    Tendsto (fun n => (μ n).real (⋃ i, E n i)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg))
  · filter_upwards [hcard, htail, hq.eventually (eventually_gt_atTop 0)] with n hn ht hqn
    have hqpos : (0 : ℝ) < q n := by exact_mod_cast hqn
    simpa only [pow_one] using
      polynomial_union_tail_le (μ n) (E n) (q n) hqpos d 1 A C hC hn ht
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp hq).const_mul (A * C)

theorem uniform_polynomial_raw_tail
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (f : ∀ q, I q → (P q).Sample → ℝ)
    (hf : ∀ q i, Measurable (f q i))
    (hf0 : ∀ q i ω, 0 ≤ f q i ω)
    (B : ∀ q, I q → ℝ) (hfB : ∀ q i ω, f q i ω ≤ B q i)
    (d : ℕ)
    (hcard : ∃ A : ℝ, 0 < A ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
      (Fintype.card (I q) : ℝ) ≤ A * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ x : (P q).Sample, ∀ i,
        (P q).fixedExpectation (K q) x (fun ω => f q i ω ^ s) ≤ C)
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ∃ i,
        (q : ℝ) ^ ((1 : ℝ) / 100) ≤ f q i ((P q).fixCoordinates (K q) x ω)} ≤
          C / (q : ℝ) ^ k := by
  obtain ⟨A, hA, qa, ha⟩ := hcard
  obtain ⟨C, hC, qc, hc⟩ := hmom (100 * (d + k)) (by omega)
  refine ⟨A * C, mul_pos hA hC, max (max qa qc) 1, ?_⟩
  intro q hq x
  have hqa : qa ≤ q := (le_max_left qa qc).trans ((le_max_left _ _).trans hq)
  have hqc : qc ≤ q := (le_max_right qa qc).trans ((le_max_left _ _).trans hq)
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := (le_max_right (max qa qc) 1).trans hq
    exact_mod_cast (by omega : 0 < q)
  have hpow : ((q : ℝ) ^ ((1 : ℝ) / 100)) ^ (100 * (d + k)) =
      (q : ℝ) ^ (d + k) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    have he : ((1 : ℝ) / 100) * ((100 * (d + k) : ℕ) : ℝ) =
        ((d + k : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have htail (i : I q) :
      (P q).measure.real {ω | (q : ℝ) ^ ((1 : ℝ) / 100) ≤
        f q i ((P q).fixCoordinates (K q) x ω)} ≤ C / (q : ℝ) ^ (d + k) := by
    have h := (fixed_tail_le_moment (P q) (K q) x (f q i) (hf q i)
      (hf0 q i) (B q i) (hfB q i) ((q : ℝ) ^ ((1 : ℝ) / 100))
      (Real.rpow_pos_of_pos hqpos _)
      (100 * (d + k))).trans
      (div_le_div_of_nonneg_right (hc q hqc x i) (by positivity))
    simpa only [hpow] using h
  have h := polynomial_union_tail_le (P q).measure
    (fun i => {ω | (q : ℝ) ^ ((1 : ℝ) / 100) ≤
      f q i ((P q).fixCoordinates (K q) x ω)})
    q hqpos d k A C hC.le (ha q hqa) htail
  simpa only [Set.mem_iUnion, Set.ofPred_exists] using h

theorem uniform_polynomial_centered_tail
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (f : ∀ q, I q → (P q).Sample → ℝ)
    (hf : ∀ q i, Measurable (f q i))
    (B : ∀ q, I q → ℝ) (hfB : ∀ q i ω, |f q i ω| ≤ B q i)
    (d : ℕ)
    (hcard : ∃ A : ℝ, 0 < A ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
      (Fintype.card (I q) : ℝ) ≤ A * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ x : (P q).Sample, ∀ i,
        (P q).fixedExpectation (K q) x
          (fun ω => |f q i ω - (P q).fixedExpectation (K q) x (f q i)| ^ (2 * s)) ≤
            C * (q : ℝ) ^ s)
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ∃ i, ε * (q : ℝ) ≤
        |f q i ((P q).fixCoordinates (K q) x ω) -
          (P q).fixedExpectation (K q) x (f q i)|} ≤ C / (q : ℝ) ^ k := by
  obtain ⟨A, hA, qa, ha⟩ := hcard
  obtain ⟨C, hC, qc, hc⟩ := hmom (d + k) (by omega)
  refine ⟨A * (C / ε ^ (2 * (d + k))), by positivity, max (max qa qc) 1, ?_⟩
  intro q hq x
  have hqa : qa ≤ q := (le_max_left qa qc).trans ((le_max_left _ _).trans hq)
  have hqc : qc ≤ q := (le_max_right qa qc).trans ((le_max_left _ _).trans hq)
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := (le_max_right (max qa qc) 1).trans hq
    exact_mod_cast (by omega : 0 < q)
  have htail (i : I q) :
      (P q).measure.real {ω | ε * (q : ℝ) ≤
        |f q i ((P q).fixCoordinates (K q) x ω) -
          (P q).fixedExpectation (K q) x (f q i)|} ≤
        (C / ε ^ (2 * (d + k))) / (q : ℝ) ^ (d + k) := by
    have hb (ω : (P q).Sample) :
        |f q i ω - (P q).fixedExpectation (K q) x (f q i)| ≤
          B q i + |(P q).fixedExpectation (K q) x (f q i)| :=
      (abs_sub _ _).trans (add_le_add (hfB q i ω) le_rfl)
    calc
      (P q).measure.real {ω | ε * (q : ℝ) ≤
        |f q i ((P q).fixCoordinates (K q) x ω) -
          (P q).fixedExpectation (K q) x (f q i)|} ≤
        (P q).fixedExpectation (K q) x
          (fun ω => |f q i ω - (P q).fixedExpectation (K q) x (f q i)| ^
            (2 * (d + k))) / (ε * q) ^ (2 * (d + k)) :=
        fixed_tail_le_moment (P q) (K q) x _ ((hf q i).sub_const _).abs
          (fun _ => abs_nonneg _) _ hb (ε * q) (mul_pos hε hqpos) _
      _ ≤ (C * (q : ℝ) ^ (d + k)) / (ε * q) ^ (2 * (d + k)) :=
        div_le_div_of_nonneg_right (hc q hqc x i) (by positivity)
      _ = (C / ε ^ (2 * (d + k))) / (q : ℝ) ^ (d + k) := by
        rw [mul_pow, show 2 * (d + k) = (d + k) + (d + k) by omega,
          pow_add, pow_add]
        field_simp
        simp only [pow_add]
        ring
  have h := polynomial_union_tail_le (P q).measure
    (fun i => {ω | ε * (q : ℝ) ≤
      |f q i ((P q).fixCoordinates (K q) x ω) -
        (P q).fixedExpectation (K q) x (f q i)|})
    q hqpos d k A (C / ε ^ (2 * (d + k))) (by positivity) (ha q hqa) htail
  simpa only [Set.mem_iUnion, Set.ofPred_exists] using h

theorem tendsto_all_tests_of_bad_union
    {Ω : ℕ → Type u} [∀ q, MeasurableSpace (Ω q)]
    (μ : ∀ q, Measure (Ω q)) [∀ q, IsProbabilityMeasure (μ q)]
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (E : ∀ q, I q → Set (Ω q)) (hE : ∀ q i, MeasurableSet (E q i))
    (hbad : Tendsto (fun q => (μ q).real (⋃ i, E q i)) atTop (𝓝 0)) :
    Tendsto (fun q => (μ q).real {ω | ∀ i, ω ∉ E q i}) atTop (𝓝 1) := by
  have h := tendsto_const_nhds.sub hbad (a := (1 : ℝ))
  simp only [sub_zero] at h
  convert h using 1
  funext q
  have hset : {ω | ∀ i, ω ∉ E q i} = (⋃ i, E q i)ᶜ := by ext ω; simp
  rw [hset, measureReal_compl (MeasurableSet.iUnion (hE q))]
  simp

theorem simultaneous_fixed_tests_of_uniform_inverse_bound
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (f : ∀ q, (P q).Sample → I q → (P q).Sample → ℝ)
    (hf : ∀ q x i, Measurable (f q x i)) (t : ℕ → ℝ)
    (hbound : ∃ C : ℝ, ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ∃ i, t q ≤ f q x i ((P q).fixCoordinates (K q) x ω)} ≤
        C / (q : ℝ))
    (x : ∀ q, (P q).Sample) :
    Tendsto (fun q => (P q).measure.real {ω | ∃ i,
      t q ≤ f q (x q) i ((P q).fixCoordinates (K q) (x q) ω)}) atTop (𝓝 0) ∧
    Tendsto (fun q => (P q).measure.real {ω | ∀ i,
      f q (x q) i ((P q).fixCoordinates (K q) (x q) ω) < t q}) atTop (𝓝 1) := by
  have hbad := tendsto_zero_of_uniform_inverse_bound
    (fun q x => (P q).measure.real {ω | ∃ i,
      t q ≤ f q x i ((P q).fixCoordinates (K q) x ω)})
    (fun _ _ => measureReal_nonneg) hbound x
  refine ⟨hbad, ?_⟩
  have h := tendsto_all_tests_of_bad_union (fun q => (P q).measure) I
    (fun q i => {ω | t q ≤ f q (x q) i ((P q).fixCoordinates (K q) (x q) ω)})
    (fun q i => measurableSet_le measurable_const
      ((hf q (x q) i).comp ((P q).measurable_fixCoordinates (K q) (x q))))
    (by simpa only [Set.mem_iUnion, Set.ofPred_exists] using hbad)
  simpa only [Set.mem_ofPred_eq, not_le] using h

theorem simultaneous_raw_tests_of_uniform_moments
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (f : ∀ q, I q → (P q).Sample → ℝ)
    (hf : ∀ q i, Measurable (f q i)) (hf0 : ∀ q i ω, 0 ≤ f q i ω)
    (B : ∀ q, I q → ℝ) (hfB : ∀ q i ω, f q i ω ≤ B q i)
    (d : ℕ)
    (hcard : ∃ A : ℝ, 0 < A ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
      (Fintype.card (I q) : ℝ) ≤ A * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ x : (P q).Sample, ∀ i,
        (P q).fixedExpectation (K q) x (fun ω => f q i ω ^ s) ≤ C)
    (x : ∀ q, (P q).Sample) :
    Tendsto (fun q => (P q).measure.real {ω | ∀ i,
      f q i ((P q).fixCoordinates (K q) (x q) ω) <
        (q : ℝ) ^ ((1 : ℝ) / 100)}) atTop (𝓝 1) := by
  obtain ⟨C, _hC, q₀, hq₀⟩ :=
    uniform_polynomial_raw_tail P K I f hf hf0 B hfB d hcard hmom 1 (by omega)
  apply (simultaneous_fixed_tests_of_uniform_inverse_bound P K I
    (fun q _ i => f q i) (fun q _ i => hf q i)
    (fun q => (q : ℝ) ^ ((1 : ℝ) / 100)) _ x).2
  exact ⟨C, q₀, fun q hq x => by simpa only [pow_one] using hq₀ q hq x⟩

theorem simultaneous_centered_tests_of_uniform_moments
    (P : ℕ → PatternModel.{u}) (K : ∀ q, Finset (P q).Color)
    (I : ℕ → Type v) [∀ q, Fintype (I q)]
    (f : ∀ q, I q → (P q).Sample → ℝ) (hf : ∀ q i, Measurable (f q i))
    (B : ∀ q, I q → ℝ) (hfB : ∀ q i ω, |f q i ω| ≤ B q i)
    (d : ℕ)
    (hcard : ∃ A : ℝ, 0 < A ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
      (Fintype.card (I q) : ℝ) ≤ A * (q : ℝ) ^ d)
    (hmom : ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ x : (P q).Sample, ∀ i,
        (P q).fixedExpectation (K q) x
          (fun ω => |f q i ω - (P q).fixedExpectation (K q) x (f q i)| ^ (2 * s)) ≤
            C * (q : ℝ) ^ s)
    (ε : ℝ) (hε : 0 < ε) (x : ∀ q, (P q).Sample) :
    Tendsto (fun q => (P q).measure.real {ω | ∀ i,
      |f q i ((P q).fixCoordinates (K q) (x q) ω) -
        (P q).fixedExpectation (K q) (x q) (f q i)| < ε * (q : ℝ)})
      atTop (𝓝 1) := by
  obtain ⟨C, _hC, q₀, hq₀⟩ :=
    uniform_polynomial_centered_tail P K I f hf B hfB d hcard hmom ε hε 1 (by omega)
  apply (simultaneous_fixed_tests_of_uniform_inverse_bound P K I
    (fun q x i ω => |f q i ω - (P q).fixedExpectation (K q) x (f q i)|)
    (fun q _ i => ((hf q i).sub_const _).abs) (fun q => ε * (q : ℝ)) _ x).2
  exact ⟨C, q₀, fun q hq x => by simpa only [pow_one] using hq₀ q hq x⟩

end Balanced.PatternTails

end OAI
