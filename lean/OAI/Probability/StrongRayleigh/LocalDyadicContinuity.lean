import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

noncomputable section

open Filter
open scoped Topology NNReal

namespace Problem336AdditiveD139.LocalDyadicContinuity

abbrev Interval (T : ℕ) := Set.Icc (0 : ℝ) (T : ℝ)

variable {T : ℕ}

def gridIndex (n : ℕ) (x : Interval T) : ℕ :=
  ⌊(2 : ℝ) ^ n * (x : ℝ)⌋₊

lemma gridIndex_le (n : ℕ) (x : Interval T) : gridIndex n x ≤ T * 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [x.property.2, pow_pos (show (0 : ℝ) < 2 by norm_num) n]

lemma gridIndex_succ_div_two (n : ℕ) (x : Interval T) :
    gridIndex (n + 1) x / 2 = gridIndex n x := by
  unfold gridIndex
  have heq : (2 : ℝ) ^ (n + 1) * (x : ℝ) = ((2 : ℝ) ^ n * (x : ℝ)) * 2 := by
    ring
  rw [heq]
  exact Nat.mul_cast_floor_div_cancel (by decide : 2 ≠ 0) _

lemma gridIndex_succ_cases (n : ℕ) (x : Interval T) :
    gridIndex (n + 1) x = 2 * gridIndex n x ∨
      gridIndex (n + 1) x = 2 * gridIndex n x + 1 := by
  have h := gridIndex_succ_div_two n x
  omega

def approximation (f : ℕ → ℕ → ℝ) (n : ℕ) (x : Interval T) : ℝ :=
  f n (gridIndex n x)

lemma approximation_increment_le (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n : ℕ) (x : Interval T) :
    |approximation f (n + 1) x - approximation f n x| ≤ a (n + 1) := by
  unfold approximation
  rcases gridIndex_succ_cases n x with heven | hodd
  · rw [heven, hcoh, sub_self, abs_zero]
    exact ha _
  · rw [hodd, ← hcoh n (gridIndex n x)]
    apply hadj
    have hle := gridIndex_le (n + 1) x
    rw [hodd] at hle
    omega

lemma gridIndex_close (n : ℕ) (x y : Interval T)
    (hxy : |(x : ℝ) - (y : ℝ)| < 1 / (2 : ℝ) ^ n) :
    gridIndex n x ≤ gridIndex n y + 1 := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hy := Nat.lt_floor_add_one ((2 : ℝ) ^ n * (y : ℝ))
  have hx0 : 0 ≤ (2 : ℝ) ^ n * (x : ℝ) := mul_nonneg hp.le x.property.1
  have hd : (2 : ℝ) ^ n * ((x : ℝ) - (y : ℝ)) < 1 := by
    have := (abs_lt.mp hxy).2
    nlinarith [mul_lt_mul_of_pos_left this hp, div_mul_cancel₀ (1 : ℝ) hp.ne']
  have hh : (2 : ℝ) ^ n * (x : ℝ) < (gridIndex n y : ℝ) + 2 := by
    change (2 : ℝ) ^ n * (y : ℝ) < (gridIndex n y : ℝ) + 1 at hy
    linarith
  have : gridIndex n x < gridIndex n y + 2 := by
    apply (Nat.floor_lt hx0).mpr
    push_cast
    exact hh
  omega

lemma approximation_close (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n : ℕ) (x y : Interval T)
    (hxy : |(x : ℝ) - (y : ℝ)| < 1 / (2 : ℝ) ^ n) :
    |approximation f n x - approximation f n y| ≤ a n := by
  have h1 := gridIndex_close n x y hxy
  have h2 := gridIndex_close n y x (by simpa [abs_sub_comm] using hxy)
  have hx := gridIndex_le n x
  have hy := gridIndex_le n y
  have hc : gridIndex n x = gridIndex n y ∨
      gridIndex n x = gridIndex n y + 1 ∨
      gridIndex n y = gridIndex n x + 1 := by omega
  unfold approximation
  rcases hc with heq | heq | heq
  · rw [heq, sub_self, abs_zero]
    exact ha n
  · rw [heq]
    exact hadj n _ (by omega)
  · rw [heq, abs_sub_comm]
    exact hadj n _ (by omega)

theorem exists_uniformContinuous_limit
    (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    ∃ g : Interval T → ℝ, UniformContinuous g ∧
      TendstoUniformly (approximation f) g atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (g x)) := by
  have hsum' : Summable (fun n => a (n + 1)) :=
    hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hstep (x : Interval T) (n : ℕ) :
      dist (approximation f n x) (approximation f (n + 1) x) ≤ a (n + 1) := by
    rw [Real.dist_eq, abs_sub_comm]
    exact approximation_increment_le f a ha hcoh hadj n x
  have hex (x : Interval T) : ∃ z : ℝ,
      Tendsto (fun n => approximation f n x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dist_le_of_summable (fun n => a (n + 1)) (hstep x) hsum')
  choose g hg using hex
  have hbound (n : ℕ) (x : Interval T) :
      dist (approximation f n x) (g x) ≤ ∑' m, a (n + m + 1) :=
    dist_le_tsum_of_dist_le_of_tendsto (fun n => a (n + 1))
      (hstep x) hsum' (hg x) n
  have htail : Tendsto (fun n => ∑' m, a (n + m + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun n => a (n + 1))
  have hunif : TendstoUniformly (approximation f) g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp htail).2 ε hε] with n hn
    intro x
    rw [dist_comm]
    exact (hbound n x).trans_lt hn
  refine ⟨g, ?_, hunif, hg⟩
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have htotal : Tendsto (fun n => 2 * (∑' m, a (n + m + 1)) + a n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (htail.const_mul 2).add hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := ((tendsto_order.mp htotal).2 ε hε).exists
  refine ⟨1 / (2 : ℝ) ^ N, by positivity, ?_⟩
  intro x y hxy
  change dist (x : ℝ) (y : ℝ) < 1 / (2 : ℝ) ^ N at hxy
  have hc : |approximation f N x - approximation f N y| ≤ a N :=
    approximation_close f a ha hadj N x y (by simpa only [Real.dist_eq] using hxy)
  have hx := hbound N x
  have hy := hbound N y
  have hx' : dist (g x) (approximation f N x) ≤ ∑' m, a (N + m + 1) := by
    simpa only [dist_comm] using hx
  have htri := dist_triangle4 (g x) (approximation f N x) (approximation f N y) (g y)
  rw [Real.dist_eq (approximation f N x) (approximation f N y)] at htri
  exact (htri.trans (by linarith)).trans_lt hN

lemma coherent_refinement (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k) (n k l : ℕ) :
    f (n + l) (2 ^ l * k) = f n k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show n + (l + 1) = (n + l) + 1 by omega,
      show 2 ^ (l + 1) * k = 2 * (2 ^ l * k) by ring, hcoh, ih]

lemma gridIndex_at_node (n k l : ℕ) (x : Interval T)
    (hx : (x : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    gridIndex (n + l) x = 2 ^ l * k := by
  unfold gridIndex
  rw [hx]
  have heq : (2 : ℝ) ^ (n + l) * ((k : ℝ) / (2 : ℝ) ^ n) =
      ((2 ^ l * k : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [heq, Nat.floor_natCast]

theorem limit_agrees_grid (f : ℕ → ℕ → ℝ) (g : Interval T → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlim : ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (g x)))
    (n k : ℕ) (x : Interval T) (hx : (x : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    g x = f n k := by
  have hevent : (fun m => approximation f m x) =ᶠ[atTop] fun _ => f n k := by
    refine eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hm
    dsimp only [approximation]
    rw [gridIndex_at_node n k l x hx, coherent_refinement f hcoh]
  exact tendsto_nhds_unique (hlim x) (tendsto_const_nhds.congr' hevent.symm)

def limit (f : ℕ → ℕ → ℝ) (x : Interval T) : ℝ :=
  limUnder atTop (fun n => approximation f n x)

theorem uniformContinuous_limit (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ n k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    UniformContinuous (limit (T := T) f) ∧
      TendstoUniformly (approximation f) (limit (T := T) f) atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (limit (T := T) f x)) := by
  obtain ⟨g, hcont, hunif, hlim⟩ :=
    exists_uniformContinuous_limit (T := T) f a ha hsum hcoh hadj
  have heq : limit (T := T) f = g := funext fun x => (hlim x).limUnder_eq
  rw [heq]
  exact ⟨hcont, hunif, hlim⟩

theorem uniformContinuous_limit_of_eventually (f : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hadj : ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    UniformContinuous (limit (T := T) f) ∧
      TendstoUniformly (approximation f) (limit (T := T) f) atTop ∧
      ∀ x, Tendsto (fun n => approximation f n x) atTop (𝓝 (limit (T := T) f x)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hadj
  let b : ℕ → ℝ := fun n =>
    if n < N then ∑ k ∈ Finset.range (T * 2 ^ n), |f n (k + 1) - f n k| else a n
  have hb : ∀ n, 0 ≤ b n := by
    intro n
    dsimp [b]
    split_ifs
    · exact Finset.sum_nonneg fun k _ => abs_nonneg _
    · exact ha n
  have hab : a =ᶠ[cofinite] b := by
    rw [Nat.cofinite_eq_atTop]
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    simp [b, not_lt.mpr hn]
  have hbsum : Summable b := hsum.congr_cofinite hab
  apply uniformContinuous_limit (T := T) f b hb hbsum hcoh
  intro n k hk
  by_cases hn : n < N
  · dsimp [b]
    rw [ite_eq_left hn]
    exact Finset.single_le_sum (f := fun j => |f n (j + 1) - f n j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hk)
  · simpa [b, hn] using hN n (not_lt.mp hn) k hk

theorem measurable_limit_eval {Ω : Type u_1} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k))
    (x : Interval T) : Measurable (fun ω => limit (T := T) (f ω) x) := by
  exact (MeasureTheory.StronglyMeasurable.limUnder
    (fun n => (hf n (gridIndex n x)).stronglyMeasurable)).measurable

theorem measurable_limit {Ω : Type u_2} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k)) :
    Measurable (fun ω => limit (T := T) (f ω)) :=
  Measurable.of_eval (fun x => measurable_limit_eval f hf x)

def globalLimit (f : ℕ → ℕ → ℝ) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun n => f n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊)

theorem continuous_globalLimit (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlocal : ∀ T : ℕ, ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n) :
    Continuous (globalLimit f) := by
  have hcont (T : ℕ) : ContinuousOn (globalLimit f) (Set.Iic (T : ℝ≥0)) := by
    obtain ⟨a, ha, hsum, hadj⟩ := hlocal T
    have hc := (uniformContinuous_limit_of_eventually f a ha hsum hcoh hadj).1.continuous
    let e : Set.Iic (T : ℝ≥0) → Interval T := fun x =>
      ⟨(x.val : ℝ), x.val.property, by exact_mod_cast x.property⟩
    have he : Continuous e :=
      (NNReal.continuous_coe.comp continuous_subtype_val).subtype_mk _
    rw [continuousOn_iff_continuous_domRestrict]
    have hce : Continuous ((limit (T := T) f) ∘ e) := hc.comp he
    simpa only [Function.comp_def, Set.domRestrict_def, globalLimit, limit,
      approximation, gridIndex, e] using hce
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  have hT' : t < (T : ℝ≥0) := by exact_mod_cast hT
  exact (hcont T).continuousAt
    (mem_of_superset (Iio_mem_nhds hT') Set.Iio_subset_Iic_self)

theorem globalLimit_agrees_grid (f : ℕ → ℕ → ℝ)
    (hcoh : ∀ n k, f (n + 1) (2 * k) = f n k)
    (hlocal : ∀ T : ℕ, ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f n (k + 1) - f n k| ≤ a n)
    (n k : ℕ) (t : ℝ≥0) (ht : (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n) :
    globalLimit f t = f n k := by
  obtain ⟨T, hT⟩ := exists_nat_gt (t : ℝ)
  obtain ⟨a, ha, hsum, hadj⟩ := hlocal T
  have hh := uniformContinuous_limit_of_eventually f a ha hsum hcoh hadj
  let x : Interval T := ⟨(t : ℝ), t.property, hT.le⟩
  exact limit_agrees_grid f (limit (T := T) f) hcoh hh.2.2 n k x ht

theorem measurable_globalLimit_eval {Ω : Type u_3} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k))
    (t : ℝ≥0) : Measurable (fun ω => globalLimit (f ω) t) := by
  exact (MeasureTheory.StronglyMeasurable.limUnder
    (fun n => (hf n ⌊(2 : ℝ) ^ n * (t : ℝ)⌋₊).stronglyMeasurable)).measurable

theorem measurable_globalLimit {Ω : Type u_4} [MeasurableSpace Ω]
    (f : Ω → ℕ → ℕ → ℝ) (hf : ∀ n k, Measurable (fun ω => f ω n k)) :
    Measurable (fun ω => globalLimit (f ω)) :=
  Measurable.of_eval (fun t => measurable_globalLimit_eval f hf t)

theorem ae_globalLimit_properties {Ω : Type u_5} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (f : Ω → ℕ → ℕ → ℝ)
    (hcoh : ∀ᵐ ω ∂P, ∀ n k, f ω (n + 1) (2 * k) = f ω n k)
    (hlocal : ∀ T : ℕ, ∀ᵐ ω ∂P, ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧ Summable a ∧
      ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n → |f ω n (k + 1) - f ω n k| ≤ a n) :
    ∀ᵐ ω ∂P, Continuous (globalLimit (f ω)) ∧
      ∀ (n k : ℕ) (t : ℝ≥0), (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n →
        globalLimit (f ω) t = f ω n k := by
  filter_upwards [hcoh, MeasureTheory.ae_all_iff.mpr hlocal] with ω hc hl
  exact ⟨continuous_globalLimit (f ω) hc hl,
    fun n k t ht => globalLimit_agrees_grid (f ω) hc hl n k t ht⟩

theorem ae_globalLimit_properties_of_eventually {Ω : Type u_6} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (f : Ω → ℕ → ℕ → ℝ) (a : ℕ → ℕ → ℝ)
    (ha : ∀ T n, 0 ≤ a T n) (hsum : ∀ T, Summable (a T))
    (hcoh : ∀ᵐ ω ∂P, ∀ n k, f ω (n + 1) (2 * k) = f ω n k)
    (hadj : ∀ T : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ k, k < T * 2 ^ n → |f ω n (k + 1) - f ω n k| ≤ a T n) :
    ∀ᵐ ω ∂P, Continuous (globalLimit (f ω)) ∧
      ∀ (n k : ℕ) (t : ℝ≥0), (t : ℝ) = (k : ℝ) / (2 : ℝ) ^ n →
        globalLimit (f ω) t = f ω n k := by
  apply ae_globalLimit_properties P f hcoh
  intro T
  filter_upwards [hadj T] with ω hω
  exact ⟨a T, ha T, hsum T, hω⟩

end Problem336AdditiveD139.LocalDyadicContinuity

end

end OAI
