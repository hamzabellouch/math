import Mathlib

namespace OAI

section
section
namespace DilutedSpinGlass.BooleanPolynomial
open scoped BigOperators
variable {R : Type} [Fintype R] [DecidableEq R]

noncomputable def truth (b : Bool) : ℝ := if b then 1 else 0
noncomputable def monomial (s : Finset R) (y : R → Bool) : ℝ := ∏ r ∈ s, truth (y r)
noncomputable def coefficient (F : (R → Bool) → ℝ) (s : Finset R) : ℝ :=
  ∑ x : R → Bool, F x * (∏ r ∈ s, if x r then (1:ℝ) else -1) *
    (∏ r ∈ sᶜ, if x r then (0:ℝ) else 1)

lemma interpolation (F : (R → Bool) → ℝ) (y : R → Bool) :
    F y = ∑ x : R → Bool, F x * ∏ r, (if x r then truth (y r) else 1-truth (y r)) := by
  classical
  symm
  rw [Finset.sum_eq_single y]
  · have he : ∏ r, (if y r then truth (y r) else 1-truth (y r)) = (1:ℝ) := by
      apply Finset.prod_eq_one
      intro r _
      cases y r <;> norm_num [truth]
    rw [he,mul_one]
  · intro x _ hxy
    have hx : ∃ r, x r ≠ y r := not_forall.mp (fun h => hxy (funext h))
    obtain ⟨r,hr⟩ := hx
    have he : ∏ j, (if x j then truth (y j) else 1-truth (y j)) = (0:ℝ) := by
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      cases hx : x r <;> cases hy : y r <;> simp_all [truth]
    rw [he,mul_zero]
  · simp

lemma product_expansion (x y : R → Bool) :
    (∏ r, (if x r then truth (y r) else 1-truth (y r))) =
      ∑ s : Finset R, ((∏ r ∈ s, if x r then (1:ℝ) else -1) *
        (∏ r ∈ sᶜ, if x r then (0:ℝ) else 1)) * monomial s y := by
  have he (r : R) : (if x r then truth (y r) else 1-truth (y r)) =
      ((if x r then (1:ℝ) else -1) * truth (y r)) + (if x r then (0:ℝ) else 1) := by
    cases x r <;> simp; ring
  simp_rw [he]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib]
  unfold monomial
  ring

/-- Every predicate of a finite sharing profile is a finite real linear
combination of positive sharing requirements. No endpoint mark is needed. -/
theorem expansion (F : (R → Bool) → ℝ) (y : R → Bool) :
    F y = ∑ s : Finset R, coefficient F s * monomial s y := by
  rw [interpolation F y]
  simp_rw [product_expansion,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

end DilutedSpinGlass.BooleanPolynomial
end

end

section
section
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

/-- The exact probe sequence of pert:parameters, indexed from zero. -/
noncomputable def extractionProbe (j : ℕ) : ℝ := 1 / ((j:ℝ)+4)

theorem extractionProbe_pos (j : ℕ) : 0 < extractionProbe j := by
  unfold extractionProbe
  positivity

theorem extractionProbe_le_half (j : ℕ) : extractionProbe j ≤ 1/2 := by
  unfold extractionProbe
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  linarith

theorem extractionProbe_tendsto : Tendsto extractionProbe atTop (𝓝 0) := by
  have hh : Tendsto (fun j : ℕ => (j:ℝ)+4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  change Tendsto (fun j : ℕ => 1 / ((j:ℝ)+4)) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hh

/-- Real finite-remainder extraction. This avoids both a complex normal-family
argument and a subsequence of limiting coefficients: all coefficients tend to
zero directly. The same base function is tested at every probe, as required by
the Poisson add-one identity. -/
theorem coefficients_tendsto_zero_of_uniform_remainders
    (H : ℕ → ℝ → ℝ) (a : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (C : ℝ)
    (_hB : ∀ k, 0 ≤ B k) (hC : 0 ≤ C)
    (hR : ∀ N k t, t ∈ Icc (0:ℝ) (1/2) →
      |H N t - ∑ i ∈ Finset.range (k+1), a N i * t^i| ≤ B k * t^(k+1))
    (err : ℕ → ℕ → ℝ) (herr : ∀ j, Tendsto (err j) atTop (𝓝 0))
    (hsmall : ∀ j N, |H N (extractionProbe j)| ≤
      C * extractionProbe j ^ (j+4) + err j N) :
    ∀ k, Tendsto (fun N => a N k) atTop (𝓝 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hlim : Tendsto (fun j => (C+B k)*extractionProbe j) atTop (𝓝 0) := by
      simpa only [mul_zero] using extractionProbe_tendsto.const_mul (C+B k)
    have he : ∀ᶠ j in atTop, (C+B k)*extractionProbe j < ε/2 :=
      hlim.eventually (eventually_lt_nhds (half_pos hε))
    obtain ⟨j, hjk, hjε⟩ := ((eventually_ge_atTop k).and he).exists
    let t := extractionProbe j
    have htpos : 0 < t := extractionProbe_pos j
    have hthalf : t ≤ 1/2 := extractionProbe_le_half j
    have htone : t ≤ 1 := by linarith
    let lower (N : ℕ) := ∑ i ∈ Finset.range k, a N i * t^i
    have hlower : Tendsto lower atTop (𝓝 0) := by
      have hh := tendsto_finsetSum (Finset.range k) (fun i hi =>
        (ih i (Finset.mem_range.mp hi)).mul_const (t^i))
      simpa only [zero_mul, Finset.sum_const_zero] using hh
    have htail : Tendsto (fun N => (err j N + |lower N|) / t^k) atTop (𝓝 0) := by
      simpa only [abs_zero, add_zero, zero_div] using ((herr j).add hlower.abs).div_const (t^k)
    have hetail : ∀ᶠ N in atTop, (err j N + |lower N|) / t^k < ε/2 :=
      htail.eventually (eventually_lt_nhds (half_pos hε))
    obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hetail
    refine ⟨N₀, fun N hN => ?_⟩
    have hTaylor := hR N k t ⟨htpos.le,hthalf⟩
    have hsplit : ∑ i ∈ Finset.range (k+1), a N i*t^i = lower N + a N k*t^k := by
      rw [Finset.sum_range_succ]
    rw [hsplit] at hTaylor
    have hnorm : |a N k| * t^k ≤ |H N t| + B k*t^(k+1) + |lower N| := by
      have hh : a N k*t^k = H N t - (H N t-(lower N+a N k*t^k)) - lower N := by ring
      have htri := abs_sub (H N t - (H N t-(lower N+a N k*t^k))) (lower N)
      have htri₂ := abs_sub (H N t) (H N t-(lower N+a N k*t^k))
      rw [← hh, abs_mul, abs_of_nonneg (pow_nonneg htpos.le _)] at htri
      linarith
    have hpow : t^(j+4) ≤ t^(k+1) :=
      pow_le_pow_of_le_one htpos.le htone (by omega)
    have hbound : |a N k| ≤ (C+B k)*t + (err j N + |lower N|)/t^k := by
      apply (mul_le_mul_iff_left₀ (pow_pos htpos k)).mp
      calc
        |a N k| * t^k ≤ |H N t| + B k*t^(k+1) + |lower N| := hnorm
        _ ≤ (C+B k)*t^(k+1) + err j N + |lower N| := by
          have := hsmall j N
          have := mul_le_mul_of_nonneg_left hpow hC
          dsimp [t] at *
          linarith
        _ = ((C+B k)*t + (err j N+|lower N|)/t^k)*t^k := by
          rw [pow_succ]
          field_simp
          ring
    rw [Real.dist_eq, sub_zero]
    exact hbound.trans_lt (by linarith [hN₀ N hN])

end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass
open MeasureTheory
open scoped BigOperators

/-- Uniform finite Taylor remainders survive an arbitrary probability-space
average. This is a plain Bochner integral statement, not an analyticity axiom. -/
theorem integral_polynomial_remainder {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (F : Z → ℝ) (a : ℕ → Z → ℝ)
    (hF : Integrable F μ) (ha : ∀ j, Integrable (a j) μ) (k : ℕ) (t R : ℝ)
    (hR : ∀ z, |F z - ∑ j ∈ Finset.range (k+1), a j z*t^j| ≤ R) :
    |(∫ z, F z ∂μ) - ∑ j ∈ Finset.range (k+1), (∫ z, a j z ∂μ)*t^j| ≤ R := by
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1), a j z*t^j) μ :=
    integrable_finsetSum _ (fun j _ => (ha j).mul_const _)
  have he : (∫ z, (F z - ∑ j ∈ Finset.range (k+1), a j z*t^j) ∂μ) =
      (∫ z, F z ∂μ) - ∑ j ∈ Finset.range (k+1), (∫ z, a j z ∂μ)*t^j := by
    rw [integral_sub hF hs,integral_finsetSum _ (fun j _ => (ha j).mul_const _)]
    simp_rw [integral_mul_const]
  rw [← he,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun z => F z - ∑ j ∈ Finset.range (k+1), a j z*t^j)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hR z))

theorem integral_difference_bound {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (F G : Z → ℝ)
    (hF : Integrable F μ) (hG : Integrable G μ) {R : ℝ}
    (hR : ∀ z, |F z-G z| ≤ R) : |(∫ z, F z ∂μ)-(∫ z, G z ∂μ)| ≤ R := by
  rw [← integral_sub hF hG,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun z => F z-G z)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hR z))

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma limsup_sqrt_error_bound (a b e : ℕ → ℝ) {c : ℝ} (hc : 0<c)
    (ha0 : ∀ n, 0≤a n) (hb1 : ∀ n, b n≤1) (he : Tendsto e atTop (𝓝 0))
    (h : ∀ n, c*a n≤Real.sqrt (b n)+e n) :
    c*limsup a atTop≤Real.sqrt (limsup b atTop) := by
  have hcap (t : ℝ) (ht : 0<t) : c*limsup a atTop≤Real.sqrt (limsup b atTop+t)+t := by
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    have hbf : ∀ᶠ n in atTop, b n<limsup b atTop+t :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall hb1))
    have hab : ∀ᶠ n in atTop, a n≤(Real.sqrt (limsup b atTop+t)+t)/c := by
      filter_upwards [hef,hbf] with n hen hbn
      apply (le_div_iff₀ hc).mpr
      rw [mul_comm]
      exact (h n).trans (add_le_add (Real.sqrt_le_sqrt hbn.le) hen.le)
    have hl := limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently)) hab
    simpa only [mul_comm c] using (le_div_iff₀ hc).mp hl
  have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (limsup b atTop+t)+t) 0 := by fun_prop
  have ht := hcont.continuousWithinAt.tendsto (s := Ioi 0)
  have hh := ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))
  simpa using hh

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

lemma limsup_finite_linear_bound {ι : Type*} (s : Finset ι)
    (a : ℕ → ℝ) (f : ι → ℕ → ℝ) (c e : ι → ℝ)
    (hc : ∀ i∈s, 0 ≤ c i) (ha0 : ∀ n, 0 ≤ a n)
    (hf1 : ∀ i∈s, ∀ n, f i n ≤ 1)
    (hbound : ∀ n, a n ≤ ∑ i∈s, c i*(f i n+e i)) :
    limsup a atTop ≤ ∑ i∈s, c i*(limsup (f i) atTop+e i) := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      limsup a atTop ≤ ∑ i∈s, c i*(limsup (f i) atTop+t+e i) := by
    have hff : ∀ᶠ n in atTop, ∀ i∈s, f i n<limsup (f i) atTop+t := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro i hi
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht)
        (isBoundedUnder_of_eventually_le (Eventually.of_forall (hf1 i hi)))
    apply limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha0).frequently))
    filter_upwards [hff] with n hn
    apply (hbound n).trans
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (add_le_add (hn i hi).le le_rfl) (hc i hi))
  have hcont : ContinuousAt (fun t : ℝ => ∑ i∈s, c i*(limsup (f i) atTop+t+e i)) 0 := by
    fun_prop
  have ht : Tendsto (fun t : ℝ => ∑ i∈s, c i*(limsup (f i) atTop+t+e i)) (𝓝[>] 0)
      (𝓝 (∑ i∈s, c i*(limsup (f i) atTop+e i))) := by
    simpa using hcont.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall (fun t ht => hcap t ht))

/-- First take each fixed-grid limsup, then the grid limit, and only then
let the arbitrary regularity cutoff tend to zero. -/
lemma squeeze_triangle_grid_zero (a : ℕ → ℝ) (C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hC : 0 ≤ C) (b : ℝ → ℕ → ℝ)
    (hb : ∀ η, 0<η → Tendsto (b η) atTop (𝓝 (C*η)))
    (hbound : ∀ η, 0<η → ∀ n, a n ≤ b η n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(2*(C+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hcut : C*η<ε := by
    dsimp [η]
    have h : C/(2*(C+1))<1 := (div_lt_one (by positivity)).mpr (by linarith)
    calc
      C*(ε/(2*(C+1))) = ε*(C/(2*(C+1))) := by ring
      _ < ε*1 := mul_lt_mul_of_pos_left h hε
      _ = ε := mul_one ε
  obtain ⟨n,hn⟩ := (eventually_atTop.mp ((hb η hη).eventually (Iio_mem_nhds hcut)))
  refine ⟨n,fun m hm => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha m)]
  exact (hbound η hη m).trans_lt (hn m hm)

end DilutedSpinGlass

end

section
open scoped BigOperators

namespace DilutedSpinGlass.Pattern

/-- The manuscript's ±1 spin, represented by Bool. -/
def sign (s : Bool) : ℝ := if s then 1 else -1

@[simp] theorem abs_sign (s : Bool) : |sign s| = 1 := by cases s <;> norm_num [sign]
@[simp] theorem sign_sq (s : Bool) : sign s ^ 2 = 1 := by cases s <;> norm_num [sign]

theorem sign_indicator (s t : Bool) : 1 + sign s * sign t = if s=t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [sign]

noncomputable def character {ι : Type*} (S : Finset ι) (e : ι → Bool) : ℝ := ∏ i ∈ S, sign (e i)

@[simp] theorem abs_character {ι : Type*} (S : Finset ι) (e : ι → Bool) :
    |character S e| = 1 := by simp [character, Finset.abs_prod]

@[simp] theorem character_empty {ι : Type*} (e : ι → Bool) : character ∅ e = 1 := by
  simp [character]

/-- Fourier inversion kernel on replica-spin patterns. -/
theorem character_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (e f : ι → Bool) :
    (∑ S : Finset ι, character S e * character S f) =
      if e=f then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have hprod : (∑ S : Finset ι, character S e * character S f) =
      ∏ i : ι, (1 + sign (e i)*sign (f i)) := by
    rw [Finset.prod_one_add]
    simp only [character, ← Finset.prod_mul_distrib]
    apply Finset.sum_congr
    · ext S
      simp
    · intro S _
      rfl
  rw [hprod]
  simp_rw [sign_indicator]
  by_cases h : e=f
  · subst f
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, e i ≠ f i := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Moments include all replica subsets, not only pair overlaps. -/
noncomputable def moment {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ∑ e, P e * character S e

/-- Exact Walsh inversion for an arbitrary signed pattern mass. -/
theorem inversion {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → Bool) → ℝ) (e : ι → Bool) :
    P e = (∑ S : Finset ι, moment P S * character S e) / (2 : ℝ)^Fintype.card ι := by
  classical
  have hh : (∑ S : Finset ι, moment P S * character S e) =
      (2 : ℝ)^Fintype.card ι * P e := by
    simp only [moment, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, character_kernel]
    simp [mul_comm]
  rw [hh]
  have hne : (2 : ℝ)^Fintype.card ι ≠ 0 := by positivity
  field_simp

/-- The total variation discrepancy costs one per nonempty multioverlap.
Both masses have the same total, so the empty Fourier coefficient cancels. -/
theorem variation_le_moments {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → Bool) → ℝ) (htotal : ∑ e, P e = ∑ e, Q e) :
    (∑ e, |P e-Q e|) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S| := by
  classical
  let C := ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S|
  have hzero : moment P ∅ - moment Q ∅ = 0 := by simpa [moment] using sub_eq_zero.mpr htotal
  have hpoint (e : ι → Bool) : |P e-Q e| ≤ C / (2 : ℝ)^Fintype.card ι := by
    rw [inversion P e, inversion Q e, ← sub_div, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^Fintype.card ι)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      |∑ S : Finset ι, (moment P S-moment Q S)*character S e| ≤
        ∑ S : Finset ι, |(moment P S-moment Q S)*character S e| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S : Finset ι, |moment P S-moment Q S| := by simp [abs_mul]
      _ = C := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ∅), hzero]
        simp [C]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hne : (2 : ℝ)^Fintype.card ι ≠ 0 := by positivity
  have heq : (2 : ℝ)^Fintype.card ι * (C / (2 : ℝ)^Fintype.card ι) = C := by field_simp
  rw [heq] at h
  exact h

/-- Exact coordinatewise product telescoping, in a form usable for different
probability laws at different message labels. -/
theorem product_variation_step {α β : Type*} [Fintype α] [Fintype β]
    (P Q : α → ℝ) (U V : β → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hV : ∀ y, 0 ≤ V y)
    (hPt : ∑ x, P x = 1) (hVt : ∑ y, V y = 1) :
    (∑ x, ∑ y, |P x*U y-Q x*V y|) ≤
      (∑ x, |P x-Q x|) + ∑ y, |U y-V y| := by
  have hstep (x : α) (y : β) : |P x*U y-Q x*V y| ≤
      P x*|U y-V y| + |P x-Q x| *V y := by
    calc
      |P x*U y-Q x*V y| = |P x*(U y-V y)+(P x-Q x)*V y| := by ring_nf
      _ ≤ |P x*(U y-V y)| + |(P x-Q x)*V y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hP x), abs_of_nonneg (hV y)]
  calc
    _ ≤ ∑ x, ∑ y, (P x*|U y-V y| + |P x-Q x| *V y) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hstep x y))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hPt, hVt,
        mul_one, one_mul]
      ring

/-- Testing a spin pattern by a bounded observable costs twice the total variation. -/
theorem observable_variation {α : Type*} [Fintype α] (P Q f : α → ℝ)
    (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x, P x*f x)-(∑ x, Q x*f x)| ≤ ∑ x, |P x-Q x| := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hf x)))

end DilutedSpinGlass.Pattern

namespace DilutedSpinGlass.Pattern

/-- Tensorization with the sharp linear number of independent labels. -/
theorem product_variation {α : Type*} [Fintype α]
    (P Q : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPt : ∑ x, P x = 1) (hQt : ∑ x, Q x = 1) (a : ℕ) :
    (∑ x : Fin a → α, |(∏ i, P (x i))-(∏ i, Q (x i))|) ≤
      (a : ℝ) * ∑ x, |P x-Q x| := by
  classical
  induction a with
  | zero => simp
  | succ a ih =>
    have heq : (∑ x : Fin (a+1) → α, |(∏ i, P (x i))-(∏ i, Q (x i))|) =
        ∑ x : α, ∑ y : Fin a → α, |P x*(∏ i, P (y i))-Q x*(∏ i, Q (y i))| := by
      rw [← (Fin.consEquiv (fun _ : Fin (a+1) => α)).sum_comp, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [heq]
    have htot : (∑ y : Fin a → α, ∏ i, Q (y i)) = 1 := by
      rw [← Fintype.prod_sum]
      simp only [hQt, Finset.prod_const_one]
    have hstep := product_variation_step P Q (fun y : Fin a → α => ∏ i, P (y i))
      (fun y : Fin a → α => ∏ i, Q (y i)) hP
      (fun y => Finset.prod_nonneg (fun i _ => hQ (y i))) hPt htot
    push_cast
    nlinarith

/-- The deterministic empirical-pattern comparison in comp:patterns.
The hypotheses are probability masses, and the conclusion involves ALL
nonempty replica-subset moments, with no assumption of decorrelation. -/
theorem pattern_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : (ι → Bool) → ℝ) (hP : ∀ x, 0 ≤ P x) (hQ : ∀ x, 0 ≤ Q x)
    (hPt : ∑ x, P x = 1) (hQt : ∑ x, Q x = 1) (a : ℕ)
    (f : (Fin a → (ι → Bool)) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∑ x, (∏ i, P (x i))*f x)-(∑ x, (∏ i, Q (x i))*f x)| ≤
      (a : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅, |moment P S-moment Q S| := by
  apply (observable_variation _ _ f hf).trans
  apply (product_variation P Q hP hQ hPt hQt a).trans
  exact mul_le_mul_of_nonneg_left (variation_le_moments P Q (hPt.trans hQt.symm)) (by positivity)

/-- Empirical law of the replica pattern at a uniformly sampled site. -/
noncomputable def empirical {ι : Type*} [Fintype ι] {N : ℕ}
    (σ : Fin N → ι → Bool) (e : ι → Bool) : ℝ := by
  classical
  exact (∑ i : Fin N, if σ i=e then 1 else 0)/(N : ℝ)

theorem empirical_nonneg {ι : Type*} [Fintype ι] {N : ℕ} (σ : Fin N → ι → Bool) (e : ι → Bool) :
    0 ≤ empirical σ e := by unfold empirical; positivity

/-- The normalization uses N>=1, as required for reservoir sizes. -/
theorem empirical_total {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (hN : 0 < N)
    (σ : Fin N → ι → Bool) : (∑ e, empirical σ e) = 1 := by
  classical
  simp only [empirical, ← Finset.sum_div]
  rw [Finset.sum_comm]
  have hne : (N : ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self hne

 
theorem empirical_moment {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (σ : Fin N → ι → Bool) (S : Finset ι) :
    moment (empirical σ) S = (∑ i : Fin N, character S (σ i))/(N : ℝ) := by
  classical
  unfold moment empirical
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end DilutedSpinGlass.Pattern

open MeasureTheory

namespace DilutedSpinGlass.Pattern

variable {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem mass_le_one (P : α → ℝ) (hP : ∀ x, 0 ≤ P x) (hPt : ∑ x, P x = 1) (x : α) :
    P x ≤ 1 := by
  classical
  rw [← hPt]
  exact Finset.single_le_sum (fun i _ => hP i) (Finset.mem_univ x)

theorem mass_abs_average (P f : α → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hPt : ∑ x, P x = 1) (hf : ∀ x, |f x| ≤ 1) : |∑ x, P x*f x| ≤ 1 := by
  calc
    _ ≤ ∑ x, |P x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, P x := Finset.sum_le_sum (fun x _ => by
      rw [abs_mul, abs_of_nonneg (hP x)]
      exact mul_le_of_le_one_right (hP x) (hf x))
    _ = 1 := hPt

theorem bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

/-- The unconditional spin-pattern distribution, not a conditional law. -/
noncomputable def meanMass (P : Ω → α → ℝ) (x : α) : ℝ := ∫ ω, P ω x ∂μ

omit [Fintype α] [IsProbabilityMeasure μ] in
theorem meanMass_nonneg (P : Ω → α → ℝ) (hP : ∀ ω x, 0 ≤ P ω x) (x : α) :
    0 ≤ meanMass (μ := μ) P x := integral_nonneg (fun ω => hP ω x)

theorem meanMass_total (P : Ω → α → ℝ) (hm : ∀ x, Measurable (fun ω => P ω x))
    (hP : ∀ ω x, 0 ≤ P ω x) (hPt : ∀ ω, ∑ x, P ω x = 1) :
    ∑ x, meanMass (μ := μ) P x = 1 := by
  have hi (x : α) : Integrable (fun ω => P ω x) μ :=
    bounded_integrable (hm x) (fun ω => by
      rw [abs_of_nonneg (hP ω x)]
      exact mass_le_one (P ω) (hP ω) (hPt ω) x)
  change (∑ x, ∫ ω, P ω x ∂μ) = 1
  rw [← integral_finsetSum (Finset.univ) (fun x _ => hi x)]
  simp_rw [hPt]
  simp

/-- Averaging the empirical law reproduces the expected multioverlaps. -/
theorem meanMass_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Ω → (ι → Bool) → ℝ) (hm : ∀ x, Measurable (fun ω => P ω x))
    (hP : ∀ ω x, 0 ≤ P ω x) (hPt : ∀ ω, ∑ x, P ω x = 1) (S : Finset ι) :
    moment (meanMass (μ := μ) P) S = ∫ ω, moment (P ω) S ∂μ := by
  have hi (x : ι → Bool) : Integrable (fun ω => P ω x) μ :=
    bounded_integrable (hm x) (fun ω => by
      rw [abs_of_nonneg (hP ω x)]
      exact mass_le_one (P ω) (hP ω) (hPt ω) x)
  simp only [moment, meanMass, ← integral_mul_const]
  exact (integral_finsetSum Finset.univ (fun x _ => (hi x).mul_const _)).symm

/-- The integrated empirical-pattern comparison, valid for arbitrary reservoir
root laws. This is comp:pattern-error; conditioning on independent new
insertion disorder can subsequently be performed without changing the bound. -/
theorem expected_pattern_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Ω → (ι → Bool) → ℝ) (hm : ∀ x, Measurable (fun ω => P ω x))
    (hP : ∀ ω x, 0 ≤ P ω x) (hPt : ∀ ω, ∑ x, P ω x = 1)
    (a : ℕ) (f : (Fin a → (ι → Bool)) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(∫ ω, ∑ x, (∏ i, P ω (x i))*f x ∂μ) -
      (∑ x, (∏ i, meanMass (μ := μ) P (x i))*f x)| ≤
      (a : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        ∫ ω, |moment (P ω) S - ∫ ω', moment (P ω') S ∂μ| ∂μ := by
  classical
  let Q := meanMass (μ := μ) P
  let A (ω : Ω) := ∑ x, (∏ i, P ω (x i))*f x
  let B := ∑ x, (∏ i, Q (x i))*f x
  have hQ : ∀ x, 0 ≤ Q x := meanMass_nonneg P hP
  have hQt : ∑ x, Q x = 1 := meanMass_total P hm hP hPt
  have hA : Measurable A := by
    dsimp [A]
    fun_prop
  have hAb : ∀ ω, |A ω| ≤ 1 := by
    intro ω
    apply mass_abs_average _ f
      (fun x => Finset.prod_nonneg (fun i _ => hP ω (x i))) _ hf
    rw [← Fintype.prod_sum]
    simp only [hPt, Finset.prod_const_one]
  have hAi : Integrable A μ := bounded_integrable hA hAb
  have hmoment (S : Finset ι) : Measurable (fun ω => moment (P ω) S) := by
    unfold moment
    fun_prop
  have hmomentb (S : Finset ι) : ∀ ω, |moment (P ω) S| ≤ 1 := by
    intro ω
    exact mass_abs_average (P ω) (character S) (hP ω) (hPt ω) (fun x => (abs_character S x).le)
  have hdiff (S : Finset ι) : Integrable (fun ω => |moment (P ω) S-moment Q S|) μ :=
    ((bounded_integrable (hmoment S) (hmomentb S)).sub (integrable_const _)).abs
  have hp (ω : Ω) := pattern_replacement (P ω) Q (hP ω) hQ (hPt ω) hQt a f hf
  change |(∫ ω, A ω ∂μ) - B| ≤ _
  have hBc : (∫ _ : Ω, B ∂μ) = B := by simp
  rw [← hBc, ← integral_sub hAi (integrable_const B)]
  calc
    _ ≤ ∫ ω, |A ω-B| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (a : ℝ) * ∑ S ∈ (Finset.univ : Finset (Finset ι)).erase ∅,
        |moment (P ω) S-moment Q S| ∂μ := by
      apply integral_mono (hAi.sub (integrable_const B)).abs
        ((integrable_finsetSum _ (fun S _ => hdiff S)).const_mul (a : ℝ)) hp
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun S _ => hdiff S)]
      simp only [Q, meanMass_moment P hm hP hPt]

end DilutedSpinGlass.Pattern

end

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

lemma limsup_finite_bound {ι : Type*} (s : Finset ι)
    (a : ℕ → ℝ) (f : ι → ℕ → ℝ) (c : ι → ℝ) (b : ℝ)
    (hc : ∀ i∈s, 0≤c i) (ha : ∀ n, 0≤a n)
    (hf : ∀ i∈s, IsBoundedUnder (·≤·) atTop (f i))
    (h : ∀ n, a n≤b+∑ i∈s, c i*f i n) :
    limsup a atTop≤b+∑ i∈s, c i*limsup (f i) atTop := by
  classical
  have hcap (t : ℝ) (ht : 0<t) :
      limsup a atTop≤b+∑ i∈s, c i*(limsup (f i) atTop+t) := by
    have he : ∀ᶠ n in atTop, ∀ i∈s, f i n<limsup (f i) atTop+t := by
      apply (eventually_all_finite s.finite_toSet).mpr
      intro i hi
      exact eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht) (hf i hi)
    apply limsup_le_of_le
      (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha).frequently))
    filter_upwards [he] with n hn
    exact (h n).trans (add_le_add le_rfl (Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hn i hi).le (hc i hi))))
  have ht : Tendsto (fun t : ℝ => b+∑ i∈s, c i*(limsup (f i) atTop+t)) (𝓝[>] 0)
      (𝓝 (b+∑ i∈s, c i*limsup (f i) atTop)) := by
    have hh : ContinuousAt (fun t : ℝ => b+∑ i∈s, c i*(limsup (f i) atTop+t)) 0 := by fun_prop
    simpa using hh.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hcap)

/-- Uniform summable remainders commute with the ordered limsup/grid limits.
No diagonal exchange of the two limits is used. -/
lemma series_double_limit (a : ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℕ → ℝ)
    (c tail : ℕ → ℝ) (ha : ∀ L n, 0≤a L n)
    (hab : ∀ L, IsBoundedUnder (·≤·) atTop (a L))
    (hc : ∀ k, 0≤c k) (hf : ∀ k L, IsBoundedUnder (·≤·) atTop (f k L))
    (hflim : ∀ k, Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0))
    (htail : Tendsto tail atTop (𝓝 0))
    (h : ∀ K L n, a L n≤tail K+∑ k∈Finset.range K, c k*f k L n) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have ha0 (L : ℕ) : 0≤limsup (a L) atTop :=
    le_limsup_of_frequently_le ((Eventually.of_forall (ha L)).frequently) (hab L)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (htail.eventually (Iio_mem_nhds (show 0<ε/2 by positivity)))
  have hb (L : ℕ) := limsup_finite_bound (Finset.range K) (a L) (fun k => f k L) c (tail K)
    (fun k _ => hc k) (ha L) (fun k _ => hf k L) (h K L)
  have hl : Tendsto (fun L => tail K+∑ k∈Finset.range K, c k*limsup (f k L) atTop)
      atTop (𝓝 (tail K)) := by
    simpa using tendsto_const_nhds.add (tendsto_finsetSum (Finset.range K)
      (fun k _ => (hflim k).const_mul (c k)))
  have hte : tail K<ε := (hK K le_rfl).trans (by linarith)
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hl.eventually (Iio_mem_nhds hte))
  refine ⟨L, fun l hLl => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha0 l)]
  exact (hb l).trans_lt (hL l hLl)
end DilutedSpinGlass

end

end OAI
