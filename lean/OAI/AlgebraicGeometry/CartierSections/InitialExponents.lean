import OAI.AlgebraicGeometry.CartierSections.Weights
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

namespace OAI

/-!
# Initial exponents of algebraic power series

The algebraic relation bounds initial exponents uniformly in the weights. Generic positive
perturbations extend this bound to least faces of nonnegative weights, as used in the
logarithmic jet argument of *Uniform Cartier sections for Fano-type contractions*.
-/

open scoped BigOperators

namespace CartierSections

section Leading
variable {ι k : Type*} [Fintype ι] [CommRing k]

/-- A nonzero coefficient of least real weight. -/
def IsInitialExponent (w : ι → ℝ) (f : MvPowerSeries ι k) (d : ι →₀ ℕ) : Prop :=
  MvPowerSeries.coeff d f ≠ 0 ∧
    ∀ e, MvPowerSeries.coeff e f ≠ 0 → realWeight w d ≤ realWeight w e

theorem exists_initial_exponent {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {f : MvPowerSeries ι k} (hf : f ≠ 0) :
    ∃ d, IsInitialExponent w f d := by
  classical
  obtain ⟨e, he⟩ : ∃ e, MvPowerSeries.coeff e f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext d
    simpa using h d
  let S := ((finite_weight_sublevel hw (realWeight w e)).toFinset).filter
    (fun d => MvPowerSeries.coeff d f ≠ 0)
  have heS : e ∈ S := by simp [S, he]
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image S (realWeight w) ⟨e, heS⟩
  have hd' : realWeight w d ≤ realWeight w e ∧ MvPowerSeries.coeff d f ≠ 0 := by
    simpa [S] using hd
  refine ⟨d, hd'.2, ?_⟩
  intro a ha
  by_cases hwa : realWeight w a ≤ realWeight w e
  · exact hmin a (by simp [S, hwa, ha])
  · exact hd'.1.trans (le_of_lt (lt_of_not_ge hwa))

theorem IsInitialExponent.unique {w : ι → ℝ} (hw : Function.Injective (realWeight w))
    {f : MvPowerSeries ι k} {d e : ι →₀ ℕ}
    (hd : IsInitialExponent w f d) (he : IsInitialExponent w f e) : d = e :=
  hw (le_antisymm (hd.2 e he.1) (he.2 d hd.1))

theorem IsInitialExponent.coeff_eq_zero {w : ι → ℝ} {f : MvPowerSeries ι k}
    {d e : ι →₀ ℕ} (hd : IsInitialExponent w f d)
    (he : realWeight w e < realWeight w d) : MvPowerSeries.coeff e f = 0 := by
  by_contra h
  exact (not_le_of_gt he) (hd.2 e h)

/-- Rationally independent weights prevent cancellation of initial terms. -/
theorem coeff_mul_initial {w : ι → ℝ} (hw : Function.Injective (realWeight w))
    {f g : MvPowerSeries ι k} {d e : ι →₀ ℕ}
    (hd : IsInitialExponent w f d) (he : IsInitialExponent w g e) :
    MvPowerSeries.coeff (d + e) (f * g) =
      MvPowerSeries.coeff d f * MvPowerSeries.coeff e g := by
  classical
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_single_of_mem (d, e) (by simp)
  rintro ⟨a, b⟩ hab hne
  have hsum : a + b = d + e := by simpa using hab
  by_cases ha : MvPowerSeries.coeff a f = 0
  · simp [ha]
  by_cases hb : MvPowerSeries.coeff b g = 0
  · simp [hb]
  have hwa := hd.2 a ha
  have hwb := he.2 b hb
  have heq := congrArg (realWeight w) hsum
  simp only [realWeight_add] at heq
  have had : a = d := hw (by linarith)
  have hbe : b = e := hw (by linarith)
  exact False.elim (hne (by simp [had, hbe]))

theorem IsInitialExponent.mul [IsDomain k] {w : ι → ℝ}
    (hw : Function.Injective (realWeight w))
    {f g : MvPowerSeries ι k} {d e : ι →₀ ℕ}
    (hd : IsInitialExponent w f d) (he : IsInitialExponent w g e) :
    IsInitialExponent w (f * g) (d + e) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [coeff_mul_initial hw hd he]
    exact mul_ne_zero hd.1 he.1
  · intro a ha
    rw [MvPowerSeries.coeff_mul] at ha
    obtain ⟨⟨b, c⟩, hbc, hcoef⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    have hsum : b + c = a := by simpa using hbc
    have hb : MvPowerSeries.coeff b f ≠ 0 := left_ne_zero_of_mul hcoef
    have hc : MvPowerSeries.coeff c g ≠ 0 := right_ne_zero_of_mul hcoef
    rw [← hsum, realWeight_add, realWeight_add]
    exact add_le_add (hd.2 b hb) (he.2 c hc)

theorem initial_one [Nontrivial k] {w : ι → ℝ} :
    IsInitialExponent w (1 : MvPowerSeries ι k) 0 := by
  classical
  refine ⟨by simp, ?_⟩
  intro e he
  have : e = 0 := by simpa [MvPowerSeries.coeff_one] using he
  subst e
  exact le_rfl

theorem IsInitialExponent.pow [IsDomain k] {w : ι → ℝ}
    (hw : Function.Injective (realWeight w))
    {f : MvPowerSeries ι k} {d : ι →₀ ℕ} (hd : IsInitialExponent w f d) (n : ℕ) :
    IsInitialExponent w (f ^ n) (n • d) := by
  induction n with
  | zero => simpa using (initial_one (k := k) (w := w))
  | succ n ih => simpa [pow_succ, add_nsmul] using ih.mul hw hd

end Leading

section AlgebraicDegree
variable {ι k J : Type*} [Fintype ι] [CommRing k]

/-- A vanishing finite sum with a nonzero term has two terms with the same
minimal exponent, for injective real weights. This follows by cancellation at the least-weight coefficient. -/
theorem initial_tie_of_sum_eq_zero (w : ι → ℝ)
    (hw : Function.Injective (realWeight w))
    (s : Finset J) (F : J → MvPowerSeries ι k) (d : J → (ι →₀ ℕ))
    (hlead : ∀ j ∈ s, F j ≠ 0 → IsInitialExponent w (F j) (d j))
    (hnonzero : ∃ j ∈ s, F j ≠ 0) (hsum : ∑ j ∈ s, F j = 0) :
    ∃ j ∈ s, ∃ l ∈ s, j ≠ l ∧ F j ≠ 0 ∧ F l ≠ 0 ∧ d j = d l := by
  classical
  let t := s.filter (fun j => F j ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨j, hj, hFj⟩ := hnonzero
    exact ⟨j, by simp [t, hj, hFj]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image t (fun j => realWeight w (d j)) ht
  have hj' : j ∈ s ∧ F j ≠ 0 := by simpa [t] using hj
  have hcoef := (hlead j hj'.1 hj'.2).1
  have hs : ∑ l ∈ s, MvPowerSeries.coeff (d j) (F l) = 0 := by
    simpa only [map_sum, map_zero] using congrArg (MvPowerSeries.coeff (d j)) hsum
  obtain ⟨l, hl, hlj, hlcoef⟩ :
      ∃ l ∈ s, l ≠ j ∧ MvPowerSeries.coeff (d j) (F l) ≠ 0 := by
    by_contra h
    push Not at h
    have heq : ∑ l ∈ s, MvPowerSeries.coeff (d j) (F l) =
        MvPowerSeries.coeff (d j) (F j) :=
      Finset.sum_eq_single_of_mem j hj'.1 (fun l hl hlj => h l hl hlj)
    exact hcoef (heq.symm.trans hs)
  have hlzero : F l ≠ 0 := by intro hz; simp [hz] at hlcoef
  have hljw := (hlead l hl hlzero).2 (d j) hlcoef
  have hjlw := hmin l (by simp [t, hl, hlzero])
  exact ⟨j, hj'.1, l, hl, Ne.symm hlj, hj'.2, hlzero, hw (le_antisymm hjlw hljw)⟩

noncomputable def exponentDegree (d : ι →₀ ℕ) : ℕ := ∑ i, d i

@[simp] theorem exponentDegree_add (d e : ι →₀ ℕ) :
    exponentDegree (d + e) = exponentDegree d + exponentDegree e := by
  simp [exponentDegree, Finset.sum_add_distrib]

@[simp] theorem exponentDegree_nsmul (n : ℕ) (d : ι →₀ ℕ) :
    exponentDegree (n • d) = n * exponentDegree d := by
  simp [exponentDegree, Finset.mul_sum]

theorem initial_polynomial_degree_le {w : ι → ℝ} {p : MvPolynomial ι k}
    {d : ι →₀ ℕ} (hd : IsInitialExponent w (p : MvPowerSeries ι k) d) :
    exponentDegree d ≤ p.totalDegree := by
  have hc : p.coeff d ≠ 0 := by simpa using hd.1
  simpa [exponentDegree, Finsupp.sum_fintype] using
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc))

/-- Every initial exponent of a nonzero algebraic power series has degree
bounded by the degrees of the polynomial coefficients of its algebraic
relation. The bound is independent of the choice of positive rationally
independent weights. This algebraic degree estimate bounds the jets in the logarithmic jet argument. -/
theorem algebraic_initial_degree_le [IsDomain k]
    {w : ι → ℝ} (hwpos : ∀ i, 0 < w i) (hw : LinearIndependent ℚ w)
    {f : MvPowerSeries ι k} {γ : ι →₀ ℕ}
    (hγ : IsInitialExponent w f γ)
    (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N)
    (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * f ^ j = 0) :
    exponentDegree γ ≤ N := by
  classical
  have hwI := realWeight_injective hw
  have hf : f ≠ 0 := by intro h; simpa [h] using hγ.1
  have hp : ∀ j, p j ≠ 0 → (p j : MvPowerSeries ι k) ≠ 0 := by
    intro j hj h
    apply hj
    ext d
    simpa using congrArg (MvPowerSeries.coeff d) h
  let δ : ℕ → (ι →₀ ℕ) := fun j =>
    if h : p j ≠ 0 then (exists_initial_exponent hwpos (hp j h)).choose else 0
  have hδ : ∀ j, p j ≠ 0 → IsInitialExponent w (p j : MvPowerSeries ι k) (δ j) := by
    intro j hj
    dsimp [δ]
    simp only [dite_eq_left hj]
    exact (exists_initial_exponent hwpos (hp j hj)).choose_spec
  let F : ℕ → MvPowerSeries ι k := fun j => (p j : MvPowerSeries ι k) * f ^ j
  have hFzero : ∀ j, F j ≠ 0 ↔ p j ≠ 0 := by
    intro j
    constructor
    · intro h hj
      apply h
      simp [F, hj]
    · intro h
      exact mul_ne_zero (hp j h) (pow_ne_zero _ hf)
  have hlead : ∀ j ∈ s, F j ≠ 0 →
      IsInitialExponent w (F j) (δ j + j • γ) := by
    intro j _ hj
    exact (hδ j ((hFzero j).mp hj)).mul hwI (hγ.pow hwI j)
  have hFnz : ∃ j ∈ s, F j ≠ 0 := by
    obtain ⟨j, hj, hpj⟩ := hnonzero
    exact ⟨j, hj, (hFzero j).mpr hpj⟩
  obtain ⟨j, hj, l, hl, hjl, hFj, hFl, heq⟩ :=
    initial_tie_of_sum_eq_zero w hwI s F (fun j => δ j + j • γ)
      hlead hFnz hrelation
  have hδj := (initial_polynomial_degree_le (hδ j ((hFzero j).mp hFj))).trans (hdeg j hj)
  have hδl := (initial_polynomial_degree_le (hδ l ((hFzero l).mp hFl))).trans (hdeg l hl)
  have heq' := congrArg exponentDegree heq
  simp only [exponentDegree_add, exponentDegree_nsmul] at heq'
  rcases lt_or_gt_of_ne hjl with hlt | hgt
  · have hmult := Nat.mul_le_mul_right (exponentDegree γ) (Nat.succ_le_of_lt hlt)
    nlinarith
  · have hmult := Nat.mul_le_mul_right (exponentDegree γ) (Nat.succ_le_of_lt hgt)
    nlinarith

end AlgebraicDegree

section GenericWeights

/-- Any finite family of nonempty real intervals contains a rationally
independent tuple. The proof uses countability of a finite rational span. -/
theorem exists_independent_fin_box (n : ℕ) (l u : Fin n → ℝ)
    (hlu : ∀ i, l i < u i) :
    ∃ w : Fin n → ℝ, LinearIndependent ℚ w ∧ ∀ i, l i < w i ∧ w i < u i := by
  induction n with
  | zero =>
      exact ⟨fun i => Fin.elim0 i, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨v, hv, hvbox⟩ := ih (fun i => l i.succ) (fun i => u i.succ)
        (fun i => hlu i.succ)
      have hcount : (↑(Submodule.span ℚ (Set.range v)) : Set ℝ).Countable :=
        Set.countable_coe_iff.mp (inferInstance : Countable (Submodule.span ℚ (Set.range v)))
      obtain ⟨x, hxl, hxu, hx⟩ :
          ∃ x, l 0 < x ∧ x < u 0 ∧ x ∉ Submodule.span ℚ (Set.range v) := by
        by_contra h
        push Not at h
        have hc : (Set.Ioo (l 0) (u 0)).Countable := hcount.mono (fun x hx => h x hx.1 hx.2)
        exact (not_le_of_gt (hlu 0)) (Cardinal.Real.Ioo_countable_iff.mp hc)
      refine ⟨Fin.cons x v, hv.finCons hx, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using And.intro hxl hxu
      · simpa using hvbox j

theorem exists_independent_box {ι : Type*} [Fintype ι] (l u : ι → ℝ)
    (hlu : ∀ i, l i < u i) :
    ∃ w : ι → ℝ, LinearIndependent ℚ w ∧ ∀ i, l i < w i ∧ w i < u i := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨v, hv, hvbox⟩ := exists_independent_fin_box (Fintype.card ι)
    (fun j => l (e.symm j)) (fun j => u (e.symm j)) (fun j => hlu (e.symm j))
  refine ⟨fun i => v (e i), hv.comp _ e.injective, ?_⟩
  intro i
  simpa using hvbox (e i)

end GenericWeights

section FaceDegree
variable {ι k : Type*} [Fintype ι] [CommRing k] [IsDomain k]

@[simp] theorem realWeight_one_eq_degree (d : ι →₀ ℕ) :
    realWeight (fun _ => 1) d = exponentDegree d := by
  simp [realWeight, exponentDegree, Nat.cast_sum]

theorem realWeight_mono {w v : ι → ℝ} (hwv : ∀ i, w i ≤ v i) (d : ι →₀ ℕ) :
    realWeight w d ≤ realWeight v d := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hwv i) (Nat.cast_nonneg _)

theorem realWeight_add_const (w : ι → ℝ) (t : ℝ) (d : ι →₀ ℕ) :
    realWeight (fun i => w i + t) d = realWeight w d + t * exponentDegree d := by
  simp [realWeight, exponentDegree, Nat.cast_sum, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- A useful exact small-perturbation bound. -/
theorem degree_perturbation_bound {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    0 < ε / (N + 1 : ℝ) ∧ ε / (N + 1 : ℝ) * N < ε := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  constructor
  · exact div_pos hε hN
  · have heq : ε / (N + 1 : ℝ) * (N + 1) = ε := div_mul_cancel₀ _ hN.ne'
    have hpos := div_pos hε hN
    nlinarith

/-- An algebraic power series has a coefficient of bounded total degree on
its least face for **every** nonnegative weight, including faces with zero
weights. This includes least faces with zero-weight transverse coordinates. -/
theorem exists_bounded_initial_exponent
    {f : MvPowerSeries ι k} (hf : f ≠ 0)
    (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N)
    (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * f ^ j = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ d, IsInitialExponent w f d ∧ exponentDegree d ≤ N := by
  classical
  have hfinite : {d : ι →₀ ℕ | exponentDegree d ≤ N}.Finite := by
    convert finite_weight_sublevel (w := fun _ : ι => (1 : ℝ)) (fun _ => zero_lt_one) (N : ℝ)
      using 1
    ext d
    simp only [Set.mem_ofPred_eq, realWeight_one_eq_degree, Nat.cast_le]
  let S := hfinite.toFinset.filter (fun d => MvPowerSeries.coeff d f ≠ 0)
  have memS (d : ι →₀ ℕ) : d ∈ S ↔ exponentDegree d ≤ N ∧ MvPowerSeries.coeff d f ≠ 0 := by
    simp [S]
  have hlead : ∀ v : ι → ℝ, (∀ i, 0 < v i) → LinearIndependent ℚ v →
      ∃ d, IsInitialExponent v f d ∧ exponentDegree d ≤ N := by
    intro v hvpos hv
    obtain ⟨d, hd⟩ := exists_initial_exponent hvpos hf
    exact ⟨d, hd, algebraic_initial_degree_le hvpos hv hd s p N hdeg hnonzero hrelation⟩
  have hS : S.Nonempty := by
    obtain ⟨v, hv, hvbox⟩ := exists_independent_box (fun _ : ι => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun _ => zero_lt_one)
    obtain ⟨d, hd, hdegree⟩ := hlead v (fun i => (hvbox i).1) hv
    exact ⟨d, (memS d).mpr ⟨hdegree, hd.1⟩⟩
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image S (realWeight w) hS
  have hd' := (memS d).mp hd
  refine ⟨d, ⟨hd'.2, ?_⟩, hd'.1⟩
  intro e he
  by_contra h
  have hgap : 0 < realWeight w d - realWeight w e := sub_pos.mpr (lt_of_not_ge h)
  let t := (realWeight w d - realWeight w e) / (exponentDegree e + 1 : ℝ)
  have ht : 0 < t ∧ t * exponentDegree e < realWeight w d - realWeight w e :=
    degree_perturbation_bound hgap _
  obtain ⟨v, hv, hvbox⟩ := exists_independent_box w (fun i => w i + t)
    (fun _ => lt_add_of_pos_right _ ht.1)
  obtain ⟨a, ha, hadegree⟩ := hlead v (fun i => (hw i).trans_lt (hvbox i).1) hv
  have hda := hmin a ((memS a).mpr ⟨hadegree, ha.1⟩)
  have hwa : realWeight w a ≤ realWeight v a := realWeight_mono (fun i => (hvbox i).1.le) a
  have hvle := ha.2 e he
  have hve : realWeight v e ≤ realWeight w e + t * exponentDegree e := by
    simpa only [realWeight_add_const] using
      realWeight_mono (fun i => (hvbox i).2.le) e
  linarith

noncomputable def partialDegree (B : Finset ι) (d : ι →₀ ℕ) : ℕ := ∑ i ∈ B, d i

theorem partialDegree_le (B : Finset ι) (d : ι →₀ ℕ) :
    partialDegree B d ≤ exponentDegree d := by
  classical
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem realWeight_sub_on [DecidableEq ι] (w : ι → ℝ) (B : Finset ι) (ε : ℝ) (d : ι →₀ ℕ) :
    realWeight (fun i => w i - if i ∈ B then ε else 0) d =
      realWeight w d - ε * partialDegree B d := by
  classical
  simp [realWeight, partialDegree, sub_mul, Finset.sum_sub_distrib, Nat.cast_sum,
    Finset.mul_sum, ite_mul]

/-- All exponents on a least face have bounded degree in the coordinates
whose weights are positive. A small generic perturbation gives the bound for every exponent on the face. -/
theorem algebraic_initial_partial_degree_le
    {f : MvPowerSeries ι k} (hf : f ≠ 0)
    (s : Finset ℕ) (p : ℕ → MvPolynomial ι k) (N : ℕ)
    (hdeg : ∀ j ∈ s, (p j).totalDegree ≤ N)
    (hnonzero : ∃ j ∈ s, p j ≠ 0)
    (hrelation : ∑ j ∈ s, (p j : MvPowerSeries ι k) * f ^ j = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (B : Finset ι) (hB : ∀ i ∈ B, 0 < w i)
    {d : ι →₀ ℕ} (hd : IsInitialExponent w f d) :
    partialDegree B d ≤ N := by
  classical
  by_cases hBempty : B = ∅
  · simp [partialDegree, hBempty]
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image B w (Finset.nonempty_iff_ne_empty.mpr hBempty)
  let ε := w i₀ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [hB i₀ hi₀]
  have hεw : ∀ i ∈ B, ε < w i := by
    intro i hi
    have hh := hmin i hi
    dsimp [ε]
    linarith [hB i₀ hi₀]
  let l : ι → ℝ := fun i => w i - if i ∈ B then ε else 0
  have hl : ∀ i, 0 ≤ l i := by
    intro i
    by_cases hi : i ∈ B
    · simp only [l, hi, ↓reduceIte]
      exact sub_nonneg.mpr (hεw i hi).le
    · simpa [l, hi] using hw i
  let t := ε / (exponentDegree d + 1 : ℝ)
  have ht : 0 < t ∧ t * exponentDegree d < ε := degree_perturbation_bound hε _
  obtain ⟨v, hv, hvbox⟩ := exists_independent_box l (fun i => l i + t)
    (fun _ => lt_add_of_pos_right _ ht.1)
  have hvpos : ∀ i, 0 < v i := fun i => (hl i).trans_lt (hvbox i).1
  obtain ⟨a, ha⟩ := exists_initial_exponent hvpos hf
  have hadegree := algebraic_initial_degree_le hvpos hv ha s p N hdeg hnonzero hrelation
  have hapart : partialDegree B a ≤ N := (partialDegree_le B a).trans hadegree
  have hbase := hd.2 a ha.1
  have hva := ha.2 d hd.1
  have hlower : realWeight w a - ε * partialDegree B a ≤ realWeight v a := by
    simpa only [l, realWeight_sub_on] using realWeight_mono (fun i => (hvbox i).1.le) a
  have hupper : realWeight v d ≤
      realWeight w d - ε * partialDegree B d + t * exponentDegree d := by
    simpa only [realWeight_add_const, l, realWeight_sub_on] using
      realWeight_mono (fun i => (hvbox i).2.le) d
  by_contra hN
  have hgap : (partialDegree B a : ℝ) + 1 ≤ partialDegree B d := by
    exact_mod_cast (show partialDegree B a + 1 ≤ partialDegree B d by omega)
  have hgapmul := mul_le_mul_of_nonneg_left hgap hε.le
  nlinarith [ht.2]

end FaceDegree

end CartierSections

end OAI
