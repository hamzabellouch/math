import OAI.Combinatorics.ProgressionColoring.SmallBoxAffinity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Rational paths from a closest return

The representatives are real vectors with explicitly integral errors along an
arithmetic progression. The minimal return to a half-open rectangular box
forces the integral numerator of the return to be primitive. The proof uses
the actual intermediate sample and uniqueness in a fundamental interval.
-/

universe uIndex

namespace QuantitativeVanDerWaerden

/-- Two representatives in the same half-open fundamental interval cannot
differ by a nonzero integer. -/
theorem eq_of_integer_difference_in_fundamental_interval {a x y : ℝ}
    (hx : a ≤ x ∧ x < a + 1) (hy : a ≤ y ∧ y < a + 1)
    (hint : ∃ z : ℤ, x - y = z) : x = y := by
  obtain ⟨z, hz⟩ := hint
  have hsmall : |(z : ℝ)| < 1 := by
    rw [← hz, abs_lt]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hzero := integer_zero_of_abs_lt_one hsmall
  rw [hzero, Int.cast_zero] at hz
  exact sub_eq_zero.mp hz

/-- The intermediate point of a segment in a half-open interval remains in
that interval, including its left endpoint. -/
theorem divided_segment_mem_Ico {a b x y e : ℝ}
    (hx : a ≤ x ∧ x < b) (hy : a ≤ y ∧ y < b) (he : 1 ≤ e) :
    a ≤ x + (y - x) / e ∧ x + (y - x) / e < b := by
  have hepos : 0 < e := by linarith
  have hmul : e * ((y - x) / e) = y - x := mul_div_cancel₀ _ hepos.ne'
  have hxmul := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hx.1)
  have hxmul' := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hx.2.le)
  constructor
  · nlinarith [hy.1]
  · nlinarith [hy.2]

/-- An actual repeat gives an integral return numerator. -/
theorem exists_integer_return_numerator {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b : ι → ℝ) (j h : ℕ)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z) :
    ∃ T : ι → ℤ, ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i := by
  classical
  have hi : ∀ i, ∃ z : ℤ,
      (h : ℝ) * b i - (X (j + h) i - X j i) = z := by
    intro i
    obtain ⟨z₀, hz₀⟩ := hAP j i
    obtain ⟨z₁, hz₁⟩ := hAP (j + h) i
    refine ⟨z₀ - z₁, ?_⟩
    push_cast at hz₁ ⊢
    nlinarith
  choose T hT using hi
  exact ⟨T, hT⟩

/-- Reducing a return numerator modulo its positive denominator gives the
finite rational label and a coordinatewise integer change of the step. -/
theorem reduced_return_numerator {ι : Type uIndex} {h : ℕ} (hh : 0 < h)
    (T : ι → ℤ) (b u : ι → ℝ)
    (hT : ∀ i, (h : ℝ) * b i - u i = T i) :
    ∃ t : ι → ℤ, (∀ i, 0 ≤ t i ∧ t i < h) ∧
      (∀ i, ∃ z : ℤ, T i - t i = (h : ℤ) * z) ∧
      (∀ i, ∃ z : ℤ, b i - ((t i : ℝ) + u i) / h = z) := by
  refine ⟨fun i => T i % (h : ℤ), ?_, ?_, ?_⟩
  · intro i
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  · intro i
    exact ⟨T i / (h : ℤ), by linarith [Int.emod_add_mul_ediv (T i) (h : ℤ)]⟩
  · intro i
    refine ⟨T i / (h : ℤ), ?_⟩
    have hid : T i - T i % (h : ℤ) = (h : ℤ) * (T i / (h : ℤ)) := by
      linarith [Int.emod_add_mul_ediv (T i) (h : ℤ)]
    have hr : (T i : ℝ) - (T i % (h : ℤ) : ℤ) =
        (h : ℝ) * (T i / (h : ℤ) : ℤ) := by exact_mod_cast hid
    have hhR : (h : ℝ) ≠ 0 := by positivity
    have hquot : ((T i % (h : ℤ) : ℤ) + u i : ℝ) / h =
        b i - (T i / (h : ℤ) : ℤ) := by
      apply (div_eq_iff hhR).2
      nlinarith [hT i]
    rw [hquot]
    ring

/-- The rational step representation gives the full path modulo integers. -/
theorem rational_path_congr {ι : Type uIndex} {h : ℕ}
    (X : ℕ → ι → ℝ) (A b u : ι → ℝ) (t : ι → ℤ)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hstep : ∀ i, ∃ z : ℤ, b i - ((t i : ℝ) + u i) / h = z)
    (j : ℕ) (i : ι) :
    ∃ z : ℤ, X j i - A i - (j : ℝ) / h * ((t i : ℝ) + u i) = z := by
  obtain ⟨z₁, hz₁⟩ := hAP j i
  obtain ⟨z₂, hz₂⟩ := hstep i
  refine ⟨z₁ + j * z₂, ?_⟩
  calc
    _ = (X j i - A i - (j : ℝ) * b i) +
        (j : ℝ) * (b i - ((t i : ℝ) + u i) / h) := by ring
    _ = _ := by rw [hz₁, hz₂]; push_cast; ring

/-- A common divisor produces a genuine earlier return to the same box.
The hypotheses are the explicit arithmetic-progression errors and the
coordinate intervals; no intermediate return is assumed. -/
theorem divided_return_mem_box {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b f lo hi : ι → ℝ) (T : ι → ℤ)
    {j h e l k : ℕ} (he : 1 ≤ e) (hfactor : h = e * l)
    (hend : j + h < k)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hfund : ∀ n, n < k → ∀ i, f i ≤ X n i ∧ X n i < f i + 1)
    (hleft : ∀ i, lo i ≤ X j i ∧ X j i < hi i)
    (hright : ∀ i, lo i ≤ X (j + h) i ∧ X (j + h) i < hi i)
    (hT : ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i)
    (hdiv : ∀ i, (e : ℤ) ∣ T i) :
    ∀ i, lo i ≤ X (j + l) i ∧ X (j + l) i < hi i := by
  have hel : l ≤ h := by nlinarith
  have hej : j < k := by omega
  have hen : j + l < k := by omega
  have heR : 1 ≤ (e : ℝ) := by exact_mod_cast he
  have hepos : 0 < (e : ℝ) := by linarith
  intro i
  let u := X (j + h) i - X j i
  let C := X j i + u / e
  have hCbox : lo i ≤ C ∧ C < hi i :=
    divided_segment_mem_Ico (hleft i) (hright i) heR
  have hCfund : f i ≤ C ∧ C < f i + 1 :=
    divided_segment_mem_Ico (hfund j hej i) (hfund (j + h) hend i) heR
  obtain ⟨s, hs⟩ := hdiv i
  have hfactorR : (h : ℝ) = (e : ℝ) * l := by exact_mod_cast hfactor
  have hsR : (T i : ℝ) = (e : ℝ) * s := by exact_mod_cast hs
  have hquot : u / (e : ℝ) = (l : ℝ) * b i - s := by
    apply (div_eq_iff hepos.ne').2
    dsimp [u]
    have hTi := hT i
    rw [hfactorR, hsR] at hTi
    nlinarith [hTi]
  obtain ⟨z₀, hz₀⟩ := hAP j i
  obtain ⟨z₁, hz₁⟩ := hAP (j + l) i
  have hcongr : ∃ z : ℤ, X (j + l) i - C = z := by
    refine ⟨z₁ - z₀ + s, ?_⟩
    dsimp only [C]
    rw [hquot]
    push_cast at hz₁ ⊢
    nlinarith
  have heq := eq_of_integer_difference_in_fundamental_interval
    (hfund (j + l) hen i) hCfund hcongr
  rwa [heq]

/-- Minimality of the positive return prohibits every common divisor greater
than one of its integral numerator and its denominator. -/
theorem primitive_of_minimal_box_return {ι : Type uIndex}
    (X : ℕ → ι → ℝ) (A b f lo hi : ι → ℝ) (T : ι → ℤ)
    {j h k : ℕ} (hh : 0 < h) (hend : j + h < k)
    (hAP : ∀ n i, ∃ z : ℤ, X n i - A i - (n : ℝ) * b i = z)
    (hfund : ∀ n, n < k → ∀ i, f i ≤ X n i ∧ X n i < f i + 1)
    (hleft : ∀ i, lo i ≤ X j i ∧ X j i < hi i)
    (hright : ∀ i, lo i ≤ X (j + h) i ∧ X (j + h) i < hi i)
    (hT : ∀ i, (h : ℝ) * b i - (X (j + h) i - X j i) = T i)
    (hmin : ∀ l, 0 < l → l < h →
      ¬ ∀ i, lo i ≤ X (j + l) i ∧ X (j + l) i < hi i) :
    ∀ e : ℕ, e ∣ h → (∀ i, (e : ℤ) ∣ T i) → e ≤ 1 := by
  intro e he hdiv
  by_contra hlarge
  have hegt : 1 < e := by omega
  obtain ⟨l, hfactor⟩ := he
  have hl : 0 < l := by nlinarith
  have hlh : l < h := by nlinarith
  exact hmin l hl hlh (divided_return_mem_box X A b f lo hi T hegt.le
    hfactor hend hAP hfund hleft hright hT hdiv)

end QuantitativeVanDerWaerden

end OAI
