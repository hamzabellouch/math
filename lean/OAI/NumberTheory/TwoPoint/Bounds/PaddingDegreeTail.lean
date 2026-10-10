import OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail
import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueTilt
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! The exact tilted padding law has mean at most `4 log L` eventually.
The finite exponential-moment bound gives the manuscript's `L^-100`
large-padding-degree error using the same fixed-modulus prime input. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma paddingPrimeSupply_split (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    paddingPrimeSupply E L = paddingPrimeSupply E 1 ∪
      modFivePrimeBand E false (Real.exp 1) (Real.exp L) := by
  have hfloor : ⌊Real.exp 1⌋₊ ≤ ⌊Real.exp L⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hL)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    obtain ⟨hp0, hpL⟩ := mem_Icc.mp hp
    apply mem_union.mpr
    by_cases hsmall : p ≤ ⌊Real.exp 1⌋₊
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hsmall⟩, hprime⟩, he⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpL⟩, hprime, he⟩)
  · intro hp
    apply Finset.mem_sdiff.mpr
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp, hprime⟩ := mem_filter.mp hp
      obtain ⟨hp0, hp1⟩ := mem_Icc.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hp1.trans hfloor⟩, hprime⟩, he⟩
    · obtain ⟨hp, hprime, he⟩ := mem_filter.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le p, (mem_Ioc.mp hp).2⟩, hprime⟩, he⟩

lemma paddingPrimeSupply_split_disjoint (E : Finset ℕ) (L : ℝ) :
    Disjoint (paddingPrimeSupply E 1)
      (modFivePrimeBand E false (Real.exp 1) (Real.exp L)) := by
  apply disjoint_left.mpr
  intro p hp hb
  have hp1 := (mem_Icc.mp (mem_filter.mp (Finset.mem_sdiff.mp hp).1).1).2
  have hp2 := (mem_Ioc.mp (mem_filter.mp hb).1).1
  omega

theorem ModFiveThetaInput.padding_reciprocal_mass (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑ p ∈ paddingPrimeSupply E L, 1 / (p : ℝ)) ≤ (3 / 4 : ℝ) * Real.log L + C := by
  obtain ⟨K, hK, hband⟩ := hP.band_error E
  refine ⟨(∑ p ∈ paddingPrimeSupply E 1, 1 / (p : ℝ)) + 4 * K,
    add_nonneg (sum_nonneg (fun _ _ => by positivity)) (by positivity), fun L hL => ?_⟩
  rw [paddingPrimeSupply_split E L hL, sum_union (paddingPrimeSupply_split_disjoint E L)]
  have hb := (abs_le.mp (hband false 1 L le_rfl hL)).2
  norm_num [modFiveDensity] at hb
  simp only [one_div]
  linarith

lemma padding_mean_le_reciprocal (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (∑ p : Q, 5 / ((p.val : ℝ) + 4)) ≤ 5 * ∑ p ∈ Q, 1 / (p : ℝ) := by
  rw [← sum_coe_sort Q (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
  apply sum_le_sum
  intro p _
  have hp : (0 : ℝ) < p.val := by exact_mod_cast (by have := hQ p p.property; omega : 0 < p.val)
  calc
    5 / ((p.val : ℝ) + 4) ≤ 5 / (p.val : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
    _ = _ := by ring

theorem ModFiveThetaInput.eventually_padding_mean (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p : paddingPrimeSupply E L, 5 / ((p.val : ℝ) + 4)) ≤ 4 * Real.log L := by
  obtain ⟨C, hC, hmass⟩ := hP.padding_reciprocal_mass E
  filter_upwards [eventually_ge_atTop (Real.exp (20 * C)), eventually_ge_atTop (1 : ℝ)]
    with L hLC hL
  have hlog : 20 * C ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLC
  have hh := padding_mean_le_reciprocal (paddingPrimeSupply E L)
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le)
  nlinarith [hmass L hL]

theorem ModFiveThetaInput.eventually_padding_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (paddingAvailableLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).probability
          (fun a => 400 * Real.log L < booleanCount a) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_mean E, eventually_ge_atTop (1 : ℝ)] with L hM hL
  let Q := paddingPrimeSupply E L
  have hQ : ∀ p ∈ Q, 2 ≤ p := fun _ hp => (paddingPrimeSupply_prime hp).two_le
  have hq0 (p : Q) : 0 ≤ 5 / ((p.val : ℝ) + 4) := by positivity
  have hq1 (p : Q) : 5 / ((p.val : ℝ) + 4) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast hQ p p.property
    linarith
  have hb := independent_boolean_tail (fun p : Q => 5 / ((p.val : ℝ) + 4)) hq0 hq1
    1 (4 * Real.log L) (400 * Real.log L) (by norm_num) hM
  change (paddingAvailableLaw Q hQ).probability _ ≤ _
  calc
    _ ≤ Real.exp ((Real.exp 1 - 1) * (4 * Real.log L) - 1 * (400 * Real.log L)) := hb
    _ ≤ Real.exp (-100 * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
      nlinarith [Real.exp_one_lt_three]
    _ = L ^ (-100 : ℝ) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hL)]
      congr 1
      ring

/-- The original uniform-residue expectation, with its literal padding
weight retained, has the same `L^-100` degree-deletion bound. -/
theorem ModFiveThetaInput.eventually_padding_residue_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (n : ℤ)
      (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B),
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            paddingTiltWeight _ (paddingResidueAvailable _ B n z) *
              if 400 * Real.log L < booleanCount (paddingResidueAvailable _ B n z)
              then 1 else 0) / paddingTiltNormalizer (paddingPrimeSupply E L) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_degree_tail E] with L hL
  intro B n hQB
  rw [padding_residue_tilt (paddingPrimeSupply E L) B
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le) hQB n
    (fun a => if 400 * Real.log L < booleanCount a then 1 else 0)]
  exact hL

end TwoPointCorrelations

end OAI
