import OAI.NumberTheory.EgyptianFractions.CeilResidue
import OAI.NumberTheory.EgyptianFractions.CyclicCeilingCount
import OAI.NumberTheory.EgyptianFractions.SimultaneousSelection
import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The ordinary normalized exponential sum, defined also at modulus zero.
All residue conclusions below explicitly require a positive modulus. -/
def residueFourierAverage {Ω : Type*} [Fintype Ω]
    (A : Ω → ℕ) (u l : ℕ) : ℂ :=
  (∑ ω : Ω, Complex.exp
    (2 * Real.pi * Complex.I * (l * A ω : ℕ) / (u : ℂ))) /
      (Fintype.card Ω : ℂ)

/-- An automatic-scale version of the positive exponential-average ceiling
count. The index type, rather than the image, counts repeated entries. -/
theorem ceiling_remainder_count_of_exp_average {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  apply ceiling_remainder_count_of_character_expect_automatic A δ hδ hsmall
  intro l hl hld
  simpa only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase,
    residueFourierAverage] using hfourier l hl hld

/-- The Fourier exception set for the deterministic high levels. -/
def highResidueExceptions {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m : ℝ) : Finset ℕ := by
  classical
  exact U.filter (fun u => ∃ l ∈ Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊,
    Real.exp (-3 * m / 10000) < ‖residueFourierAverage A u l‖)

/-- The exact frequency-union exponent is `-9m/1000`. This is stronger
than the `-m/1000` exception budget required by density descent. -/
theorem highResidueExceptions_card_bound {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m X : ℝ) (hX : 0 ≤ X)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖residueFourierAverage A u l‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ((highResidueExceptions U A m).card : ℝ) ≤ X * Real.exp (-9 * m / 1000) := by
  classical
  have hmarkov := card_exists_large_norm_le_of_moments U
    (Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊) (residueFourierAverage A)
    (Real.exp (-3 * m / 10000)) (X * Real.exp (-m / 100))
    (Real.exp_pos _) (fun l hl => hmoment l (Finset.mem_Icc.mp hl).1
      (Finset.mem_Icc.mp hl).2)
  have hcard : ((Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊).card : ℝ) ≤
      Real.exp (m / 2500) := by
    simpa using Nat.floor_le (Real.exp_pos (m / 2500)).le
  calc
    ((highResidueExceptions U A m).card : ℝ) ≤
        ((Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊).card : ℝ) *
          (X * Real.exp (-m / 100)) / Real.exp (-3 * m / 10000) ^ 2 := by
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hmarkov
      intro u hu
      simpa only [highResidueExceptions, Finset.mem_filter] using hu
    _ ≤ Real.exp (m / 2500) * (X * Real.exp (-m / 100)) /
        Real.exp (-3 * m / 10000) ^ 2 := by gcongr
    _ = X * Real.exp (-9 * m / 1000) := by
      have he : Real.exp (m / 2500) * Real.exp (-m / 100) /
          Real.exp (-3 * m / 10000) ^ 2 = Real.exp (-9 * m / 1000) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub]
        congr 1
        ring
      calc
        _ = X * (Real.exp (m / 2500) * Real.exp (-m / 100) /
            Real.exp (-3 * m / 10000) ^ 2) := by ring
        _ = _ := by rw [he]

/-- Outside the explicit exception set, every frequency needed by the cyclic
localization theorem satisfies the correct cubed-density bound. -/
theorem highResidueExceptions_fourier {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m : ℝ) {u : ℕ}
    (hu : u ∈ U) (hgood : u ∉ highResidueExceptions U A m) :
    ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / Real.exp (-m / 10000) ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ Real.exp (-m / 10000) ^ 3 := by
  classical
  have hfreq : 1 / Real.exp (-m / 10000) ^ 4 = Real.exp (m / 2500) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    ring
  have hthreshold : Real.exp (-m / 10000) ^ 3 = Real.exp (-3 * m / 10000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  intro l hl hld
  rw [hthreshold]
  apply le_of_not_gt
  intro hlarge
  apply hgood
  simp only [highResidueExceptions, Finset.mem_filter]
  exact ⟨hu, l, Finset.mem_Icc.mpr ⟨hl, by simpa [hfreq] using hld⟩, hlarge⟩

/-- Deterministic high-level residue distribution from its normalized second
moments. No cancellation or discrepancy hypothesis is hidden in the output:
the only input still needed is precisely the displayed second-moment bound. -/
theorem high_level_residues_of_second_moments {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m X : ℝ)
    (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hsmall : Real.exp (-m / 10000) ≤ 1 / 65536)
    (hupos : ∀ u ∈ U, 0 < u) (hubound : ∀ u ∈ U, (u : ℝ) ≤ X)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖residueFourierAverage A u l‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ∃ E : Finset ℕ, E ⊆ U ∧ (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
      ∀ u ∈ U, u ∉ E →
        (Real.exp (-m / 10000) / 2) * (Fintype.card Ω : ℝ) ≤
          ((Finset.univ.filter (fun ω =>
            ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) ≤
              Real.exp (-m / 10000) * X)).card : ℝ) := by
  classical
  refine ⟨highResidueExceptions U A m, ?_, ?_, ?_⟩
  · intro u hu
    simp only [highResidueExceptions, Finset.mem_filter] at hu
    exact hu.1
  · exact (highResidueExceptions_card_bound U A m X hX hmoment).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hX)
  · intro u hu hgood
    let : NeZero u := ⟨Nat.ne_of_gt (hupos u hu)⟩
    have hc := ceiling_remainder_count_of_exp_average A (Real.exp (-m / 10000))
      (Real.exp_pos _) hsmall (highResidueExceptions_fourier U A m hu hgood)
    apply hc.trans
    exact_mod_cast Finset.card_le_card (show
      Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) <
          Real.exp (-m / 10000) * u) ⊆
      Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) ≤
          Real.exp (-m / 10000) * X) from by
        intro ω hω
        obtain ⟨hω, hrem⟩ := Finset.mem_filter.mp hω
        exact Finset.mem_filter.mpr ⟨hω, hrem.le.trans
          (mul_le_mul_of_nonneg_left (hubound u hu) (Real.exp_pos _).le)⟩)

/-- The rational-ceiling convention in cyclic counts and the real-ceiling
convention in geometric descent specify exactly the same least residue. -/
theorem rational_ceiling_residue_lt_iff_fract_lt (u A : ℕ) (hu : 0 < u) (δ : ℝ) :
    ((u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A : ℕ) : ℝ) < δ * u ↔
      Int.fract (-(A : ℝ) / u) < δ := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  rw [ceiling_remainder_eq_neg_cast_val,
    ← natural_ceil_residue_eq_neg_zmod_val u A hu]
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u A hu
  exact residue_lt_iff_fract_lt hlt heq δ

/-- The direct fractional-part count needed by geometric residue families. -/
theorem fractional_residue_count_of_exp_average {Ω : Type*} [Fintype Ω]
    (A : Ω → ℕ) (u : ℕ) (hu : 0 < u) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => Int.fract (-(A ω : ℝ) / u) < δ)).card : ℝ) := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hc := ceiling_remainder_count_of_exp_average A δ hδ hsmall hfourier
  simpa only [rational_ceiling_residue_lt_iff_fract_lt u _ hu δ] using hc

/-- High-level distribution in exactly the fractional-part convention used
by geometric raw-density packaging. The exceptional set is independent of
the chosen residue index, and multiplicities are retained. -/
theorem high_level_fractional_residues_of_second_moments
    {Ω : Type*} [Fintype Ω] (U : Finset ℕ) (A : Ω → ℕ) (m X : ℝ)
    (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hsmall : Real.exp (-m / 10000) ≤ 1 / 65536)
    (hupos : ∀ u ∈ U, 0 < u)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖residueFourierAverage A u l‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ∃ E : Finset ℕ, E ⊆ U ∧ (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
      ∀ u ∈ U, u ∉ E →
        (Real.exp (-m / 10000) / 2) * (Fintype.card Ω : ℝ) ≤
          ((Finset.univ.filter (fun ω =>
            Int.fract (-(A ω : ℝ) / u) < Real.exp (-m / 10000))).card : ℝ) := by
  classical
  refine ⟨highResidueExceptions U A m, ?_, ?_, ?_⟩
  · intro u hu
    simp only [highResidueExceptions, Finset.mem_filter] at hu
    exact hu.1
  · exact (highResidueExceptions_card_bound U A m X hX hmoment).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hX)
  · intro u hu hgood
    exact fractional_residue_count_of_exp_average A u (hupos u hu)
      (Real.exp (-m / 10000)) (Real.exp_pos _) hsmall
      (highResidueExceptions_fourier U A m hu hgood)

/-- Finset-indexed form, matching the deterministic second-moment interface.
Repeated values of `A` remain distinct indices of `T`. -/
theorem high_level_fractional_residues_finset
    {ι : Type*} (T : Finset ι) (A : ι → ℕ) (U : Finset ℕ) (m X : ℝ)
    (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hsmall : Real.exp (-m / 10000) ≤ 1 / 65536)
    (hupos : ∀ u ∈ U, 0 < u)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖(∑ i ∈ T, Complex.exp
        (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))) /
          (T.card : ℂ)‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ∃ E : Finset ℕ, E ⊆ U ∧ (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
      ∀ u ∈ U, u ∉ E →
        (Real.exp (-m / 10000) / 2) * (T.card : ℝ) ≤
          ((T.filter (fun i =>
            Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card : ℝ) := by
  classical
  have he (u l : ℕ) : residueFourierAverage (fun i : T => A i) u l =
      (∑ i ∈ T, Complex.exp
        (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))) /
          (T.card : ℂ) := by
    unfold residueFourierAverage
    rw [Finset.sum_coe_sort T (fun i => Complex.exp
      (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))), Fintype.card_coe]
  obtain ⟨E, hEU, hEc, hE⟩ := high_level_fractional_residues_of_second_moments
    U (fun i : T => A i) m X hm hX hsmall hupos (by
      intro l hl hlH
      simpa only [he] using hmoment l hl hlH)
  refine ⟨E, hEU, hEc, ?_⟩
  intro u hu hgood
  have hcard : (Finset.univ.filter (fun i : T =>
      Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card =
      (T.filter (fun i => Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort T (fun i =>
      if Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000) then 1 else 0)
  simpa only [Fintype.card_coe, hcard] using hE u hu hgood

/-- The only small-density cutoff in the finite discrepancy argument holds
uniformly at the canonical prime-product scale. -/
theorem eventually_high_residue_localization_scale :
    ∀ᶠ S : ℝ in atTop,
      Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) ≤ 1 / 65536 := by
  have ht : Tendsto
      (fun S : ℝ => Real.exp (-((ResidueLevels.scale S : ℝ) / 10000)))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ResidueLevels.tendsto_scale.atTop_div_const (by norm_num))
  have he := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 65536))
  filter_upwards [he] with S hS
  simpa only [neg_div] using hS.le

end Problem337

end

end OAI
