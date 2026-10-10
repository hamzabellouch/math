import OAI.Analysis.IrrationalRotation.Product.ProductCocycleWindow
import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Model.MixedRadixCircle
import OAI.Analysis.IrrationalRotation.Sampling.CircleCharacterDynamics

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterData

theorem sum_flattenedCost_prefix (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j : ℕ) :
    (∑ n ∈ Finset.range (p.blockEnd j), p.flattenedCost n) =
      ∑ s ∈ Finset.Icc 1 j, p.C s * (p.m s : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [p.blockEnd_succ, Finset.sum_range_add, ih,
      Finset.sum_Icc_succ_top (by omega)]
    congr 1
    calc
      (∑ n ∈ Finset.range (p.m (j + 1)), p.flattenedCost (p.blockEnd j + n)) =
          ∑ _n ∈ Finset.range (p.m (j + 1)), p.C (j + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply p.flattenedCost_eq_of_mem hm
        rw [p.mem_block_iff, Nat.add_sub_cancel, p.blockEnd_succ]
        have hn' := Finset.mem_range.mp hn
        constructor <;> omega
      _ = p.C (j + 1) * (p.m (j + 1) : ℝ) := by simp [nsmul_eq_mul, mul_comm]

theorem coordinate_mem_Ico (p : CircleParameterData) (i : ℕ) (x : Circle) :
    p.coordinate i x ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [coordinate, rep, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)).property

theorem exists_late_block (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j n : ℕ) (hj : 1 ≤ j)
    (hn : n ∉ Finset.range (p.blockEnd (j - 1))) :
    ∃ s, j ≤ s ∧ n + 1 ∈ p.block s := by
  obtain ⟨s, hs, hmem⟩ := p.exists_mem_block hm (n + 1) (by omega)
  refine ⟨s, ?_, hmem⟩
  have hn' : p.blockEnd (j - 1) ≤ n := by simpa using hn
  have hi := ((p.mem_block_iff s (n + 1)).mp hmem).2
  by_contra h
  have hsj : s ≤ j - 1 := by omega
  have hd := (p.blockEnd_strictMono hm).monotone hsj
  omega

theorem coordinate_circleValue (p : CircleParameterData)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (i : ℕ) :
    p.coordinate i (MixedRadix.circleValue d) =
      Int.fract ((p.q i : ℝ) * MixedRadix.ofDigits d) := by
  unfold coordinate rep MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  exact CircleCharacterDynamics.representative_coe _

end Invariant233.CircleParameterData

namespace Invariant233.CocycleWindowBounds

theorem exclusions_of_rounding {x y X Y K N : ℝ}
    (hK : 1 ≤ K) (hN : 0 < N)
    (hx : |x - X| ≤ 1 / N) (hy : |y - Y| ≤ 1 / N)
    (hX : X < 1 - 3 * K / N) (hY : 3 * K / N < Y) :
    x < 1 - 2 * K / N ∧ 2 * K / N < y := by
  have hdiv : 1 / N ≤ K / N := div_le_div_of_nonneg_right hK hN.le
  have hxx := (abs_le.mp hx).2
  have hyy := (abs_le.mp hy).1
  simp only [mul_div_assoc] at hX hY ⊢
  constructor <;> linarith

end Invariant233.CocycleWindowBounds

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordinate_raw_error_le (s : ℕ) (hs : 1 ≤ s) (i : ℕ) (hi : i ∈ p.block s)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (hd : MixedRadix.Nonterminal d)
    (X : ℝ) (hX : 0 ≤ X)
    (hfloor : ⌊(MixedRadix.radices p.q i : ℝ) * X⌋₊ = (d i : ℕ)) :
    |p.coordinate i (MixedRadix.circleValue d) - X| ≤ 1 / p.N s := by
  rw [p.coordinate_circleValue]
  apply (MixedRadix.abs_coordinate_sub_raw_le hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible d hd i hX hfloor).trans
  have hN : 0 < p.N s := by
    unfold CircleParameterData.N
    exact mul_pos (by exact_mod_cast hp.m_pos s hs) (by exact_mod_cast hp.K_pos s hs)
  apply one_div_le_one_div_of_le hN
  simpa only [MixedRadix.radices, Nat.cast_div_charZero (hp.frequency_divisible i)] using
    hp.frequency_ratios s hs i hi

theorem raw_good_event_exclusions (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      3 * (p.K j : ℝ) / p.N s < Y i) :
    ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i (MixedRadix.circleValue d) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (MixedRadix.circleValue e) := by
  intro s hsj i hi
  have hs : 1 ≤ s := hj.trans hsj
  have hN : 0 < p.N s := by
    unfold CircleParameterData.N
    exact mul_pos (by exact_mod_cast hp.m_pos s hs) (by exact_mod_cast hp.K_pos s hs)
  exact CocycleWindowBounds.exclusions_of_rounding
    (by exact_mod_cast hp.K_pos j hj) hN
    (hp.coordinate_raw_error_le s hs i hi d hd (X i) (hX i) (hdigit i))
    (hp.coordinate_raw_error_le s hs i hi e he (Y i) (hY i) (hedigit i))
    (hleft s hsj i hi) (hright s hsj i hi)

theorem current_margin_eq (j : ℕ) (hj : 1 ≤ j) (a : ℝ) :
    a * (p.K j : ℝ) / p.N j = a / (p.m j : ℝ) := by
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  unfold CircleParameterData.N
  field_simp

theorem source_good_event_exclusions (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hcurrent : ∀ i ∈ p.block j,
      X i < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < Y i)
    (hfuture : ∀ s, j < s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i) :
    ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i (MixedRadix.circleValue d) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (MixedRadix.circleValue e) := by
  have hraw : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i := by
    intro s hsj i hi
    rcases eq_or_lt_of_le hsj with h | h
    · subst s
      simpa only [hp.current_margin_eq j hj 3] using hcurrent i hi
    · exact hfuture s h i hi
  exact hp.raw_good_event_exclusions j hj d e hd he X Y hX hY hdigit hedigit
    (fun s hs i hi => (hraw s hs i hi).1) (fun s hs i hi => (hraw s hs i hi).2)

theorem finite_window_coefficients (j : ℕ) (hj : 1 ≤ j) (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost v
        (fun n => p.q (n + 1) • x) : ℂ)‖ ≤ p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost (-v)
        (fun n => p.q (n + 1) • y) : ℂ) * conj (γ (-v))‖ ≤ p.coefficientBound j) := by
  have hc (n : ℕ) : 0 ≤ p.flattenedCost n :=
    (hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))).le
  have hα (n : ℕ) : p.alpha θ (n + 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hexclude (n : ℕ) (hn : n ∉ Finset.range (p.blockEnd (j - 1))) :
      p.coordinate (n + 1) x + (p.K j : ℝ) * p.alpha θ (n + 1) < 1 ∧
        (p.K j : ℝ) * p.alpha θ (n + 1) ≤ p.coordinate (n + 1) y := by
    obtain ⟨s, hsj, hns⟩ := p.exists_late_block hp.m_pos j n hj hn
    have hs : 1 ≤ s := hj.trans hsj
    have hphase := (hp.phase_bounds s hs (n + 1) hns).2
    have hmul := mul_le_mul_of_nonneg_left hphase.le (Nat.cast_nonneg (p.K j))
    have hbound : (p.K j : ℝ) * p.alpha θ (n + 1) ≤ 2 * (p.K j : ℝ) / p.N s := by
      calc
        _ ≤ (p.K j : ℝ) * (2 / p.N s) := hmul
        _ = _ := by ring
    constructor
    · linarith [hleft s hsj (n + 1) hns]
    · exact hbound.trans (hright s hsj (n + 1) hns).le
  have h := ProductCocycle.finite_window_coefficients
    (Finset.range (p.blockEnd (j - 1))) (fun n => p.alpha θ (n + 1)) p.flattenedCost
    (p.K j) (fun n => p.q (n + 1) • x) (fun n => p.q (n + 1) • y) hα hc
    (fun n hn => (hexclude n hn).1) (fun n hn => (hexclude n hn).2) ξ γ hξ hγ
  simpa only [p.sum_flattenedCost_prefix hp.m_pos, CircleParameterData.coefficientBound] using h

end Invariant233.CircleParameterLaws

end

end OAI
