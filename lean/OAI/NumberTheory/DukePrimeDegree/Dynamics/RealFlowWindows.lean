import OAI.NumberTheory.DukePrimeDegree.Dynamics.FiniteFlowGenericSets
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-!
# Real stopping times for bounded flow averages

An arbitrary real window differs from its integer part by a boundary
interval of length at most one.  The estimate is uniform in the initial
point, so the same good set works for stopping times selected from a pair.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

lemma normalized_integral_nearby_length_bound
    (F : ℝ → ℝ) (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, |F t| ≤ C)
    (L T : ℝ) (hL : 0 < L) (hLT : L ≤ T) (hTL : T ≤ L + 1) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) -
        L⁻¹ * (∫ t in (0 : ℝ)..L, F t)| ≤ 2 * C / L := by
  have hT : 0 < T := hL.trans_le hLT
  have hJ : |∫ t in L..T, F t| ≤ C := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
      (a := L) (b := T) (C := C) (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
    simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hLT)] at hb
    exact hb.trans (by nlinarith)
  have hI : |∫ t in (0 : ℝ)..L, F t| ≤ C * L := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hL] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (f := F)
        (a := 0) (b := L) (C := C)
        (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t))
  have hinv : T⁻¹ ≤ L⁻¹ := (inv_le_inv₀ hT hL).mpr hLT
  have hcoef : |T⁻¹ - L⁻¹| * (C * L) ≤ C / L := by
    rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
    have heq : -(T⁻¹ - L⁻¹) * (C * L) = C * (T - L) / T := by
      field_simp [ne_of_gt hT, ne_of_gt hL]
      ring
    rw [heq]
    calc
      C * (T - L) / T ≤ C / T := by
        exact div_le_div_of_nonneg_right (by nlinarith) hT.le
      _ ≤ C / L := div_le_div_of_nonneg_left hC hL hLT
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 L) (hint L T)]
  have heq : T⁻¹ * ((∫ t in (0 : ℝ)..L, F t) + ∫ t in L..T, F t) -
      L⁻¹ * (∫ t in (0 : ℝ)..L, F t) =
      T⁻¹ * (∫ t in L..T, F t) +
        (T⁻¹ - L⁻¹) * (∫ t in (0 : ℝ)..L, F t) := by ring
  rw [heq]
  calc
    _ ≤ |T⁻¹ * (∫ t in L..T, F t)| +
        |(T⁻¹ - L⁻¹) * (∫ t in (0 : ℝ)..L, F t)| := abs_add_le _ _
    _ = T⁻¹ * |∫ t in L..T, F t| +
        |T⁻¹ - L⁻¹| * |∫ t in (0 : ℝ)..L, F t| := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hT)]
    _ ≤ T⁻¹ * C + |T⁻¹ - L⁻¹| * (C * L) :=
      add_le_add (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hT.le))
        (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ C / L + C / L := by
      exact add_le_add (by simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right hinv hC) hcoef
    _ = 2 * C / L := by ring

/-- Any real-time average has uniformly small distance from its integer
part once that integer part is positive. -/
lemma normalized_integral_floor_bound
    (F : ℝ → ℝ) (hint : ∀ a b, IntervalIntegrable F volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, |F t| ≤ C)
    (T : ℝ) (hT : 1 ≤ T) :
    |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) -
        (⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), F t)| ≤
      2 * C / (⌊T⌋₊ : ℝ) := by
  have hnonneg : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT
  have hfloor : 1 ≤ ⌊T⌋₊ := (Nat.le_floor_iff hnonneg).mpr (by simpa using hT)
  exact normalized_integral_nearby_length_bound F hint C hC hbound (⌊T⌋₊ : ℝ) T
    (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hfloor))
    (Nat.floor_le hnonneg) (Nat.lt_floor_add_one T).le

/-- Integer good-set control extends to all sufficiently large real
window lengths, retaining the same measurable set. -/
theorem real_window_control_of_integer_mean_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (G : Set Y) (q : Y → ℝ) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ)
    (hgood : ∀ x ∈ G, ∀ N ≥ N₀,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (U t x)) - q x| ≤ ε / 2) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - q x| ≤ ε := by
  have hlim : Tendsto (fun N : ℕ => 2 * C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  let M : ℕ := max 1 (max N₀ N₁)
  refine ⟨(M : ℝ), ?_, ?_⟩
  · exact_mod_cast (le_max_left 1 (max N₀ N₁))
  · intro x hx T hT
    have hM : 1 ≤ M := le_max_left _ _
    have hT₁ : 1 ≤ T := (show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast hM).trans hT
    have hT₀ : 0 ≤ T := (by norm_num : (0 : ℝ) ≤ 1).trans hT₁
    have hfM : M ≤ ⌊T⌋₊ := (Nat.le_floor_iff hT₀).mpr hT
    have hf₀ : N₀ ≤ ⌊T⌋₊ := (le_trans (le_max_left N₀ N₁) (le_max_right 1 _)).trans hfM
    have hf₁ : N₁ ≤ ⌊T⌋₊ := (le_trans (le_max_right N₀ N₁) (le_max_right 1 _)).trans hfM
    have hb := normalized_integral_floor_bound (fun t => f (U t x)) (hint x)
      C hC (fun t => hbound (U t x)) T hT₁
    have hg := hgood x hx ⌊T⌋₊ hf₀
    have hsmall := hN₁ ⌊T⌋₊ hf₁
    calc
      _ ≤ |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) -
          (⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x))| +
          |(⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x)) - q x| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
          (T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)))
          ((⌊T⌋₊ : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), f (U t x))) (q x)
      _ ≤ 2 * C / (⌊T⌋₊ : ℝ) + ε / 2 := add_le_add hb hg
      _ ≤ ε := by linarith

/-- The constant-mean specialization retains the original generic-set API. -/
theorem real_window_control_of_integer_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C)
    (G : Set Y) (c ε : ℝ) (hε : 0 < ε) (N₀ : ℕ)
    (hgood : ∀ x ∈ G, ∀ N ≥ N₀,
      |(N : ℝ)⁻¹ * (∫ t in (0 : ℝ)..(N : ℝ), f (U t x)) - c| ≤ ε / 2) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - c| ≤ ε :=
  real_window_control_of_integer_mean_control U f hint C hC hbound G
    (fun _ => c) ε hε N₀ hgood

theorem exists_uniform_real_flow_generic_set
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : Y →ᵇ ℝ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
      ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ G, ∀ T ≥ R,
        |T⁻¹ * (∫ t in (0 : ℝ)..T, f (realActionTime t x)) - ∫ y, f y ∂μ| ≤ ε := by
  obtain ⟨G, hG, hGμ, N₀, hN₀⟩ := exists_uniform_integer_flow_generic_set
    μ f (ε / 2) δ (by positivity) hδ
  refine ⟨G, hG, hGμ, ?_⟩
  exact real_window_control_of_integer_control realActionTime f
    (fun x a b => ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    ‖f‖ (norm_nonneg f) (fun x => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    G (∫ y, f y ∂μ) ε hε N₀ hN₀

end DukePrimeDegree

end

end OAI
