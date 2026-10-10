import OAI.Analysis.IrrationalRotation.Analysis.IndividualLusin
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Lusin

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [CompactSpace X] [NormalSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]

theorem exists_bounded_continuous_eq_on_large_compact
    {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖g x‖ ≤ C) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (a : C(X, ℂ)) (K : Set X), IsCompact K ∧ μ Kᶜ < ε ∧
      (∀ x, ‖a x‖ ≤ 2 * C) ∧ Set.EqOn a g K := by
  obtain ⟨K, hK, hμK, hgK⟩ := exists_compact_continuousOn μ hg hε
  let gre : C(K, ℝ) := ⟨fun x => (g x).re, Complex.continuous_re.comp hgK.domRestrict⟩
  let gim : C(K, ℝ) := ⟨fun x => (g x).im, Complex.continuous_im.comp hgK.domRestrict⟩
  have hre : ∀ x : K, gre x ∈ Icc (-C) C := by
    intro x
    exact abs_le.mp ((Complex.abs_re_le_norm (g x)).trans (hb x))
  have him : ∀ x : K, gim x ∈ Icc (-C) C := by
    intro x
    exact abs_le.mp ((Complex.abs_im_le_norm (g x)).trans (hb x))
  have hne : (Icc (-C) C).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨are, hare, heqre⟩ := gre.exists_restrict_eq_forall_mem_of_closed hre hne hK.isClosed
  obtain ⟨aim, haim, heqim⟩ := gim.exists_restrict_eq_forall_mem_of_closed him hne hK.isClosed
  let a : C(X, ℂ) := ⟨fun x => (are x : ℂ) + (aim x : ℂ) * Complex.I, by fun_prop⟩
  refine ⟨a, K, hK, hμK, ?_, ?_⟩
  · intro x
    change ‖(are x : ℂ) + (aim x : ℂ) * Complex.I‖ ≤ 2 * C
    calc
      _ ≤ ‖(are x : ℂ)‖ + ‖(aim x : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |are x| + |aim x| := by simp
      _ ≤ C + C := add_le_add (abs_le.mpr (hare x)) (abs_le.mpr (haim x))
      _ = 2 * C := by ring
  · intro x hx
    have hr := DFunLike.congr_fun heqre ⟨x, hx⟩
    have hi := DFunLike.congr_fun heqim ⟨x, hx⟩
    change are x = (g x).re at hr
    change aim x = (g x).im at hi
    change (are x : ℂ) + (aim x : ℂ) * Complex.I = g x
    rw [hr, hi, Complex.re_add_im]

theorem exists_bounded_continuous_eventuallyEq
    {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖g x‖ ≤ C) :
    ∃ a : ℕ → C(X, ℂ), (∀ n x, ‖a n x‖ ≤ 2 * C) ∧
      ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a n x = g x := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' (by simp : (1 : ℝ≥0∞) ≠ 0) ℕ
  choose a K hK hμK hbA heq using
    (fun n => exists_bounded_continuous_eq_on_large_compact μ hg hC hb (hδpos n).ne')
  have hsum : (∑' n, μ (K n)ᶜ) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hμK n).le
      _ < 1 := hδsum
      _ < ∞ := by simp
  refine ⟨a, hbA, ?_⟩
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with n hn
  exact heq n (by simpa using hn)

end Invariant233.Lusin

end

end OAI
