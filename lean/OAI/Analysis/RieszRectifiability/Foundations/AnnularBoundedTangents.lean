import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularTangentBounds
import OAI.Analysis.RieszRectifiability.Flatness.SmoothAnnularHyperplaneTangent

namespace OAI

/-!
# Tangents with global smooth annular bounds

The global smooth annular bound is stable under blowups and compact-test limits.
This stability preserves the bound when extracting a nonzero tangent supported on a
proper hyperplane, so that the dimension-reduction argument can be iterated.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def GlobalSmoothAnnularBound {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (B : ℝ) : Prop :=
  ∀ a ∈ μ.support, ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
    ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ ≤ B

theorem GlobalSmoothAnnularBound.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (B : ℝ) (hB : GlobalSmoothAnnularBound n μ B) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    GlobalSmoothAnnularBound n (blowupMeasure n μ a s) B := by
  intro b hb r R hr hrR
  rw [smoothAnnularTransform_blowup n μ a b s r R hs hr (hr.trans_le hrR)]
  exact hB (a + s • b) ((blowupMeasure_support_iff n μ a b s hs).mp hb)
    (s * r) (s * R) (mul_pos hs hr) (mul_le_mul_of_nonneg_left hrR hs.le)

theorem GlobalSmoothAnnularBound.compact_limit {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (hB : ∀ᶠ j in atTop, GlobalSmoothAnnularBound n (μ j) B) :
    GlobalSmoothAnnularBound n ν B := by
  intro b hb r R hr hrR
  apply smoothAnnularTransform_bound_at_limit_support n G B μ ν hg hlocal univ isOpen_univ
    b hb (mem_univ b) r R hr hrR
  filter_upwards [hB] with j hj
  intro x hx _
  exact hj x hx r R hr hrR

theorem GlobalSmoothAnnularBound.of_local_tangent {d : ℕ} (n : ℕ) (G B cap : ℝ)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hg : GlobalUpperGrowth n G μ) (U : Set (Ambient d)) (hU : IsOpen U)
    (a : Ambient d) (ha : a ∈ U) (hcap : 0 < cap)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B) :
    GlobalSmoothAnnularBound n ν B := by
  exact smoothAnnularTransform_bound_on_tangent n G B cap μ ν hg U hU a ha hcap
    s hs hs0 hlocal hbound

theorem exists_annular_bounded_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G B : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support) (hB : GlobalSmoothAnnularBound n μ B)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support ∧
      GlobalSmoothAnnularBound n ν B := by
  have horigin : ∀ (t : ℝ) (ht : 0 < t), 2 * t ≤ 1 →
      ‖smoothAnnularTransform n μ 0 t 1 ht zero_lt_one‖ ≤ B := by
    intro t ht hsep
    exact hB 0 hzero t 1 ht (by linarith)
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper⟩ :=
    exists_nonzero_smooth_annular_hyperplane_tangent n hn μ C G hC hg hlower hzero e he hside
      1 B zero_lt_one horigin r hr hr0
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, ?_⟩
  apply GlobalSmoothAnnularBound.compact_limit n G B
    (fun j => blowupMeasure n μ 0 (r (ρ j))) ν
    (fun j => blowupMeasure_growth n μ 0 (r (ρ j)) G (hr (ρ j)) hg) hlocal
  exact Eventually.of_forall fun j => GlobalSmoothAnnularBound.blowup n μ B hB 0 (r (ρ j)) (hr (ρ j))

end

end RieszRectifiability

end OAI
