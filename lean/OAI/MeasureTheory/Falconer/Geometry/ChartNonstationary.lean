import OAI.MeasureTheory.Falconer.Fourier.ChartDerivatives
import OAI.MeasureTheory.Falconer.Fourier.NonstationaryPhase

namespace OAI

/-!
# Nonstationary integration in the actual normalized chart

The phase is the scalar product with the normalized affine chart, not an
abstract phase supplied as a hypothesis. Its higher derivative constants
come from `tangent_line_phase_derivatives`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_chart_nonstationary (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w y t v : E) (f : ℝ → ℂ),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ContDiff ℝ ∞ f →
      ∀ (C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      ‖v‖ ≤ τ * D → tsupport f ⊆ Icc (-1 : ℝ) 1 →
      (∀ u ∈ tsupport f,
        τ ≤ |deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v) u|) →
      (∀ k ≤ n, ∀ u ∈ tsupport f, ‖iteratedDeriv k f u‖ ≤ C*D^k) →
      ‖∫ u, phaseOscillator (fun x => inner ℝ (normalizedLine (w+y) t x) v) Λ u * f u‖ ≤
        A*C*(D/(Λ*τ))^n := by
  choose B hB hbound using (fun k => tangent_line_phase_derivatives (E := E) (k+1))
  obtain ⟨A,hA,hestimate⟩ := phase_nonstationary_from_derivative_bounds B hB n
  refine ⟨2*A,by positivity,?_⟩
  intro w y t v f hw ht hwy hwt hyt hy hf C D Λ τ hC hD hΛ hτ hv hs hl hb
  have hφ := tangent_line_phase_smooth hw ht hwy hwt hyt v
  have hgb (k : ℕ) (hk : 1 ≤ k) (_hkn : k ≤ n) (u : ℝ) (hu : u ∈ tsupport f) :
      |iteratedDeriv k (deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v)) u| ≤
        B k * τ * D^k := by
    rw [← iteratedDeriv_succ']
    calc
      _ ≤ B k * ‖v‖ := hbound k w y t v hw ht hwy hwt hyt hy u (hs hu)
      _ ≤ B k * (τ*D^k) := by
        apply mul_le_mul_of_nonneg_left _ (hB k)
        exact hv.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hD (by omega)) hτ.le)
      _ = _ := by ring
  have hh := hestimate _ f hφ hf (-1) 1 C D Λ τ (by norm_num) hC
    (zero_le_one.trans hD) hΛ hτ hs hl hgb hb
  convert hh using 1; ring

/-- One failed perpendicular test selects a single tangent direction for
all the point replacements in the same discarded cell--cap term. -/
theorem failed_test_chart_nonstationary (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : E) (τ : ℝ), ‖w‖ = 1 → 0 < τ →
      τ < ‖perpendicularPart w d‖ →
      ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w t = 0 ∧
        ∀ (y v : E) (f : ℝ → ℂ), inner ℝ w y = 0 → inner ℝ y t = 0 →
          ‖y‖ ≤ 1 → ContDiff ℝ ∞ f →
          ∀ (C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
          ‖v‖ ≤ (τ/4)*D → tsupport f ⊆ Icc (-1 : ℝ) 1 →
          (∀ u ∈ tsupport f, ‖y+u•t‖ ≤ 1 ∧
            ‖v-d‖ + 4*‖y+u•t‖*‖d‖ ≤ τ/2) →
          (∀ k ≤ n, ∀ u ∈ tsupport f, ‖iteratedDeriv k f u‖ ≤ C*D^k) →
          ‖∫ u, phaseOscillator (fun x => inner ℝ (normalizedLine (w+y) t x) v) Λ u * f u‖ ≤
            A*C*(D/(Λ*(τ/4)))^n := by
  obtain ⟨A,hA,hestimate⟩ := tangent_chart_nonstationary (E := E) n
  refine ⟨A,hA,?_⟩
  intro w d τ hw hτ hbad
  obtain ⟨t,ht,hwt,hlower⟩ := perpendicular_failure_chart_nonstationary hw hτ hbad
  refine ⟨t,ht,hwt,?_⟩
  intro y v f hwy hyt hy hf C D Λ hC hD hΛ hv hs herr hb
  exact hestimate w y t v f hw ht hwy hwt hyt hy hf C D Λ (τ/4) hC hD hΛ
    (by positivity) hv hs (fun u hu => hlower y v u hwy (herr u hu).1 (herr u hu).2) hb

end Falconer

end OAI
