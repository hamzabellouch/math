import Mathlib
import OAI.Analysis.AffineBernstein.LocalDet

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedDetProducer

/-- Prescribed lower modulus of tangent sections; this is the same section
condition as rigidity.tex, with the frozen `tangentSection` definition. -/
def HasLowerSectionModulus {n : ℕ} (O : Set (Space n)) (f : Space n → ℝ)
    (b : ℝ → ℝ) : Prop :=
  ∀ x ∈ O, ∀ r : ℝ, 0 < r → tangentSection O f x (b r) ⊆ Metric.ball x r

/-- A genuine solution-uniform nonlinear estimate. The determinant bound is
produced from the unchanged PDE, oscillation and section modulus, rather
than postulated. This is an intermediate estimate, not the TW Hessian/C³
producer or the full Bernstein theorem. -/
theorem normalized_det_upper_producer (n : ℕ) (b : ℝ → ℝ)
    (hb : ∀ r : ℝ, 0 < r → 0 < b r) :
    ∃ C > (0:ℝ), ∀ f : Space n → ℝ,
      ContDiffOn ℝ ∞ f (Metric.ball 0 (1/4 : ℝ)) →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), (hessian f x).PosDef) →
      AffineMaximalOn (Metric.ball 0 (1/4 : ℝ)) f →
      (∀ x ∈ Metric.ball (0 : Space n) (1/4 : ℝ), -1 ≤ f x ∧ f x ≤ 0) →
      HasLowerSectionModulus (Metric.ball 0 (1/4 : ℝ)) f b →
      (hessian f 0).det ≤ C := by
  let h := b (1/16) / 2
  have hh : 0 < h := half_pos (hb _ (by norm_num))
  let C : ℝ := (2*(n:ℝ)*(((n:ℝ)+2)*(2*((4*(1:ℝ)/(1/16))^2+1))+
      (4*(1:ℝ)/(1/16))^2))^n * h^2 *
        Real.exp ((4*(1:ℝ)/(1/16))^2/(4*((4*(1:ℝ)/(1/16))^2+1))) / h^(n+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  intro f hf hp hm hfbound hmod
  have hzero : (0:Space n) ∈ Metric.ball 0 (1/4 : ℝ) := Metric.mem_ball_self (by norm_num)
  have hsection : tangentSection (Metric.ball 0 (1/4 : ℝ)) f 0 (2*h) ⊆ Metric.ball 0 (1/16 : ℝ) := by
    have he : 2*h = b (1/16) := by dsimp [h]; ring
    rw [he]
    exact hmod 0 hzero _ (by norm_num)
  have hbound : ∀ x ∈ Metric.ball (0:Space n) (1/4 : ℝ), |f x| ≤ 1 := by
    intro x hx
    exact abs_le.mpr ⟨(hfbound x hx).1,(hfbound x hx).2.trans (by norm_num)⟩
  have H := affineMaximal_det_upper_of_section_control Metric.isOpen_ball (convex_ball _ _)
    hf hp hm (a := 0) (r := 1/16) (h := h) (M := 1) (by norm_num) hh (by norm_num)
    (Metric.closedBall_subset_ball (by norm_num)) hbound hsection
  exact H.trans (le_add_of_nonneg_right zero_le_one)

end NormalizedDetProducer



end
end AffineBernstein
end

end OAI
