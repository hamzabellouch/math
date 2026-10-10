import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RectangleAffine
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Geometry

namespace OAI

/-! Quantitative separation during ordered horizontal extraction and insertion.
Only the active rectangle's right endpoint changes during its swept box. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

/-- A rational coordinate gap between two filled rectangles. -/
def EndpointGap (δ : ℚ) (R S : RationalBox 2) : Prop :=
  ∃ j : Fin 2, R.upper j + δ ≤ S.lower j ∨ S.upper j + δ ≤ R.lower j

/-- The existing computable maximum of the four signed endpoint gaps supplies
an actual separating coordinate. -/
theorem endpointGap_of_le_boxGap {R S : RationalBox 2} {δ : ℚ}
    (hδ : δ ≤ boxGap R S) : EndpointGap δ R S := by
  simp only [boxGap, le_max_iff] at hδ
  rcases hδ with (hδ | hδ) | (hδ | hδ)
  · exact ⟨0, Or.inr (by linarith)⟩
  · exact ⟨0, Or.inl (by linarith)⟩
  · exact ⟨1, Or.inr (by linarith)⟩
  · exact ⟨1, Or.inl (by linarith)⟩

theorem separated_endpointGap {R S : RationalBox 2}
    (hR : R.positive) (hS : S.positive)
    (hsep : PositivelySeparated R.carrier S.carrier) :
    0 < boxGap R S ∧ EndpointGap (boxGap R S) R S :=
  ⟨boxGap_pos_of_separated R S hR hS hsep, endpointGap_of_le_boxGap le_rfl⟩

/-- The full bounding box swept when a rectangle is moved horizontally to a
point on its right. `endpoint` is the right edge of the translated rectangle. -/
def rightSweep (R : RationalBox 2) (endpoint : ℚ) : RationalBox 2 :=
  ⟨R.lower, ![max (R.upper 0) endpoint, R.upper 1]⟩

theorem rightSweep_positive {R : RationalBox 2} (hR : R.positive) (endpoint : ℚ) :
    (rightSweep R endpoint).positive := by
  intro j
  fin_cases j
  · exact (hR 0).trans_le (le_max_left _ _)
  · exact hR 1

/-- Center order rules out a separated obstacle lying to the right. -/
theorem left_gap_of_center_order {a b c d δ : ℚ}
    (hab : a ≤ b) (hcd : c ≤ d) (hδ : 0 < δ) (hcenter : c + d ≤ a + b)
    (hgap : b + δ ≤ c ∨ d + δ ≤ a) : d + δ ≤ a := by
  rcases hgap with hgap | hgap
  · exfalso
    linarith
  · exact hgap

/-- A stationary rectangle with no larger horizontal center retains the same
quantitative gap while the active rectangle sweeps to the right. -/
theorem rightSweep_gap {R S : RationalBox 2} {δ : ℚ}
    (hR : R.positive) (hS : S.positive) (hδ : 0 < δ)
    (hcenter : S.lower 0 + S.upper 0 ≤ R.lower 0 + R.upper 0)
    (hgap : EndpointGap δ R S) (endpoint : ℚ) :
    EndpointGap δ (rightSweep R endpoint) S := by
  obtain ⟨j, hj⟩ := hgap
  fin_cases j
  · refine ⟨0, Or.inr ?_⟩
    exact left_gap_of_center_order (hR 0).le (hS 0).le hδ hcenter hj
  · exact ⟨1, hj⟩

theorem rightSweep_gap_of_centers {R S : RationalBox 2} {δ : ℚ}
    (hR : R.positive) (hS : S.positive) (hδ : 0 < δ)
    (hcenter : S.center 0 ≤ R.center 0) (hgap : EndpointGap δ R S) (endpoint : ℚ) :
    EndpointGap δ (rightSweep R endpoint) S := by
  apply rightSweep_gap hR hS hδ ?_ hgap endpoint
  have hsum : (S.lower 0 : ℝ) + (S.upper 0 : ℝ) ≤
      (R.lower 0 : ℝ) + (R.upper 0 : ℝ) := by
    dsimp [RationalBox.center] at hcenter
    linarith
  exact_mod_cast hsum

theorem EndpointGap.separated {δ : ℚ} {R S : RationalBox 2}
    (hgap : EndpointGap δ R S) (hδ : 0 < δ) :
    PositivelySeparated R.carrier S.carrier := by
  have hp : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine ⟨δ, hp, ?_⟩
  intro x hx y hy
  obtain ⟨j, hj⟩ := hgap
  have ha : (δ : ℝ) ≤ |x j - y j| := by
    rcases hj with hj | hj
    · have hg : (R.upper j : ℝ) + (δ : ℝ) ≤ S.lower j := by exact_mod_cast hj
      calc
        (δ : ℝ) ≤ y j - x j := by linarith [(hx j).2, (hy j).1]
        _ ≤ |y j - x j| := le_abs_self _
        _ = |x j - y j| := abs_sub_comm _ _
    · have hg : (S.upper j : ℝ) + (δ : ℝ) ≤ R.lower j := by exact_mod_cast hj
      exact (show (δ : ℝ) ≤ x j - y j by linarith [(hy j).2, (hx j).1]).trans
        (le_abs_self _)
  exact ha.trans (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) j)

end ForcedComputation.PlanarRouting

end OAI
