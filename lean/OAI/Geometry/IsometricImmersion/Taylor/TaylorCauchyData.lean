import OAI.Geometry.IsometricImmersion.Taylor.FiniteTaylorComparison
import OAI.Geometry.IsometricImmersion.Darboux.QStripJetControl

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Weighted

def heightCauchyValue (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ := z ![x, a]

def heightCauchyVelocity (z : Coord → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  coordPartial 1 z ![x, a]

theorem heightCauchyValue_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyValue z a) I :=
  hz.comp (initialPoint_contDiff a).contDiffOn hcut

theorem heightCauchyVelocity_contDiffOn {z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (a : ℝ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U) :
    ContDiffOn ℝ ∞ (heightCauchyVelocity z a) I :=
  (partial_contDiffOn hz hU 1).comp (initialPoint_contDiff a).contDiffOn hcut

theorem linearCauchy_height_initial_state {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    qSolutionJet (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) ![x, a] =
      qSolutionJet z ![x, a] := by
  have h0 := heightCauchyValue_contDiffOn hz a hcut
  have h1 := heightCauchyVelocity_contDiffOn hz hU a hcut
  have hlin := linearCauchy_contDiffOn h0 h1 a
  let V : Set Coord := U ∩ spatialStrip (Ioo left right)
  have hV : IsOpen V := hU.inter (spatialStrip_isOpen isOpen_Ioo)
  have hzV : ContDiffOn ℝ ∞ z V := hz.mono inter_subset_left
  have hlinV : ContDiffOn ℝ ∞
      (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a)) V :=
    hlin.mono inter_subset_right
  have hpoint (y : ℝ) : boxPoint y a = (![y, a] : Coord) := by
    ext i
    fin_cases i <;> simp [boxPoint]
  have hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ V := by
    intro y hy
    rw [hpoint]
    exact ⟨hcut y hy, hy⟩
  have hval : ∀ y ∈ Ioo left right,
      linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a) (boxPoint y a) =
      z (boxPoint y a) := by
    intro y _
    rw [hpoint]
    exact linearCauchy_value a y _ _
  have hvel : ∀ y ∈ Ioo left right,
      coordPartial 1 (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        (boxPoint y a) = coordPartial 1 z (boxPoint y a) := by
    intro y hy
    rw [hpoint]
    exact linearCauchy_velocity isOpen_Ioo h0 h1 a (p := ![y, a]) hy
  have hh := qSolutionJet_eq_of_cauchy_data hzV hlinV hV hline hval hvel hx
  rw [hpoint] at hh
  exact hh

theorem linearCauchy_height_initial_hessian {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (left right a : ℝ)
    (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    covHessian g (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
      ![x, a] 0 0 = covHessian g z ![x, a] 0 0 := by
  rw [← stateQDenominator_qSolutionJet,
    linearCauchy_height_initial_state hz hU left right a hcut hx,
    stateQDenominator_qSolutionJet]

theorem finiteTaylorComparison_from_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (left right a : ℝ) (hcut : ∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ Ioo left right, covHessian g z ![x, a] 0 0 ≠ 0) (N : ℕ) :
    let z0 := taylorApproximation g a (heightCauchyValue z a) (heightCauchyVelocity z a) N
    ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo left right)) ∧
    (∀ x ∈ Ioo left right, z0 ![x, a] = z ![x, a] ∧
      coordPartial 1 z0 ![x, a] = coordPartial 1 z ![x, a]) ∧
    (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧ ∀ t, p.eval t = z0 ![x, t]) ∧
    (∃ V : Set Coord, IsOpen V ∧ V ⊆ U ∩ spatialStrip (Ioo left right) ∧
      (∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ V) ∧
      (∀ p ∈ V, covHessian g z0 p 0 0 ≠ 0) ∧
      ContDiffOn ℝ ∞ (qResidual g z0) V) ∧
    (∀ x ∈ Ioo left right, ∀ k < N,
      iteratedDeriv k (fun t => qResidual g z0 ![x, t]) a = 0) := by
  have h0 := heightCauchyValue_contDiffOn hz a hcut
  have h1 := heightCauchyVelocity_contDiffOn hz hU a hcut
  have hlin : ∀ x ∈ Ioo left right,
      covHessian g (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        ![x, a] 0 0 ≠ 0 := by
    intro x hx
    rw [linearCauchy_height_initial_hessian hz hU left right a hcut hx]
    exact hxx x hx
  exact finiteTaylorComparison hg hU isOpen_Ioo h0 h1 a hcut hlin N

end SmoothLocal.Taylor

end

end OAI
