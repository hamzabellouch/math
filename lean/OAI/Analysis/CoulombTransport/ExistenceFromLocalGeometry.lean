import OAI.Analysis.CoulombTransport.SmoothBranchMarginal
import OAI.Analysis.CoulombTransport.BranchOptimizer
import OAI.Analysis.CoulombTransport.BranchSeparation
import OAI.Analysis.CoulombTransport.CompactLiftApproximation

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

theorem exists_fullCoulombConclusion_of_local_geometry
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e i)
      (SmoothBranchMarginal.componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i) (e i).source)
    (he' : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    {U : Set E3} (hU : MeasurableSet U)
    (hBU : Metric.ball c r ⊆ U) (heU : ∀ i, e i '' Metric.ball c r ⊆ U)
    {u : E3 → ℝ} (hu : Measurable u) {M : ℝ} (hM : 0 ≤ M)
    (hubound : ∀ x ∈ U, -M ≤ u x ∧ u x ≤ M)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) ≤
        coulombCost t)
    (hcontact01 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 0 x) + u (e 1 x)) = coulombCost (x, (e 0 x, e 1 x)))
    (hcontact23 : ∀ x ∈ Metric.ball c r,
      ENNReal.ofReal (u x + u (e 2 x) + u (e 3 x)) = coulombCost (x, (e 2 x, e 3 x)))
    (hselect : ∀ x y z : E3, x ∈ Metric.ball c r → y ∈ U → z ∈ U →
      ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
      ∃ i, y = e i x) :
    ∃ rho : E3 → ℝ, HasFullCoulombConclusion rho := by
  obtain ⟨d, hd⟩ := SmoothBranchMarginal.exists_smoothBranchData_of_smooth_charts
    c hr e hsource hdisj he he'
  have : IsProbabilityMeasure d.nu := d.probability
  have hfull : ∀ᵐ x ∂d.nu, x ∈ Metric.ball c r :=
    d.core_full.mono (fun _ hx => d.core_subset hx)
  have hdensity : densityMeasure d.rho =
      branchMarginal d.nu (d.branch 0) (d.branch 1) (d.branch 2) (d.branch 3) := by
    simpa [branchMarginal, Fin.sum_univ_succ, smul_add, add_assoc] using d.density_eq
  have hHU : ∀ i, d.branch i '' Metric.ball c r ⊆ U := by
    rintro i _ ⟨x, hx, rfl⟩
    rw [hd i x hx]
    exact heU i ⟨x, hx, rfl⟩
  have hCentral : ∀ i, Disjoint (Metric.ball c r) (d.branch i '' Metric.ball c r) := by
    intro i
    exact d.component_disjoint (show (none : Option (Fin 4)) ≠ some i by simp)
  have hPair : Pairwise fun i j =>
      Disjoint (d.branch i '' Metric.ball c r) (d.branch j '' Metric.ball c r) := by
    intro i j hij
    exact d.component_disjoint (show some i ≠ some j by simpa using hij)
  have hc01 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 0 x) + u (d.branch 1 x)) =
        coulombCost (x, (d.branch 0 x, d.branch 1 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 0 x hx, hd 1 x hx] using hcontact01 x hx
  have hc23 : ∀ᵐ x ∂d.nu,
      ENNReal.ofReal (u x + u (d.branch 2 x) + u (d.branch 3 x)) =
        coulombCost (x, (d.branch 2 x, d.branch 3 x)) := by
    filter_upwards [hfull] with x hx
    simpa only [hd 2 x hx, hd 3 x hx] using hcontact23 x hx
  have hcounter : HasCoulombCounterexample d.rho := by
    apply hasCoulombCounterexample_of_real_branches d.rho d.density_smooth d.nu
      d.branch d.branch_measurable hdensity d.measurable_central hU hfull hBU hHU
      d.branch_injective d.branch_image_measurable hCentral hPair
      hu hM hubound hbound hc01 hc23
    intro x y z hx hy hz hc
    obtain ⟨i, hi⟩ := hselect x y z hx hy hz hc
    exact ⟨i, hi.trans (hd i x hx).symm⟩
  have hoptimal := branchCoupling_optimality_of_real_certificate d.nu d.branch
    d.branch_measurable hU hfull hBU hHU hu hM hubound hbound hc01 hc23
  have hdisjoint : Pairwise (fun i j =>
      Disjoint (BranchSeparation.components d.compactCore d.branch i)
        (BranchSeparation.components d.compactCore d.branch j)) := by
    apply BranchSeparation.disjoint_components_mono d.core_subset
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact hCentral j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (hCentral i).symm
      | succ j => exact hPair (by simpa using hij)
  obtain ⟨eta, heta, hsep⟩ := BranchSeparation.exists_ae_separated_branchCoupling
    d.core_compact d.core_full d.branch_measurable d.branch_continuous hdisjoint
  refine ⟨d.rho, hcounter.hasFull_of_separated_optimizer ?_ ?_ heta hsep⟩
  · rw [hdensity]
    exact isThreeCoupling_branchCoupling d.nu (d.branch_measurable 0)
      (d.branch_measurable 1) (d.branch_measurable 2) (d.branch_measurable 3)
  · simpa only [hdensity] using hoptimal.1

end Problem356

end

end OAI
