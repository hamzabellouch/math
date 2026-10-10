import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContinuousCompactSmoothJets

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Distributions Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M]
local instance chartTensorNeighborhoodInst1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorNeighborhoodInst2 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartTensorNeighborhoodInst3 : NormedAddCommGroup (MetricForm E) := inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ))
local instance chartTensorNeighborhoodInst4 : NormedSpace ℝ (MetricForm E) := inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ))

omit [T2Space M] in
lemma chartTensorOfMetric_sub (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (g h : SmoothMetric E M)
    (hg : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x)
    (hh : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → h.inner x = g₀.inner x) :
    ((chartTensorOfMetric g₀ p K ht h hh - chartTensorOfMetric g₀ p K ht g hg) : E → MetricForm E) =
      fun y => metricMatrixForm (metricCoefficients h p y - metricCoefficients g p y) := by
  funext y
  change (chartMetricForm h p y-chartMetricForm g₀ p y) -
    (chartMetricForm g p y-chartMetricForm g₀ p y) = _
  rw [sub_sub_sub_cancel_right]
  exact (map_sub (metricMatrixFormCLM (E:=E)) _ _).symm

omit [T2Space M] in
lemma chartTensorRepresentation_neighborhood (g₀ : SmoothMetric E M) (p : M) (K : Compacts E)
    (ht : (chartAt E p).target = univ) (g : SmoothMetric E M)
    (hg : ∀ x, x ∉ (chartAt E p).symm '' (K : Set E) → g.inner x = g₀.inner x)
    (U : Set 𝓓_{K}(E,MetricForm E)) (hU : U ∈ 𝓝 (chartTensorOfMetric g₀ p K ht g hg)) :
    IsSmoothNeighborhood g {h | ∀ hh, chartTensorOfMetric g₀ p K ht h hh ∈ U} := by
  classical
  let : NormedAddCommGroup
      (Matrix (CoordIndex E) (CoordIndex E) ℝ →L[ℝ] CoordinateForm E) :=
    inferInstanceAs (NormedAddCommGroup
      ((CoordIndex E → CoordIndex E → ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)))
  obtain ⟨s,r,hr,hs⟩ := (ContDiffMapSupportedIn.withSeminorms ℝ E (MetricForm E) ⊤ K).mem_nhds_iff _ _ |>.mp hU
  let C : ℝ := max ‖metricMatrixFormCLM (E:=E)‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let ε := r/(2*C)
  have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hC)
  let test (m : ℕ) (i j : CoordIndex E) : CoordinateTest E M :=
    ⟨p,K,K.isCompact,ht ▸ subset_univ _,m,i,j⟩
  let tests := s.toList.flatMap (fun m => (Finset.univ : Finset (CoordIndex E × CoordIndex E)).toList.map
    (fun ij => test m ij.1 ij.2))
  refine ⟨tests,ε,hε,?_⟩
  intro h hh hhe
  apply hs
  rw [Seminorm.mem_ball]
  apply Seminorm.finset_sup_apply_lt hr
  intro m hm
  have htst (i j : CoordIndex E) : test m i j ∈ tests := by
    simp only [tests,List.mem_flatMap,Finset.mem_toList,List.mem_map]
    exact ⟨m,hm,⟨(i,j),Finset.mem_univ _,rfl⟩⟩
  have hb : (ContDiffMapSupportedIn.seminorm ℝ E (MetricForm E) ⊤ K m)
      (chartTensorOfMetric g₀ p K ht h hhe - chartTensorOfMetric g₀ p K ht g hg) ≤
      ‖metricMatrixFormCLM (E:=E)‖*ε := by
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (mul_nonneg (norm_nonneg _) hε.le) _ _).mpr
    intro y hy
    change ‖iteratedFDeriv ℝ m (fun y =>
      chartTensorOfMetric g₀ p K ht h hhe y - chartTensorOfMetric g₀ p K ht g hg y) y‖ ≤ _
    rw [show (fun y => chartTensorOfMetric g₀ p K ht h hhe y -
      chartTensorOfMetric g₀ p K ht g hg y) = fun y =>
        metricMatrixForm (metricCoefficients h p y - metricCoefficients g p y) from
      chartTensorOfMetric_sub g₀ p K ht g h hg hhe]
    refine metricMatrixForm_iterated_jet_bound ?_ m hε.le ?_
    · apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact ((contDiffOn_metricCoefficient h p i j).contDiffAt (ht ▸ univ_mem)).sub
        ((contDiffOn_metricCoefficient g p i j).contDiffAt (ht ▸ univ_mem))
    · intro i j
      exact (hh (test m i j) (htst i j) y hy).le
  apply lt_of_le_of_lt hb
  calc
    ‖metricMatrixFormCLM (E:=E)‖*ε ≤ C*ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
    _ = r/2 := by dsimp [ε]; field_simp
    _ < r := by linarith
end YauCounterexamples
end

end OAI
