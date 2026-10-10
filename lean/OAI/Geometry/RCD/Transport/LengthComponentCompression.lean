import OAI.Geometry.RCD.Transport.LengthComponentNode
import OAI.Geometry.RCD.Transport.LengthComponentDyadic
import OAI.Geometry.RCD.Transport.MaximalTreeCompression

namespace OAI

/-! # Compression at the length of a component, independent of total diameter

Normalization cancels from the inherited density budget. This estimate is
uniform for fixed length windows when bounded endpoint approximations grow.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.length_component_compression
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (hm : ∀ m, RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m)
    {S : Set ℝ} (hS : MeasurableSet S) (κ : Measure C(Time,X))
    (heκ : κ=π.restrict {γ | dist (γ 0) (γ 1)∈S})
    {D : ℝ} (hD0 : 0≤D) (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    ∀ t, κ.map (fun γ => γ t)≤compressionBudget K n D a.capacity • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  have hκ : κ≤π := by rw [heκ]; exact Measure.restrict_le_self
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  by_cases hκ0 : κ univ=0
  · have he : κ=0 := Measure.measure_univ_eq_zero.mp hκ0
    simp only [he,Measure.map_zero]
    exact fun _ => bot_le
  have hκtop : κ univ≠∞ := measure_ne_top κ univ
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,_⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  obtain ⟨b,hb0,hb1,hbD,hbC⟩ :=
    hX.compressed_subplan_node_capacity K n hn a π hg hp hC hc κ hκ hκ0 hD0 hD
  have hpb : IsOptimalCoupling b.left b.right (πn.map (fun γ => (γ 0,γ 1))) := by
    rw [hb0,hb1,←heval,←heval]; exact hpn
  have hmn (m) := hX.length_component_dyadic_maximal K n hn hq0 hq1 hC m a π inferInstance
    hg hp hc (hm m) S hS κ heκ hκ0
  have hh := hX.maximal_tree_compression K n hn hq0 hq1 b πn hgn hpb hmn
  rw [hbD,hbC] at hh
  have hbudget : compressionBudget K n D ((κ univ)⁻¹*a.capacity)=
      (κ univ)⁻¹*compressionBudget K n D a.capacity := by
    unfold compressionBudget compressionStep
    ring
  intro t B
  have hb := hh t B
  rw [heval,hbudget] at hb
  change (κ univ)⁻¹*(κ.map (fun γ => γ t)) B≤
    ((κ univ)⁻¹*compressionBudget K n D a.capacity)*(hausdorff n X) B at hb
  change (κ.map (fun γ => γ t)) B≤compressionBudget K n D a.capacity*(hausdorff n X) B
  calc
    _ = κ univ*((κ univ)⁻¹*(κ.map (fun γ => γ t)) B) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hκ0 hκtop,one_mul]
    _ ≤ κ univ*(((κ univ)⁻¹*compressionBudget K n D a.capacity)*(hausdorff n X) B) :=
      mul_le_mul' le_rfl hb
    _ = _ := by rw [←mul_assoc,←mul_assoc,ENNReal.mul_inv_cancel hκ0 hκtop,one_mul]

end RegularPointCoordinates

end

end OAI
