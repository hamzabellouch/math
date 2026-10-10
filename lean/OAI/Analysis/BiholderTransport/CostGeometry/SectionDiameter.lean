import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.SectionOscillation
import OAI.Analysis.BiholderTransport.Regularity.LiftedSections

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SectionDiameter
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.liftedGapSection_diameter_sq (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v) (huv : IsCostDualPair u v)
    {x : M} {r : ℝ} (hr : 0≤r) {p q : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈liftedGapSection u v x r) (hq : q∈liftedGapSection u v x r) :
    ‖p-q‖^2≤8*(r+sectionOscillation u v x r) := by
  let m := (1/2:ℝ) • p+(1/2:ℝ) • q
  have hm : m∈liftedGapSection u v x r :=
    (hmtw.convex_liftedGapSection hu hv huv x r) hp hq (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨y₀,_,y₁,_,hmin,hmax,heq⟩ := sectionOscillation_extrema hv huv x hr
  have hpS := (mem_liftedGapSection_iff.mp hp).2
  have hqS := (mem_liftedGapSection_iff.mp hq).2
  have hmS := (mem_liftedGapSection_iff.mp hm).2
  have hpl := hmin _ hpS
  have hql := hmin _ hqS
  have hmu := hmax _ hmS
  have hpm := hp.2
  have hqm := hq.2
  have hmn := dualPair_gap_nonneg hv huv x (riemannianExp x m)
  rw [contactGap,cost_minimizingVector hm.1] at hmn
  have norm_m : ‖m‖^2=(‖p‖^2+‖q‖^2)/2-‖p-q‖^2/4 := by
    have hpar := parallelogram_law_with_norm ℝ p q
    dsimp [m]
    rw [←smul_add,norm_smul]
    norm_num
    nlinarith [hpar]
  rw [heq]
  nlinarith [norm_m]

end SectionDiameter
end WeakMTWTransport

end

end

section

noncomputable section
open Bundle Bornology Set MeasureTheory Manifold Filter Metric
open scoped ENNReal NNReal ContDiff Topology

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

end
end
end

end OAI
