import OAI.Geometry.Relativity.CKS.ConstraintCompareInterior
import OAI.Geometry.Relativity.CKS.DenseInterior

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold
open scoped ContDiff Topology
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g K : InnerField I (M := M)} {x : M}
lemma ConstraintChart.compare (c d : ConstraintChart g K x) :
    c.energy = d.energy ∧ c.momentumNorm = d.momentumNorm := by
  let : NeBot (𝓝[I.interior M] x) :=
    mem_closure_iff_nhdsWithin_neBot.mp (CKSIntrinsicTopology.dense_interior I x)
  have heq : ∀ᶠ y in 𝓝[I.interior M] x,
      spatialEnergy c.metric c.tensor (c.coordinate y) = spatialEnergy d.metric d.tensor (d.coordinate y) ∧
      coordinateMomentumNorm c.metric c.tensor (c.coordinate y) =
        coordinateMomentumNorm d.metric d.tensor (d.coordinate y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (c.isOpen.mem_nhds c.mem),
      nhdsWithin_le_nhds (d.isOpen.mem_nhds d.mem)] with y hy hcy hdy
    exact (c.at y hcy).compare_interior (d.at y hdy) hy
  constructor
  · exact tendsto_nhds_unique_of_eventuallyEq
      (((c.continuous_energy x c.mem).continuousAt (c.isOpen.mem_nhds c.mem)).mono_left nhdsWithin_le_nhds)
      (((d.continuous_energy x d.mem).continuousAt (d.isOpen.mem_nhds d.mem)).mono_left nhdsWithin_le_nhds)
      (heq.mono fun _ h => h.1)
  · exact tendsto_nhds_unique_of_eventuallyEq
      (((c.continuous_momentumNorm x c.mem).continuousAt (c.isOpen.mem_nhds c.mem)).mono_left nhdsWithin_le_nhds)
      (((d.continuous_momentumNorm x d.mem).continuousAt (d.isOpen.mem_nhds d.mem)).mono_left nhdsWithin_le_nhds)
      (heq.mono fun _ h => h.2)

omit [IsManifold I ∞ M] in
lemma chart_exists_of_DECAt [IsManifold I ∞ M] (h : PhysicalDECAt I g K x) :
    ∃ c : ConstraintChart g K x, c.momentumNorm ≤ c.energy := by
  rcases h with ⟨V,f,A,B,hV,hx,hf,hfull,hs,hpos,hrep,hdec⟩
  exact ⟨⟨V,f,A,B,hV,hx,hf,hfull,hs,hpos,hrep⟩,hdec⟩

theorem exists_canonical_constraint_densities
    (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (hDEC : PhysicalDEC I g.inner K) :
    ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm := by
  classical
  choose atlas hbound using fun x => chart_exists_of_DECAt (hDEC x)
  let C : M → ℝ := fun x => (atlas x).energy
  let Q : M → ℝ := fun x => (atlas x).momentumNorm
  have hsame (x : M) (c : ConstraintChart g.inner K x) : C x = c.energy ∧ Q x = c.momentumNorm :=
    (atlas x).compare c
  have hc : Continuous C := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have heq : C =ᶠ[𝓝 x] (fun y => spatialEnergy (atlas x).metric (atlas x).tensor ((atlas x).coordinate y)) := by
      filter_upwards [(atlas x).isOpen.mem_nhds (atlas x).mem] with y hy
      exact (hsame y ((atlas x).at y hy)).1
    exact (((atlas x).continuous_energy x (atlas x).mem).continuousAt
      ((atlas x).isOpen.mem_nhds (atlas x).mem)).congr heq.symm
  have hq : Continuous Q := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have heq : Q =ᶠ[𝓝 x] (fun y => coordinateMomentumNorm (atlas x).metric (atlas x).tensor ((atlas x).coordinate y)) := by
      filter_upwards [(atlas x).isOpen.mem_nhds (atlas x).mem] with y hy
      exact (hsame y ((atlas x).at y hy)).2
    exact (((atlas x).continuous_momentumNorm x (atlas x).mem).continuousAt
      ((atlas x).isOpen.mem_nhds (atlas x).mem)).congr heq.symm
  exact ⟨C,Q,hc,hq,(fun x => ⟨Real.sqrt_nonneg _,hbound x⟩),hsame⟩
end CKSIntrinsicConstraints

end

end OAI
