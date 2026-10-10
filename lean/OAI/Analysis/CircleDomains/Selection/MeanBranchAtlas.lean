import OAI.Analysis.CircleDomains.Selection.CountableLogarithmicCover
import OAI.Analysis.CircleDomains.Selection.MeanBranchBounds
import OAI.Analysis.CircleDomains.Selection.LiftedMeanBands
import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle
import OAI.Analysis.CircleDomains.Sobolev.BoundedLocalBranches

namespace OAI

/-! Bounded real representatives for the actual mean on a punctured
spherical mask. The countable logarithmic atlas and every bound are
constructed from the compact arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_bounded_mean_branch_atlas
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) (F : C(Sphere, ℂ))
    (S U : Set Sphere) (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : K ∂(η : Measure K), F x ∉ range γ.val) :
    ∃ (I : Type) (_ : Countable I) (V : I → Set Sphere) (a M : I → ℝ)
      (u : I → Sphere → ℝ),
      S ⊆ ⋃ i, V i ∧
      (∀ i, IsOpen (V i) ∧ closure (V i) ⊆ S) ∧
      (∀ i, ContinuousOn (fun x => logarithmicCutChart (a i) (F x)) (closure (V i))) ∧
      (∀ i x, |u i x| ≤ M i) ∧
      (∀ i, ContinuousOn (u i) (U ∩ V i)) ∧
      (∀ i x, x ∈ V i →
        u i x = meanGeometricIndex hsch K hKS η
          (upperHalfPlaneClamp (logarithmicCutChart (a i) (F x)))) ∧
      (∀ i x, x ∈ V i → (u i x : UnitAddCircle) = diskMeanCircle hsch K hKS η (F x)) := by
  obtain ⟨T, V, a, R, _, hTc, hcover, hlocal⟩ :=
    exists_countable_bounded_logarithmic_cover F S hS h0 h1
  let : Countable T := hTc
  let L : T → Sphere → ClosedUpperHalfPlane := fun i x =>
    upperHalfPlaneClamp (logarithmicCutChart (a i.val) (F x))
  let v : T → Sphere → ℝ := fun i x => meanGeometricIndex hsch K hKS η (L i x)
  have hbound (i : T) : ∃ M : ℝ, ∀ x ∈ V i.val, |v i x| ≤ M := by
    apply bounded_meanGeometricIndex_on_chart hsch K hK hKS η (V i.val) (L i) (R i.val)
    intro x hx
    dsimp only [L]
    rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x (subset_closure hx))]
    exact (hlocal i.val i.property).2.2.2.2.1 x (subset_closure hx)
  choose M hM using hbound
  let u : T → Sphere → ℝ := fun i => localBranchRepresentative (V i.val) (v i)
  have hMn (i : T) : 0 ≤ M i :=
    (abs_nonneg (v i i.val)).trans (hM i i.val (hlocal i.val i.property).2.1)
  have hcont (i : T) : ContinuousOn (v i) (U ∩ V i.val) := by
    have hL : ContinuousOn (L i) (closure (V i.val)) :=
      continuous_upperHalfPlaneClamp.comp_continuousOn (hlocal i.val i.property).2.2.2.1
    intro x hx
    have hxcl := subset_closure hx.2
    have hxS := (hlocal i.val i.property).2.2.1 hxcl
    have hp : diskRayProjection (L i x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x hxcl)]
      exact (hlocal i.val i.property).2.2.2.2.2.2 x hxcl
    have hm := continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L i x)
      (by simpa only [hp] using hmiss x ⟨hx.1, hxS⟩)
    exact hm.comp_continuousWithinAt ((hL x hxcl).mono (inter_subset_right.trans subset_closure))
  refine ⟨T, inferInstance, (fun i => V i.val), (fun i => a i.val), M, u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hiT, hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion.mpr ⟨⟨i, hiT⟩, hxi⟩
  · intro i
    exact ⟨(hlocal i.val i.property).1, (hlocal i.val i.property).2.2.1⟩
  · intro i
    exact (hlocal i.val i.property).2.2.2.1
  · intro i x
    exact localBranchRepresentative_bound (D := univ) (hMn i)
      (fun x hx => hM i x hx.2) x (mem_univ x)
  · intro i
    exact localBranchRepresentative_continuousOn (hcont i)
  · intro i x hx
    exact indicator_of_mem hx (v i)
  · intro i x hx
    have hp : diskRayProjection (L i x).val = F x := by
      dsimp only [L]
      rw [upperHalfPlaneClamp_val ((hlocal i.val i.property).2.2.2.2.2.1 x (subset_closure hx))]
      exact (hlocal i.val i.property).2.2.2.2.2.2 x (subset_closure hx)
    change (((V i.val).indicator (v i) x : ℝ) : UnitAddCircle) = _
    rw [indicator_of_mem hx]
    exact hp ▸ (diskMeanCircle_projection hsch hsep K hK hKS η (L i x)).symm

end CircleDomainRigidity

end

end OAI
