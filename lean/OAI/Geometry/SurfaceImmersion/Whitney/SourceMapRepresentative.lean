import OAI.Geometry.SurfaceImmersion.Whitney.SourceArcChart

namespace OAI

/-! The original surface map in the constructed full-arc coordinates,
with an actual globally smooth representative near the entire rectangle. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem source_map_representative (P : SmoothCompactArc planeModel M)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f) :
    ∃ (c : OpenPartialHomeomorph M Base) (δ : ℝ) (φ : Base → V) (U : Set Base),
      0 < δ ∧ ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ φ ∧ IsOpen U ∧ U ⊆ c.target ∧ EqOn φ (f ∘ c.symm) U ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t]) ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (P.start-δ) (P.finish+δ), (![x,t] : Base) ∈ U) := by
  obtain ⟨c,δ,hδ,hcs,hci,haxis,hrect⟩ := source_arc_chart P
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  let K := T '' (Icc (-δ) δ ×ˢ Icc (P.start-δ) (P.finish+δ))
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image hT
  have hKt : K ⊆ c.target := by
    rintro x ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩
    exact hrect s hs t ht
  have hlocal : ContDiffOn ℝ ∞ (f ∘ c.symm) c.target :=
    (hf.comp_contMDiffOn hci).contDiffOn
  obtain ⟨U,hU,hKU,hUt,φ,hφ,hEq⟩ :=
    CollarVelocity.compact_smooth_extension hK c.open_target hKt hlocal
  refine ⟨c,δ,φ,U,hδ,hcs,hci,hφ,hU,hUt,hEq,haxis,?_⟩
  intro x hx t ht
  exact hKU ⟨(x,t),⟨hx,ht⟩,rfl⟩

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem coordinate_representative_immersion_iff (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U) :
    Function.Injective (fderiv ℝ φ x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) := by
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hbij := hcD.mfderiv_bijective (hUt hx)
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))]
  change Function.Injective ((mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) ∘
    (mfderiv 𝓘(ℝ,Base) planeModel c.symm x)) ↔ _
  constructor
  · intro h v w hvw
    obtain ⟨v',rfl⟩ := hbij.2 v
    obtain ⟨w',rfl⟩ := hbij.2 w
    exact congrArg (mfderiv 𝓘(ℝ,Base) planeModel c.symm x) (h hvw)
  · intro h
    exact h.comp hbij.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
