import OAI.Analysis.CircleDomains.Modulus.FixedCoreBarrierPayment
import OAI.Analysis.CircleDomains.Topology.SourceMapNeighborhood

namespace OAI

/-! A fixed source real barrier gives an open exclusion of conformal maps. The neighborhood
retains only compact source traces; later model limits may use different core exhaustions. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_open_fixed_core_real_exclusion
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (B : SmoothJordanCore G) (j : Fin B.count)
    (F₀ : ℂ → ℂ) (hF₀ : ContinuousOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (ho₀ : ∀ U, IsOpen U → U ⊆ ((↑) : ℂ → Sphere) ⁻¹' G → IsOpen (F₀ '' U))
    (hi₀ : InjOn F₀ (((↑) : ℂ → Sphere) ⁻¹' G))
    (J₀ : ℂ ≃ₜ ℂ)
    (hboundary₀ : extendAtInfinity F₀ ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J₀))
    (hside₀ : extendAtInfinity F₀ ''
      (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F₀ '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior J₀))
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (c : ℂ) (δ : ℝ) (hanchor : closedBall c δ ⊆ F₀ '' jordanInterior H)
    (hd : Disjoint (closedBall c δ) (closure (jordanInterior J₀)))
    {Q : Set ℂ} (hQ : IsCompact Q) (hQinner : Q ⊆ jordanInterior J₀)
    {W : Set ℂ} (hW : IsClosed W) (hWconvex : Convex ℝ W)
    (hQW : Q ⊆ W) (hBW : closedBall c δ ⊆ W)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (F₀ '' P) W)
    (rot : Circle) {J : Set ℝ} (hJ : MeasurableSet J)
    (hprojection : J ⊆ (fun z => ((rotation rot).symm z).im) '' Q ∩
      Ioo (((rotation rot).symm c).im - δ) (((rotation rot).symm c).im + δ))
    (R : ℝ) (hWR : W ⊆ closedBall 0 R) :
    ∃ V : Set C(FiniteSource G, ℂ), IsOpen V ∧ finiteSourceMap F₀ hF₀ ∈ V ∧
      ∀ {S : Type*} {π : Sphere → Sphere} {σ : S → Sphere}
        {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
        (M : RealModelExhaustion d O ε) (A : AssignedRealModelLimit M) (l : ℕ),
        Tendsto ε atTop (𝓝 0) → 3 * M.radius ≤ R →
        (∀ z ∈ frontier (jordanInterior (B.disk j)),
          d.physical l (Complex.equivRealProdCLM z) = 1) →
        (∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0) →
        Real.sqrt Real.pi * R * Real.sqrt
          (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
            gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
          2 * R * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) < (volume J).toReal →
        finiteSourceMap A.function (A.plane_open_embedding hG).1 ∉ V := by
  let γ : C(Circle, FiniteSource G) :=
    ⟨fun t => ⟨B.curve j t, B.boundary_subset_domain j
      ⟨B.curve j t, (B.boundary j) ▸ mem_range_self t, rfl⟩⟩,
      (B.embedding j).continuous.subtype_mk _⟩
  obtain ⟨q, hqG, hqB⟩ := exists_domain_point_inside_jordan hG (B.disk j)
    (B.boundary_subset_domain j)
  let a : FiniteSource G := ⟨q, hqG⟩
  have ha : (finiteSourceMap F₀ hF₀) a ∈ jordanInterior J₀ := by
    change F₀ q ∈ jordanInterior J₀
    have hh := mem_image_of_mem (extendAtInfinity F₀)
      (show (q : Sphere) ∈ G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j)) from
        ⟨hqG, q, hqB, rfl⟩)
    rw [hside₀] at hh
    simpa only [finiteSourceMap, ContinuousMap.coe_mk, a, extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hh.2
  have hfront : range ((finiteSourceMap F₀ hF₀).comp γ) = frontier (jordanInterior J₀) := by
    change range (fun t => F₀ (B.curve j t)) = _
    simpa only [finiteSourceMap, γ, ContinuousMap.comp_apply, ContinuousMap.coe_mk, extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (B.boundary j) hboundary₀
        (fun t => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  obtain ⟨V₁, hV₁, hmem₁, hcontrol⟩ := exists_open_jordan_map_control
    (finiteSourceMap F₀ hF₀) γ a J₀ hfront ha hQ hQinner
    isClosed_closedBall.isOpen_compl
    (fun z hz hzb => Set.disjoint_left.mp hd hzb hz)
  obtain ⟨V₂, hV₂, hmem₂, hanchorControl⟩ := exists_open_source_anchor_control
    hsch hG F₀ hF₀ ho₀ hi₀ H hHG (isCompact_closedBall c δ) hanchor
  let V₃ : Set C(FiniteSource G, ℂ) := {f | Disjoint (f '' {x | x.val ∈ P}) W}
  have hV₃ : IsOpen V₃ := isOpen_source_image_disjoint hP hPG hW
  have hmem₃ : finiteSourceMap F₀ hF₀ ∈ V₃ := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    exact Set.disjoint_left.mp hPW (mem_image_of_mem F₀ hx) hz
  refine ⟨V₁ ∩ V₂ ∩ V₃, (hV₁.inter hV₂).inter hV₃, ⟨⟨hmem₁, hmem₂⟩, hmem₃⟩, ?_⟩
  intro S π σ d O ε M A l hε hR hone hzero hsmall hmem
  have hA := A.plane_open_embedding hG
  obtain ⟨J', _, _, hb', hs'⟩ := exists_matched_image_core hsch hG hconn
    (B.subset (interior_subset B.infty_interior)) A.conformal.1 A.conformal.bijOn.injOn
    (by simp) B
  have ha' : (finiteSourceMap A.function hA.1) a ∈ jordanInterior (J' j) := by
    change A.function q ∈ jordanInterior (J' j)
    have hh := mem_image_of_mem (extendAtInfinity A.function)
      (show (q : Sphere) ∈ G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j)) from
        ⟨hqG, q, hqB, rfl⟩)
    rw [hs' j] at hh
    simpa only [finiteSourceMap, ContinuousMap.coe_mk, a, extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hh.2
  have hfront' : range ((finiteSourceMap A.function hA.1).comp γ) =
      frontier (jordanInterior (J' j)) := by
    change range (fun t => A.function (B.curve j t)) = _
    simpa only [finiteSourceMap, γ, ContinuousMap.comp_apply, ContinuousMap.coe_mk, extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (B.boundary j) (hb' j)
        (fun t => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  have hgeometry := hcontrol _ hmem.1.1 (J' j) hfront' ha'
  have hanchor' := hanchorControl A.function hA.1 hmem.1.2 hA.2.1 hA.2.2
  have hPW' : Disjoint (A.function '' P) W := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    exact Set.disjoint_left.mp hmem.2
      (show A.function x ∈ (finiteSourceMap A.function hA.1) '' {y | y.val ∈ P} from
        ⟨⟨x, hPG hx⟩, hx, rfl⟩) hz
  have hbound := A.fixed_core_barrier_payment hsch harea hG hε B j l (J' j)
    (hb' j) (hs' j) hone H hHG hzero c δ hanchor'
    (Set.disjoint_left.mpr fun z hz hzc => hgeometry.2 hzc hz)
    hQ hgeometry.1 hW hWconvex hQW hBW hP hPG hPW' rot hJ hprojection hR hWR
  exact (not_lt_of_ge hbound) hsmall

end CircleDomainRigidity

end

end OAI
