import OAI.Analysis.CircleDomains.Transfer.CountableRealTransfer
import OAI.Analysis.CircleDomains.Selection.RealCoordinateSubfamily
import OAI.Analysis.CircleDomains.Transfer.TransportedRealCoordinates
import OAI.Analysis.CircleDomains.Uniformization.BandLimits

namespace OAI

/-! Place the existing real barrier coordinates into the masked family
without changing their graph, physical function, or band endpoints. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

attribute [local instance] sphereMetric sphereBorel

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}

theorem CountableRealCoordinates.boundary_limits
    (d : CountableRealCoordinates G π σ) (l : ℕ) (s : S) :
    d.lower l s = liminf (d.coordinate l) (𝓝[d.source] (σ s)) ∧
      d.upper l s = limsup (d.coordinate l) (𝓝[d.source] (σ s)) := by
  have he := (d.band l s).symm.trans
    (intervalFiberHull_clusterGraph_eq_boundary_band (d.coordinate_bounded l) (d.labels_closure s))
  exact (Icc_eq_Icc_iff (sub_nonneg.mp (d.width_nonneg l s))).mp he

def CountableRealCoordinates.maskedCoordinate
    (d : CountableRealCoordinates G π σ) (hG : IsOpen G) (s₀ : S) (l : ℕ) :
    MaskedCoordinateData G d.source π σ := by
  classical
  let q : Sphere → ℝ := d.source.indicator (d.coordinate l)
  have hq (x : Sphere) (hx : x ∈ d.source) : q x = d.coordinate l x := indicator_of_mem hx _
  have hbound (x : Sphere) : |q x| ≤ |d.bound l| := by
    by_cases hx : x ∈ d.source
    · rw [hq x hx]
      exact (d.coordinate_bounded l x hx).trans (le_abs_self _)
    · simpa only [q, indicator_of_notMem hx, abs_zero] using abs_nonneg (d.bound l)
  have hpull (x : ℝ × ℝ) (hx : x ∈ realChartDomain G) :
      q (π (Complex.equivRealProdCLM.symm x : Sphere)) = d.physical l x := by
    rw [hq _ (d.source_map _ hx)]
    exact (d.pullback l _ hx).symm.trans
      (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  refine {
    graph := circleBandGraph d.source (d.coordinate l)
    graph_closed := (isCompact_circleBandGraph (d.coordinate_bounded l)).isClosed
    mask := univ
    mask_closed := isClosed_univ
    mask_frontier := by simp
    singular := s₀
    Index := Unit
    patch := fun _ => univ
    patch_open := fun _ => isOpen_univ
    cover := by
      intro x _
      exact mem_iUnion.mpr ⟨(), mem_univ _⟩
    branch := fun _ => q
    bound := fun _ => |d.bound l|
    branch_bounded := fun _ => hbound
    physical := fun x => (d.physical l x : UnitAddCircle)
    measurable := (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp (d.physical_measurable l)
    gradient_measurable := measurable_circleGradient
      ((AddCircle.continuous_mk' (1 : ℝ)).measurable.comp (d.physical_measurable l))
    smooth := ?_
    energy := ?_
    physical_graph := ?_
    branch_smooth := ?_
    branch_projection := ?_
    lower := d.lower l
    upper := d.upper l
    width_nonneg := d.width_nonneg l
    width_summable := d.width_summable l
    marked_fiber := ?_
    marked_branch := ?_
    free_fiber := ?_ }
  · simpa only [physicalMask, preimage_univ, realChartDomain, interior_univ, inter_univ] using
      smoothCircleOn_coe (isOpen_realChartDomain hG) (d.physical_smooth l)
  · simp only [physicalMask, preimage_univ, realChartDomain, Measure.restrict_univ]
    apply (d.physical_energy l).ae_eq
    filter_upwards [ae_restrict_mem (isOpen_realChartDomain hG).measurableSet] with x hx
    exact (circleGradient_coe_eq_planarGradient (isOpen_realChartDomain hG)
      (d.physical_smooth l) hx).symm
  · intro x hx
    apply (circleBandGraph_on_open d.source_open (d.coordinate_continuous l)
      (d.source_map _ hx.1)).mpr
    congr 1
    exact (d.pullback l _ hx.1).symm.trans
      (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  · intro i
    apply ((d.physical_smooth l).mono inter_subset_left).congr
    intro x hx
    exact hpull x hx.1
  · intro i x hx
    exact congrArg (fun r : ℝ => (r : UnitAddCircle)) (hpull x hx.1)
  · intro s t ht
    obtain ⟨⟨x, a⟩, ha, he⟩ := ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨a, (d.band l s ▸ ha), rfl⟩
  · intro s _ _
    have heq : q =ᶠ[𝓝[d.source] (σ s)] d.coordinate l := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hq x hx
    refine ⟨(), mem_univ _, ?_, ?_⟩
    · exact (d.boundary_limits l s).1.trans (liminf_congr heq).symm
    · exact (d.boundary_limits l s).2.trans (limsup_congr heq).symm
  · intro x hx hfree t ht u hu
    obtain ⟨a, ha⟩ := d.free_trace x hx hfree l
    obtain ⟨⟨y, b⟩, hb, he⟩ := ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨⟨y, c⟩, hc, he⟩ := hu
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hb' : b = a := mem_singleton_iff.mp (ha ▸ hb)
    have hc' : c = a := mem_singleton_iff.mp (ha ▸ hc)
    exact congrArg (fun r : ℝ => (r : UnitAddCircle)) (hb'.trans hc'.symm)

def CountableRealCoordinates.realSubfamily
    (d : CountableRealCoordinates G π σ) (hG : IsOpen G) (s₀ : S) :
    RealCoordinateSubfamily (d.maskedCoordinate hG s₀) id where
  physical := d.physical
  quotient := d.coordinate
  bound := d.bound
  bounded := d.coordinate_bounded
  full_mask := fun _ => rfl
  smooth := d.physical_smooth
  energy := d.physical_energy
  pullback l x hx := (d.pullback l _ hx).symm.trans
    (congrArg (d.physical l) (Complex.equivRealProdCLM.apply_symm_apply x))
  projection := fun _ _ => rfl
  width l s := by
    change limsup (d.coordinate l) (𝓝[d.source] (σ s)) -
      liminf (d.coordinate l) (𝓝[d.source] (σ s)) ≤ d.upper l s - d.lower l s
    rw [← (d.boundary_limits l s).1, ← (d.boundary_limits l s).2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
