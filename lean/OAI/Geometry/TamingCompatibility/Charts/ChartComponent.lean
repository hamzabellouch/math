import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Helmholtz
import OAI.Geometry.TamingCompatibility.Elliptic.DerivativeIndex
import OAI.Geometry.TamingCompatibility.Functional.PiCompact

namespace OAI

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.ManifoldLocalization
open MeasureTheory TemperedDistribution Set Function HilbertSobolev
open scoped Topology Manifold ContDiff SchwartzMap LineDeriv Laplacian RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (k : ℕ)

def chartComponent (j : DerivativeIndex) (p : A.centers) :
    globalH1 A k →L[ℝ] H Space (CoordinateFiber k) 0 :=
  PiLp.proj 2 _ p ∘L PiLp.proj 2 _ j ∘L (globalH1 A k).subtypeL

def chartRecover (p : A.centers) : globalH1 A k →L[ℝ] H Space (CoordinateFiber k) 1 :=
  (reindex (E := Space) (F := CoordinateFiber k) (0-1) (0+1)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∘L
    ((inclusion (E := Space) (F := CoordinateFiber k) (show (0:ℝ)-1 ≤ 0 by norm_num)).restrictScalars ℝ ∘L
        chartComponent A k none p -
      ((2*Real.pi)^2)⁻¹ • ∑ i : Fin (Module.finrank ℝ Space),
        (derivative (F := CoordinateFiber k) 0 (stdOrthonormalBasis ℝ Space i)).restrictScalars ℝ ∘L
          chartComponent A k (some i) p)

omit [T2Space X] in
lemma chartRecover_apply (p : A.centers) (u : globalH1 A k) :
    chartRecover A k p u = recover 0 (u.val none p) (fun i => u.val (some i) p) := by
  simp only [chartRecover, chartComponent, ContinuousLinearMap.comp_apply,
    _root_.sub_apply, _root_.smul_apply,
    _root_.sum_apply]
  unfold recover
  rfl

omit [T2Space X] in
lemma chartRecover_distribution (p : A.centers) (u : globalH1 A k) :
    toDistribution Space (CoordinateFiber k) 1 (chartRecover A k p u) =
      Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val none p) := by
  rw [chartRecover_apply]
  have hr := recover_distribution (E := Space) (F := CoordinateFiber k) 0
    (u.val none p) (fun i => u.val (some i) p)
  rw [show (0 : ℝ) + 1 = 1 by ring] at hr
  rw [hr]
  have hz (w : H Space (CoordinateFiber k) 0) :
      toDistribution Space (CoordinateFiber k) 0 w =
        Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 w := by
    simp [toDistribution]
  simp only [hz]
  have hd (i : Fin (Module.finrank ℝ Space)) := derivative_relation A k u i p
  change ∀ i : Fin (Module.finrank ℝ Space),
    ∂_{stdOrthonormalBasis ℝ Space i}
      (Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val none p)) =
      Lp.toTemperedDistributionCLM (CoordinateFiber k) volume 2 (u.val (some i) p) at hd
  simp only [← hd]
  rw [← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ Space)]
  exact EuclideanGreen.green_helmholtz _

omit [T2Space X] in
lemma chartRecover_inclusion (p : A.centers) (u : globalH1 A k) :
    inclusion (show (0:ℝ) ≤ 1 by norm_num) (chartRecover A k p u) = u.val none p := by
  apply toDistribution_injective (E := Space) (F := CoordinateFiber k) 0
  rw [toDistribution_inclusion, chartRecover_distribution]
  simp [toDistribution]

omit [T2Space X] in
lemma localizedLinear_zero_off (p : A.centers) (α : ManifoldForms.smoothForms X k)
    (y : Space) (hy : y ∉ coordinateSupport A p) : localizedLinear A k p α y = 0 := by
  change formCoordinates k (localizedFunction A p α.val y) = 0
  suffices h : localizedFunction A p α.val y = 0 by rw [h, map_zero]
  unfold localizedFunction
  by_cases ht : y ∈ (extChartAt Model p.val).target
  · rw [indicator_of_mem ht]
    have hn : (extChartAt Model p.val).symm y ∉ tsupport (A.partition p) := by
      intro h
      exact hy ⟨_,h,(extChartAt Model p.val).right_inv ht⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  · rw [indicator_of_notMem ht]

omit [T2Space X] in
lemma chart_restore (p : A.centers) (u : globalH1 A k) :
    LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
      (LocalRestriction.restrict volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
        (u.val none p)) = u.val none p := by
  let R := LocalRestriction.restrict (F := CoordinateFiber k) volume
    (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
  let D : ChartH1 A k →L[ℝ] Lp (CoordinateFiber k) 2 (volume : Measure Space) :=
    ((ContinuousLinearMap.adjoint R) ∘L R - ContinuousLinearMap.id ℝ _) ∘L
      PiLp.proj 2 _ p ∘L PiLp.proj 2 _ none
  have ht : LinearMap.range (localizeH1 A k) ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨α,rfl⟩
    change LocalRestriction.restore volume (coordinateSupport A p) _
      (R ((localizedLinear A k p α).toLp 2 volume)) - (localizedLinear A k p α).toLp 2 volume = 0
    rw [sub_eq_zero]
    apply LocalRestriction.restore_restrict
    filter_upwards [(localizedLinear A k p α).coeFn_toLp 2 volume] with y hy
    intro hn
    rw [hy]
    exact localizedLinear_zero_off A k p α y hn
  have h := (LinearMap.range (localizeH1 A k)).topologicalClosure_minimal ht D.isClosed_ker u.property
  exact sub_eq_zero.mp h

omit [T2Space X] in
lemma chartComponent_compact (p : A.centers) : IsCompactOperator (chartComponent A k none p) := by
  have hc := LocalRellich.realize_compact (F := CoordinateFiber k)
    (coordinateSupport A p) (coordinateSupport_compact A p) (show (0:ℝ) < 1 by norm_num)
  have h := (hc.comp_clm (chartRecover A k p)).clm_comp
    (LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet)
  have he : (chartComponent A k none p : globalH1 A k → H Space (CoordinateFiber k) 0) =
      (LocalRestriction.restore volume (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet) ∘
        (LocalRellich.realize (coordinateSupport A p) (coordinateSupport_compact A p).measurableSet
          (show (0:ℝ) ≤ 1 by norm_num)) ∘ (chartRecover A k p) := by
    funext u
    change u.val none p = _
    dsimp only [Function.comp_def, LocalRellich.realize, ContinuousLinearMap.comp_apply]
    change u.val none p = LocalRestriction.restore volume (coordinateSupport A p) _
      (LocalRestriction.restrict volume (coordinateSupport A p) _
        (inclusion (show (0:ℝ) ≤ 1 by norm_num) (chartRecover A k p u)))
    rw [chartRecover_inclusion, chart_restore]
  rw [he]
  exact h

omit [T2Space X] in
lemma h1ToL2_compact : IsCompactOperator (h1ToL2 A k) := by
  let f := ContinuousLinearMap.pi (fun p : A.centers => chartComponent A k none p)
  have hf : IsCompactOperator f :=
    CompactPi.pi_compact _ (chartComponent_compact A k)
  have h := hf.clm_comp (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toContinuousLinearMap
  have he : (zeroth A k).comp (globalH1 A k).subtypeL =
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : A.centers => Lp (CoordinateFiber k) 2 (volume : Measure Space))).symm.toContinuousLinearMap.comp f := by
    ext u p
    rfl
  have hg : IsCompactOperator ((zeroth A k).comp (globalH1 A k).subtypeL) := by
    rw [he]
    exact h
  exact hg.codRestrict (zeroth_mem_globalL2 A k)
    (LinearMap.range (localizeL2 A k)).isClosed_topologicalClosure

end TamingCompatibility.ManifoldLocalization

end

end OAI
