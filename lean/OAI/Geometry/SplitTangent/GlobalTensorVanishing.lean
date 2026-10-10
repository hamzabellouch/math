import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.RationalTrivialization
import OAI.Geometry.SplitTangent.TwistedCurveTensor

namespace OAI

/-! Global Tensor Vanishing. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

lemma tangentTensorCoordinates_zero_iff {X : ComplexManifold.{u}} {m : ℕ}
    {g : ℂ → X.Carrier} {A : ℂ → TangentTensor X m} {z₀ z : ℂ}
    (hz : g z∈(trivializationAt (Model X) (Tangent X) (g z₀)).baseSet) :
    tangentTensorCoordinates g A z₀ z=0 ↔ A z=0 := by
  let t := trivializationAt (Model X) (Tangent X) (g z₀)
  constructor
  · intro h
    apply ContinuousMultilinearMap.ext
    intro v
    have h' := congrArg (fun B : TangentTensor X m => B (fun i => t.continuousLinearMapAt ℂ (g z) (v i))) h
    change A z (fun i => t.symmL ℂ (g z) (t.continuousLinearMapAt ℂ (g z) (v i)))=0 at h'
    have he : (fun i => t.symmL ℂ (g z)
        (t.continuousLinearMapAt ℂ (g z) (v i))) = v := by
      funext i
      exact t.symmL_continuousLinearMapAt hz (v i)
    rw [he] at h'
    exact h'
  · intro h
    apply ContinuousMultilinearMap.ext
    intro v
    simp [tangentTensorCoordinates,h]
    rfl

namespace TwistedCurveTensor
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {d m : ℕ}

 

theorem finite_zero_of_eventually {d : ℤ} (A : TwistedCurveTensor g d m)
    {z₀ : ℂ} (h : ∀ᶠz in 𝓝 z₀,A.finite z=0) : ∀z,A.finite z=0 := by
  have hall : (Set.univ : Set ℂ)⊆{z | A.finite z=0} := by
    apply AnalyticContinuation.subset_of_local_analytic_equations (F := TangentTensor X m) isPreconnected_univ
    · intro z hz
      refine ⟨tangentTensorCoordinates g.finite A.finite z,A.finite_holomorphic z,?_⟩
      let t := trivializationAt (Model X) (Tangent X) (g.finite z)
      have hbase : g.finite z∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
      filter_upwards [g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
        (t.open_baseSet.mem_nhds hbase)] with w hw
      exact (tangentTensorCoordinates_zero_iff hw).symm
    · exact ⟨z₀,Set.mem_univ _,mem_interior_iff_mem_nhds.mpr h⟩
  exact fun z => hall (Set.mem_univ z)

 

theorem finite_zero_of_pointedGenerated (A : TwistedCurveTensor g (d : ℤ) m)
    (S : TangentSplitting X) (hg : PointedGenerated g S.first) (hdm : d < m)
    (hSupport : ∀z v,A.finite z (fun i => S.projector (g.finite z) (v i))=A.finite z v) :
    ∀z,A.finite z=0 := by
  classical
  let t := trivializationAt (Model X) (Tangent X) (g.finite 1)
  let c := chartAt (Model X) (g.finite 1)
  let b := Pi.basisFun ℂ (Fin X.dim)
  let a (j : Fin X.dim) := S.projector (g.finite 1) (t.symmL ℂ (g.finite 1) (b j))
  have ha : ∀j,a j∈S.first (g.finite 1) := fun j => ⟨_,rfl⟩
  choose σ hσf hσi hσ0 hσ1 using fun j => hg (a j) (ha j)
  let w (j : Fin X.dim) (z : ℂ) :=
    (t (⟨g.finite z,(σ j).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  let M (z : ℂ) : Model X →L[ℂ] Model X :=
    ∑j,(ContinuousLinearMap.proj j).smulRight (w j z)
  let P (z : ℂ) := S.coordinateProjector (g.finite 1) (c (g.finite z))
  have hMb : ∀z j,M z (b j)=w j z := by
    intro z j
    simp [M,b,Pi.basisFun_apply]
  have hM : ContinuousAt M 1 := by
    apply tendsto_finsetSum
    intro j hj
    exact (ContinuousLinearMap.smulRightL ℂ (Model X) (Model X)
      (ContinuousLinearMap.proj j)).continuous.continuousAt.comp
        (section_coordinates_analytic (σ j).finite_holomorphic 1).continuousAt
  have hP : ContinuousAt P 1 := by
    have hc : AnalyticAt ℂ (c ∘ g.finite) (1 : ℂ) :=
      TangentSplitting.coordinateCurve_analytic g.finite_holomorphic (g.finite 1) (mem_chart_source _ _)
    have hp := (S.coordinateProjector_analytic (g.finite 1) _
      (c.map_source (mem_chart_source _ _))).comp (f := c ∘ g.finite) (x := (1 : ℂ)) hc
    exact hp.continuousAt
  have hbase : ∀ᶠz in 𝓝 (1 : ℂ),g.finite z∈t.baseSet :=
    g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  have hPw : ∀z,g.finite z∈t.baseSet → ∀j,P z (w j z)=w j z := by
    intro z hz j
    change S.coordinateProjector (g.finite 1) (c (g.finite z))
      (t (⟨g.finite z,(σ j).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2=_
    rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz,S.coordinateProjector_fixed _ hz,
      (S.mem_first_iff _ _).mp (hσf j z)]
    exact t.continuousLinearMapAt_apply_of_mem ℂ hz _
  have hx : M 1=P 1 := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    change M 1 (b j)=P 1 (b j)
    rw [hMb]
    dsimp only [w]
    rw [hσ1]
    change (t (⟨g.finite 1,S.projector (g.finite 1) (t.symmL ℂ (g.finite 1) (b j))⟩ :
      TangentBundle (ModelWithCorners X) X.Carrier)).2=P 1 (b j)
    rw [← t.continuousLinearMapAt_apply_of_mem ℂ (FiberBundle.mem_baseSet_trivializationAt' _)]
    dsimp only [P,TangentSplitting.coordinateProjector]
    rw [c.left_inv (mem_chart_source _ _)]
    rfl
  have hPP : ∀ᶠz in 𝓝 (1 : ℂ),∀v,P z (P z v)=P z v := by
    filter_upwards [hbase] with z hz
    exact S.coordinateProjector_idempotent _ (c.map_source hz)
  have hPM : ∀ᶠz in 𝓝 (1 : ℂ),∀v,P z (M z v)=M z v := by
    filter_upwards [hbase] with z hz
    intro v
    simp only [M,sum_apply,ContinuousLinearMap.smulRight_apply,map_sum,map_smul,
      hPw z hz]
  have hRange := ProjectorSpanning.eventually_range_eq hP hM hx hPP hPM
  apply A.finite_zero_of_eventually (z₀ := 1)
  filter_upwards [hbase,hRange] with z hz hRange
  let B := tangentTensorCoordinates g.finite A.finite 1 z
  have hB : ∀j : Fin m → Fin X.dim,B (fun i => M z (b (j i)))=0 := by
    intro j
    have hc := A.contract_zero hdm (fun i => σ (j i)) (fun i => hσ0 (j i))
    have hv := congrArg (fun s : DiagonalRationality.lineSections (d : ℤ) => s.val.1 z) hc
    change A.finite z (fun i => (σ (j i)).finite z)=0 at hv
    have he (i : Fin m) : t.symmL ℂ (g.finite z) (M z (b (j i))) =
        (σ (j i)).finite z := by
      rw [hMb]
      change t.symmL ℂ (g.finite z) (t (⟨g.finite z,(σ (j i)).finite z⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)).2=_
      rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz,t.symmL_continuousLinearMapAt hz]
    change A.finite z (fun i => t.symmL ℂ (g.finite z) (M z (b (j i)))) = 0
    exact (congrArg (A.finite z) (funext he)).trans hv
  apply ContinuousMultilinearMap.ext
  intro v
  rw [← hSupport z v]
  have hv : ∀i,t.continuousLinearMapAt ℂ (g.finite z) (S.projector (g.finite z) (v i))∈
      LinearMap.range (M z).toLinearMap := by
    intro i
    rw [hRange]
    exact ⟨t.continuousLinearMapAt ℂ (g.finite z) (v i),S.coordinateProjector_fixed _ hz _⟩
  have h := ProjectorSpanning.multilinear_zero_of_basis_range (M z) B hB _ hv
  change A.finite z (fun i => t.symmL ℂ (g.finite z)
    (t.continuousLinearMapAt ℂ (g.finite z) (S.projector (g.finite z) (v i))))=0 at h
  simpa only [t.symmL_continuousLinearMapAt hz,zero_apply] using h

end TwistedCurveTensor
end SplitTangent

end

end OAI
