import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.GlobalTensorVanishing
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.FormalBoxes
import OAI.Geometry.SplitTangent.RationalTrivialization
import OAI.Geometry.SplitTangent.TwistedCurveTensor

namespace OAI

/-! Tensor Spanning. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent
namespace TwistedCurveTensor
variable {X : ComplexManifold.{u}} {g : RationalCurve X} {d : ℤ} {m : ℕ}

 

theorem infinity_zero_of_finite_zero (A : TwistedCurveTensor g d m)
    (h : ∀z,A.finite z=0) : ∀z,A.infinity z=0 := by
  have ho {z : ℂ} (hz : z≠0) : A.infinity z=0 := by
    have he := A.overlap z⁻¹ (inv_ne_zero hz)
    rw [h,inv_inv] at he
    exact (smul_eq_zero.mp he.symm).resolve_left (zpow_ne_zero _ (inv_ne_zero hz))
  have hall : (Set.univ : Set ℂ)⊆{z | A.infinity z=0} := by
    apply AnalyticContinuation.subset_of_local_analytic_equations
      (F := TangentTensor X m) isPreconnected_univ
    · intro z hz
      refine ⟨tangentTensorCoordinates g.infinity A.infinity z,A.infinity_holomorphic z,?_⟩
      let t := trivializationAt (Model X) (Tangent X) (g.infinity z)
      have hbase : g.infinity z∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
      filter_upwards [g.infinity_holomorphic.continuous.continuousAt.preimage_mem_nhds
        (t.open_baseSet.mem_nhds hbase)] with w hw
      exact (tangentTensorCoordinates_zero_iff hw).symm
    · refine ⟨1,Set.mem_univ _,mem_interior_iff_mem_nhds.mpr ?_⟩
      exact (eventually_ne_nhds (one_ne_zero : (1:ℂ)≠0)).mono fun z hz => ho hz
  exact fun z => hall (Set.mem_univ z)

 

theorem finite_zero_of_spanning_sections (A : TwistedCurveTensor g d m)
    (S : TangentSplitting X) {r : ℕ} (σ : Fin r → CurveTangentSection g)
    (hσ : ∀j z,(σ j).finite z∈S.first (g.finite z))
    (hspan : ∀v∈S.first (g.finite 1),∃a : Fin r → ℂ,∑j,a j • (σ j).finite 1=v)
    (hSupport : ∀z v,A.finite z (fun i => S.projector (g.finite z) (v i))=A.finite z v)
    (hcontract : ∀j : Fin m → Fin r,A.contract (σ ∘ j)=0) : ∀z,A.finite z=0 := by
  classical
  let t := trivializationAt (Model X) (Tangent X) (g.finite 1)
  let c := chartAt (Model X) (g.finite 1)
  let b := Pi.basisFun ℂ (Fin X.dim)
  let w (j : Fin r) (z : ℂ) :=
    (t (⟨g.finite z,(σ j).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2
  let M (z : ℂ) : (Fin r → ℂ) →L[ℂ] Model X :=
    ∑j,(ContinuousLinearMap.proj j).smulRight (w j z)
  let P (z : ℂ) := S.coordinateProjector (g.finite 1) (c (g.finite z))
  have hMb : ∀z j,M z ((Pi.basisFun ℂ (Fin r)) j)=w j z := by
    intro z j
    simp [M,Pi.basisFun_apply]
  have hM : ContinuousAt M 1 := by
    apply tendsto_finsetSum
    intro j hj
    exact (ContinuousLinearMap.smulRightL ℂ (Fin r → ℂ) (Model X)
      (ContinuousLinearMap.proj j)).continuous.continuousAt.comp
        (section_coordinates_analytic (σ j).finite_holomorphic 1).continuousAt
  have hP : ContinuousAt P 1 := by
    have hc : AnalyticAt ℂ (c ∘ g.finite) (1 : ℂ) :=
      TangentSplitting.coordinateCurve_analytic g.finite_holomorphic (g.finite 1) (mem_chart_source _ _)
    exact ((S.coordinateProjector_analytic (g.finite 1) _
      (c.map_source (mem_chart_source _ _))).comp (f := c ∘ g.finite) (x := (1 : ℂ)) hc).continuousAt
  have hbase : ∀ᶠz in 𝓝 (1 : ℂ),g.finite z∈t.baseSet :=
    g.finite_holomorphic.continuous.continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  have hPw : ∀z,g.finite z∈t.baseSet → ∀j,P z (w j z)=w j z := by
    intro z hz j
    change S.coordinateProjector (g.finite 1) (c (g.finite z))
      (t (⟨g.finite z,(σ j).finite z⟩ : TangentBundle (ModelWithCorners X) X.Carrier)).2=_
    rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz,S.coordinateProjector_fixed _ hz,
      (S.mem_first_iff _ _).mp (hσ j z)]
    exact t.continuousLinearMapAt_apply_of_mem ℂ hz _
  have hspan' : ∀j : Fin X.dim, ∃a : Fin r → ℂ,M 1 a=P 1 (b j) := by
    intro j
    obtain ⟨a,ha⟩ := hspan (S.projector (g.finite 1) (t.symmL ℂ (g.finite 1) (b j))) ⟨_,rfl⟩
    refine ⟨a,?_⟩
    have hz : g.finite 1∈t.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
    have he := congrArg (t.continuousLinearMapAt ℂ (g.finite 1)) ha
    simp only [map_sum,map_smul] at he
    change M 1 a=S.coordinateProjector (g.finite 1) (c (g.finite 1)) (b j)
    have hproj : S.coordinateProjector (g.finite 1) (c (g.finite 1)) (b j)=
        t.continuousLinearMapAt ℂ (g.finite 1)
          (S.projector (g.finite 1) (t.symmL ℂ (g.finite 1) (b j))) := by
      have hh := S.coordinateProjector_fixed (g.finite 1) hz
        (t.symmL ℂ (g.finite 1) (b j))
      change S.coordinateProjector (g.finite 1) (c (g.finite 1))
        (t.continuousLinearMapAt ℂ (g.finite 1) (t.symmL ℂ (g.finite 1) (b j)))=_ at hh
      rw [t.continuousLinearMapAt_symmL hz] at hh
      exact hh
    rw [hproj]
    rw [←he]
    simp only [M,sum_apply,ContinuousLinearMap.smulRight_apply]
    congr 1
    funext k
    rw [t.continuousLinearMapAt_apply_of_mem ℂ hz]
    rfl
  choose a ha using hspan'
  let K : Model X →L[ℂ] (Fin r → ℂ) :=
    ∑j,(ContinuousLinearMap.proj j).smulRight (a j)
  have hK : ∀j,K (b j)=a j := by intro j; simp [K,b,Pi.basisFun_apply]
  have hx : (M 1).comp K=P 1 := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro j
    change M 1 (K (b j))=P 1 (b j)
    rw [hK,ha]
  have hMK : ContinuousAt (fun z => (M z).comp K) 1 := hM.clm_comp continuousAt_const
  have hPP : ∀ᶠz in 𝓝 (1 : ℂ),∀v,P z (P z v)=P z v := by
    filter_upwards [hbase] with z hz
    exact S.coordinateProjector_idempotent _ (c.map_source hz)
  have hPM : ∀ᶠz in 𝓝 (1 : ℂ),∀v,P z ((M z).comp K v)=(M z).comp K v := by
    filter_upwards [hbase] with z hz
    intro v
    simp only [ContinuousLinearMap.comp_apply,M,sum_apply,
      ContinuousLinearMap.smulRight_apply,map_sum,map_smul,hPw z hz]
  have hRange := ProjectorSpanning.eventually_range_eq hP hMK hx hPP hPM
  apply A.finite_zero_of_eventually (z₀ := 1)
  filter_upwards [hbase,hRange] with z hz hRange
  let B := tangentTensorCoordinates g.finite A.finite 1 z
  have hB : ∀j : Fin m → Fin r,B (fun i => M z ((Pi.basisFun ℂ (Fin r)) (j i)))=0 := by
    intro j
    have hv := congrArg (fun s : DiagonalRationality.lineSections d => s.val.1 z) (hcontract j)
    change A.finite z (fun i => (σ (j i)).finite z)=0 at hv
    have he (i : Fin m) : t.symmL ℂ (g.finite z) (M z ((Pi.basisFun ℂ (Fin r)) (j i))) =
        (σ (j i)).finite z := by
      rw [hMb]
      change t.symmL ℂ (g.finite z) (t (⟨g.finite z,(σ (j i)).finite z⟩ :
        TangentBundle (ModelWithCorners X) X.Carrier)).2=_
      rw [← t.continuousLinearMapAt_apply_of_mem ℂ hz,t.symmL_continuousLinearMapAt hz]
    change A.finite z (fun i => t.symmL ℂ (g.finite z)
      (M z ((Pi.basisFun ℂ (Fin r)) (j i)))) = 0
    exact (congrArg (A.finite z) (funext he)).trans hv
  apply ContinuousMultilinearMap.ext
  intro v
  rw [← hSupport z v]
  have hv : ∀i,t.continuousLinearMapAt ℂ (g.finite z) (S.projector (g.finite z) (v i))∈
      LinearMap.range (M z).toLinearMap := by
    intro i
    have he : t.continuousLinearMapAt ℂ (g.finite z) (S.projector (g.finite z) (v i))∈
        LinearMap.range ((M z).comp K).toLinearMap := by
      rw [hRange]
      exact ⟨t.continuousLinearMapAt ℂ (g.finite z) (v i),S.coordinateProjector_fixed _ hz _⟩
    obtain ⟨a,ha⟩ := he
    exact ⟨K a,ha⟩
  have h := ProjectorSpanning.multilinear_zero_of_basis_range (M z) B hB _ hv
  change A.finite z (fun i => t.symmL ℂ (g.finite z)
    (t.continuousLinearMapAt ℂ (g.finite z) (S.projector (g.finite z) (v i))))=0 at h
  simpa only [t.symmL_continuousLinearMapAt hz,zero_apply] using h

end TwistedCurveTensor
end SplitTangent

end

end OAI
