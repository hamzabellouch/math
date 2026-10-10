import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectionTangentGeneric

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

noncomputable def oldOffsetDerivative (c : NashBoundaryChart (m := m) U V B q)
    (s : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) :
    Affine m →L[ℝ] (Fin c.normal.normalDim → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp c.normal.realCoordinates.toContinuousLinearMap -
    (fderiv ℝ c.normal.graph s).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp c.normal.realCoordinates.toContinuousLinearMap)

 theorem oldOffset_hasFDerivAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    HasFDerivAt c.oldOffset (c.oldOffsetDerivative s) (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.hasFDerivAt (x := c.oldPosition s)
  have hP := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hQ := (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hφ := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  have hφ' : HasFDerivAt c.normal.graph (fderiv ℝ c.normal.graph s)
      (c.oldParameter (c.oldPosition s)) := by simpa only [oldParameter_oldPosition] using hφ
  exact hQ.sub (hφ'.comp (c.oldPosition s) hP)

 theorem oldOffsetDerivative_surjective (c : NashBoundaryChart (m := m) U V B q) (s) :
    Function.Surjective (c.oldOffsetDerivative s) := by
  intro v
  refine ⟨c.normal.realCoordinates.symm (0,v),?_⟩
  change (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).2 -
    fderiv ℝ c.normal.graph s (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).1 = v
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero,sub_zero]

theorem oldOffsetDerivative_generic (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ ((LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap) : Set (Affine m)) = ⊤ := by
  let f : (Fin d → ℝ) → Affine m := fun y => c.chart.projection (q y-q c.center)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hD : HasFDerivAt c.oldOffset (c.oldOffsetDerivative (c.normal.parameters x)) (f x) := by
    dsimp only [f]
    rw [← c.oldPosition_projection hgood]
    exact c.oldOffset_hasFDerivAt hgood.2.1
  have hz : (c.oldOffsetDerivative (c.normal.parameters x)).comp (fderiv ℝ f x) = 0 :=
    ((hD.comp x hf.hasFDerivAt).congr_of_eventuallyEq (c.oldOffset_projection_germ hgood).symm).unique (hasFDerivAt_const (0 : Fin c.normal.normalDim → ℝ) x)
  have hle : range (fderiv ℝ f x) ⊆ ((LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap) : Set (Affine m)) := by
    rintro _ ⟨v,rfl⟩
    change c.oldOffsetDerivative (c.normal.parameters x) (fderiv ℝ f x v) = 0
    exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin c.normal.normalDim → ℝ) => L v) hz
  have hgen := (c.projection_tangent_generic hgood hq hqi hr).2
  apply top_unique
  rw [← hgen]
  exact Submodule.span_mono hle
end Release061.NashBoundaryChart

namespace Release061
open Set Filter Topology Flatten
open scoped Classical

theorem real_surjection_normal_factor {r l k : ℕ}
    (M : (Affine r × Affine l) →L[ℝ] (Fin k → ℝ))
    (hM : Function.Surjective M)
    (hker : ∀ z, M z = 0 ↔ Flatten.imaginaryPart l z.2 = 0) :
    ∃ L : (Fin l → ℝ) ≃L[ℝ] (Fin k → ℝ),
      ∀ z, M z = L (Flatten.imaginaryPart l z.2) := by
  let j : (Fin l → ℝ) →L[ℝ] (Affine r × Affine l) :=
    (ContinuousLinearMap.inr ℝ (Affine r) (Affine l)).comp
      (((Complex.I • ContinuousLinearMap.id ℂ (Affine l)).restrictScalars ℝ).comp (Flatten.realEmbedding l))
  have hj (v : Fin l → ℝ) : Flatten.imaginaryPart l (j v).2 = v := by
    ext i
    simp [j,Flatten.imaginaryPart,Flatten.realEmbedding]
  let L := M.comp j
  have hf (z : Affine r × Affine l) : M z = L (Flatten.imaginaryPart l z.2) := by
    have hz : M (z-j (Flatten.imaginaryPart l z.2)) = 0 := by
      apply (hker _).mpr
      change Flatten.imaginaryPart l (z.2-(j (Flatten.imaginaryPart l z.2)).2) = 0
      rw [map_sub,hj,sub_self]
    exact sub_eq_zero.mp (by simpa only [map_sub,L,ContinuousLinearMap.comp_apply] using hz)
  have hi : Function.Injective L := by
    intro u v huv
    apply sub_eq_zero.mp
    have hz : M (j (u-v)) = 0 := by change L (u-v)=0; rw [map_sub,huv,sub_self]
    simpa only [hj] using (hker _).mp hz
  have hs : Function.Surjective L := by
    intro y
    obtain ⟨z,hz⟩ := hM y
    exact ⟨Flatten.imaginaryPart l z.2,by rw [← hf,hz]⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,hf⟩

theorem generic_surjective_real_normal_form {m k : ℕ}
    (D : Affine m →L[ℝ] (Fin k → ℝ)) (hD : Function.Surjective D)
    (hgen : Submodule.span ℂ ((LinearMap.ker D.toLinearMap) : Set (Affine m)) = ⊤) :
    ∃ (r l : ℕ) (e : Affine m ≃L[ℂ] (Affine r × Affine l))
      (L : (Fin l → ℝ) ≃L[ℝ] (Fin k → ℝ)),
      r+l=m ∧ l=k ∧ ∀ z, D (e.symm z) = L (Flatten.imaginaryPart l z.2) := by
  obtain ⟨r,e,hdim,hker⟩ := generic_tangent_complex_normal_form (LinearMap.ker D.toLinearMap) hgen
  let l := Module.finrank ℝ (LinearMap.ker D.toLinearMap).dualAnnihilator
  let M := D.comp (e.symm.toContinuousLinearMap.restrictScalars ℝ)
  have hM : Function.Surjective M := hD.comp e.symm.surjective
  have he : ∀ z, M z = 0 ↔ Flatten.imaginaryPart l z.2 = 0 := by
    intro z
    change e.symm z ∈ LinearMap.ker D.toLinearMap ↔ _
    rw [hker,ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨fun h => funext h,fun h i => congrFun h i⟩
  obtain ⟨L,hL⟩ := real_surjection_normal_factor M hM he
  have hlk : l=k := by simpa only [Module.finrank_pi,Fintype.card_fin] using L.toLinearEquiv.finrank_eq
  exact ⟨r,l,e,L,hdim,hlk,hL⟩
end Release061

end

end OAI
