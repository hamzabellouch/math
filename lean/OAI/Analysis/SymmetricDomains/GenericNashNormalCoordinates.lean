import Mathlib
import OAI.Analysis.SymmetricDomains.InjectiveConormalFinrank
import OAI.Analysis.SymmetricDomains.GenericTangentComplexNormal
import OAI.Analysis.SymmetricDomains.ComplexNashNormalGraph

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
namespace Release061
open Set Filter Topology Metric
open scoped Classical

structure NashNormalCoordinates {d m : ℕ}
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine m) (a : Fin d → ℝ) where
  tangentDim : ℕ
  normalDim : ℕ
  complex_dimension : tangentDim + normalDim = m
  real_dimension : d = (tangentDim+tangentDim)+normalDim
  coordinates : Affine m ≃L[ℂ] (Affine tangentDim × Affine normalDim)
  parameters : OpenPartialHomeomorph (Fin d → ℝ) (Fin ((tangentDim+tangentDim)+normalDim) → ℝ)
  radius : ℝ
  radius_pos : 0 < radius
  graph : (Fin ((tangentDim+tangentDim)+normalDim) → ℝ) → (Fin normalDim → ℝ)
  parameter_eq : (parameters : (Fin d → ℝ) → _) =
    fun x => (complexGraphRealEquiv tangentDim normalDim (coordinates (q x-q a))).1
  source_mem : a ∈ parameters.source
  inverse_zero : parameters.symm 0 = a
  ball_target : ball 0 radius ⊆ parameters.target
  inverse_mapsTo : MapsTo parameters.symm (ball 0 radius) B
  inverse_analytic : AnalyticOnNhd ℝ parameters.symm (ball 0 radius)
  inverse_semialgebraic : SemialgebraicOn (ball 0 radius) parameters.symm
  graph_analytic : AnalyticOnNhd ℝ graph (ball 0 radius)
  graph_semialgebraic : SemialgebraicOn (ball 0 radius) graph
  graph_zero : graph 0 = 0
  derivative_zero : fderiv ℝ graph 0 = 0
  graph_identity : ∀ s ∈ ball 0 radius,
    complexGraphRealEquiv tangentDim normalDim (coordinates (q (parameters.symm s)-q a)) = (s,graph s)
  local_graph_identity : ∀ᶠ x in 𝓝 a, parameters x ∈ ball 0 radius ∧
    complexGraphRealEquiv tangentDim normalDim (coordinates (q x-q a)) =
      (parameters x,graph (parameters x))

theorem generic_nash_normal_coordinates {d m : ℕ}
    (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine m) (hqa : AnalyticOnNhd ℝ q B)
    (hqs : SemialgebraicOn B (fun x => complexRealEquiv m (q x)))
    {a : Fin d → ℝ} (ha : a ∈ B)
    (hqi : Function.Injective (fderiv ℝ q a))
    (hqg : Submodule.span ℂ (range (fderiv ℝ q a)) = ⊤) :
    Nonempty (NashNormalCoordinates B q a) := by
  let S := LinearMap.range (fderiv ℝ q a).toLinearMap
  let k := Module.finrank ℝ S.dualAnnihilator
  obtain ⟨r,e,he,het⟩ := generic_tangent_complex_normal_form S hqg
  have hdk : d+k=2*m := injective_conormal_finrank (fderiv ℝ q a) hqi
  have hdr : d=(r+r)+k := by omega
  let er := e.toContinuousLinearMap.restrictScalars ℝ
  let u := fun x => e (q x-q a)
  have hua : AnalyticOnNhd ℝ u B := by
    intro x hx
    have hs : AnalyticAt ℝ (fun y => q y-q a) x := (hqa x hx).sub analyticAt_const
    exact (er.analyticAt (q x-q a)).comp (f := fun y => q y-q a) hs
  have hu0 : u a = 0 := by simp only [u,sub_self,map_zero]
  have hud : HasFDerivAt u (er.comp (fderiv ℝ q a)) a := by
    have hs : HasFDerivAt (fun x => q x-q a) (fderiv ℝ q a) a :=
      (hqa a ha).differentiableAt.hasFDerivAt.sub_const (q a)
    exact er.hasFDerivAt.comp a hs
  have hui : Function.Injective (fderiv ℝ u a) := by
    rw [hud.fderiv]
    exact e.injective.comp hqi
  have hut : ∀ v i, (((fderiv ℝ u a) v).2 i).im = 0 := by
    intro v i
    rw [hud.fderiv]
    exact (het ((fderiv ℝ q a) v)).mp ⟨v,rfl⟩ i
  let L := (complexGraphRealEquiv r k).toContinuousLinearMap.comp
    (er.comp (complexRealEquiv m).symm.toContinuousLinearMap)
  let P := (ContinuousLinearMap.fst ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp L
  let Q := (ContinuousLinearMap.snd ℝ (Fin ((r+r)+k) → ℝ) (Fin k → ℝ)).comp L
  have hPs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (u x)).1) := by
    have hh := (SemialgebraicOn.affine PolynomialSignSet.univ P.toLinearMap
      (-P (complexRealEquiv m (q a)))).comp hqs (fun _ _ => mem_univ _)
    apply hh.congr
    intro x _
    simp [P,L,u,er,sub_eq_add_neg]
  have hQs : SemialgebraicOn B (fun x => (complexGraphRealEquiv r k (u x)).2) := by
    have hh := (SemialgebraicOn.affine PolynomialSignSet.univ Q.toLinearMap
      (-Q (complexRealEquiv m (q a)))).comp hqs (fun _ _ => mem_univ _)
    apply hh.congr
    intro x _
    simp [Q,L,u,er,sub_eq_add_neg]
  obtain ⟨p,R,φ,hp,hps,hp0,hR,hRt,hRB,hia,his,hφa,hφs,hφ0,hφd,hgr,hlgr⟩ :=
    complex_nash_normal_graph B hB u hua hPs hQs ha hu0 hdr hui hut
  exact ⟨⟨r,k,he,hdr,e,p,R,hR,φ,hp,hps,hp0,hRt,hRB,hia,his,hφa,hφs,hφ0,hφd,hgr,hlgr⟩⟩
end Release061

end

end OAI
