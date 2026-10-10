import Mathlib.Analysis.Normed.Module.Connected
import OAI.Geometry.NodalSets.Charts.SphereChartOpenMap
import OAI.Geometry.NodalSets.Elliptic.IntrinsicCompactWeakEquation
import OAI.Geometry.NodalSets.Persistence.RealWeakUniqueContinuation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section

lemma sphere_base_preconnected : PreconnectedSpace Base := by
  apply isPreconnected_iff_preconnectedSpace.mp
  apply isPreconnected_sphere
  rw [← Module.finrank_eq_rank]
  norm_num [AmbientBase]

lemma intrinsic_chart_zero_from_germ (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (y : Yau.Jets.Coord) (hy : w =ᶠ[𝓝 (sphereChartCoordMap p y)] (fun _ ↦ 0)) :
    ∀ x, w (sphereChartCoordMap p x) = 0 := by
  have hy' : (w ∘ sphereChartCoordMap p) =ᶠ[𝓝 y] (fun _ ↦ 0) :=
    hy.comp_tendsto (sphereChartCoordMap_smooth p).continuous.continuousAt
  have hEq (x) : realEllipticResidual roundCoordDensity (intrinsicRealPotential rho lam p)
      (intrinsicRealPrincipal A p) (w ∘ sphereChartCoordMap p) x = 0 :=
    intrinsic_real_divergence_equation A rho hrp w lam he p x
  have hzero := real_global_unique_continuation roundCoordDensity (intrinsicRealPotential rho lam p)
    (w ∘ sphereChartCoordMap p) (intrinsicRealPrincipal A p) roundCoordDensity_smooth roundCoordDensity_pos
    (intrinsicRealPotential_smooth rho hr lam p) (intrinsicRealPrincipal_smooth A hA hs hp p)
    (intrinsicRealPrincipal_symmetric A hs p) (spherePullback_smooth w hw p)
    (intrinsicRealPrincipal_posDef A hs hp p) hEq y hy'
  intro x
  exact congrFun hzero x

theorem sphere_weak_unique_continuation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z))
    (p : Base) (hz : w =ᶠ[𝓝 p] (fun _ ↦ 0)) : w = 0 := by
  let := sphere_base_preconnected
  let Z := (tsupport w)ᶜ
  have hZ : IsOpen Z := (isClosed_tsupport w).isOpen_compl
  have hne : (univ ∩ Z).Nonempty := ⟨p,mem_univ _,notMem_tsupport_iff_eventuallyEq.mpr hz⟩
  have hclosed : closure Z ∩ univ ⊆ Z := by
    intro q hq
    let V := sphereChartCoordMap q '' (univ : Set Yau.Jets.Coord)
    have hV : IsOpen V := sphereChartCoordMap_isOpenMap q _ isOpen_univ
    have hqV : q ∈ V := ⟨0,mem_univ _,sphereChartCoordMap_zero q⟩
    obtain ⟨a,haV,haZ⟩ := mem_closure_iff.mp hq.1 V hV hqV
    obtain ⟨y,_,rfl⟩ := haV
    have hchart := intrinsic_chart_zero_from_germ A hA hs hp rho hr hrp w hw lam he q y
      (notMem_tsupport_iff_eventuallyEq.mp haZ)
    have hh : w =ᶠ[𝓝 q] (fun _ ↦ 0) := by
      filter_upwards [hV.mem_nhds hqV] with a ha
      obtain ⟨x,_,rfl⟩ := ha
      exact hchart x
    exact notMem_tsupport_iff_eventuallyEq.mpr hh
  have hall := isPreconnected_univ.subset_of_closure_inter_subset hZ hne hclosed
  funext q
  exact image_eq_zero_of_notMem_tsupport (hall (mem_univ q))

theorem sphere_eigenfunction_nonzero_on_open (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (hne : w ≠ 0)
    (U : Set Base) (hU : IsOpen U) (hUn : U.Nonempty) : ∃ p ∈ U, w p ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨p,hpU⟩ := hUn
  have hh : w =ᶠ[𝓝 p] (fun _ ↦ 0) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact hn q hq
  exact hne (sphere_weak_unique_continuation A hA hs hp rho hr hrp w hw lam he p hh)

end
end Yau.Target

end OAI
