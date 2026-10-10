import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.FibreNonfocal
import OAI.Geometry.WeakMTW.Coordinates.PairExpCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def Nonconjugate (x : M) (v : TangentSpace (model n) x) : Prop :=
    Function.Injective (fderiv ℝ (fun w => chartAt (Model n) (exp x v) (exp x w)) v)

 theorem nonconjugate_of_mem_injectivity (x : M) {v : TangentSpace (model n) x}
    (hv : v ∈ injectivityDomain x) : Nonconjugate x v :=
    exp_coordinates_injective_derivative x (exp x v) hv (mem_chart_source (Model n) (exp x v))

 theorem nonfocal_line_zero (x y : M) {v w : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun u => chartAt (Model n) y (exp x u)) v))
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hc : HasDerivAt (fun s : ℝ => chartAt (Model n) y (exp x (v+s•w))) 0 0) : w = 0 := by
  have hd : HasDerivAt (fun s : ℝ => v+s•w) w 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v using 1
    simp
  have hF := ((exp_coordinates_smooth x y hy).differentiableAt (by simp)).hasFDerivAt
  have hF' : HasFDerivAt (fun u => chartAt (Model n) y (exp x u))
      (fderiv ℝ (fun u => chartAt (Model n) y (exp x u)) v) (v+(0 : ℝ)•w) := by simpa using hF
  have hh := (hF'.comp_hasDerivAt (l := fun u => chartAt (Model n) y (exp x u)) (f := fun s : ℝ => v+s•w) 0 hd).unique hc
  apply hn
  simpa only [map_zero] using hh

 theorem pairExpCoordinates_injective_of_nonfocal (x y : M) {v : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v)) (hy : exp x v ∈ (chartAt (Model n) y).source) :
    Function.Injective (fderiv ℝ (pairExpCoordinates (n := n) x y)
      (stateChart x (⟨x,v⟩ : TangentBundle (model n) M))) := by
  let q₀ := stateChart x (⟨x,v⟩ : TangentBundle (model n) M)
  have hsrc : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hdom : q₀ ∈ pairExpDomain (n := n) x y := by
    refine ⟨(stateChart x).map_source hsrc,?_⟩
    dsimp only [q₀]
    rw [(stateChart x).left_inv hsrc]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source
    simpa only [← exp_eq_geodesic] using hy
  have hs := (pairExpCoordinates_smooth x y _ hdom).contDiffAt ((pairExpDomain_open x y).mem_nhds hdom)
  have hD := (hs.differentiableAt (by simp)).hasFDerivAt
  rw [injective_iff_map_eq_zero]
  intro k hk
  change (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) k = 0 at hk
  have hf := (hasFDerivAt_fst (𝕜 := ℝ) (p := pairExpCoordinates (n := n) x y q₀)).comp q₀ hD
  have hf' : (ContinuousLinearMap.fst ℝ (Model n) (Model n)).comp
      (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) = ContinuousLinearMap.fst ℝ (Model n) (Model n) :=
    hf.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := q₀))
  have hk₁ : k.1 = 0 := by
    have hh := congrArg (fun A : (Model n × Model n) →L[ℝ] Model n => A k) hf'
    change ((fderiv ℝ (pairExpCoordinates (n := n) x y) q₀) k).1 = k.1 at hh
    rw [hk] at hh
    exact hh.symm
  let e := trivializationAt (Model n) (TangentSpace (model n)) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt (Model n) (TangentSpace (model n)) x
  let w : TangentSpace (model n) x := e.symmL ℝ x k.2
  let L := e.continuousLinearMapAt ℝ x
  have hL : L w = k.2 := e.continuousLinearMapAt_symmL he k.2
  have hcurve : HasDerivAt (fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) k 0 := by
    have hh : HasDerivAt (fun s : ℝ => (chartAt (Model n) x x,L v+s•L w)) (0,L w) 0 := by
      have hl : HasDerivAt (fun s : ℝ => L v+s•L w) (L w) 0 := by
        convert (hasDerivAt_const (0 : ℝ) (L v)).add ((hasDerivAt_id (0 : ℝ)).smul_const (L w)) using 1 <;> (first | rfl | simp)
      exact (hasDerivAt_const (0 : ℝ) (chartAt (Model n) x x)).prodMk hl
    have heq : (fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) =
        (fun s : ℝ => (chartAt (Model n) x x,L v+s•L w)) := by
      funext s
      rw [stateChart_vertical,map_add,map_smul]
    rw [heq]
    convert hh using 1
    exact Prod.ext hk₁ hL.symm
  have hD' : HasFDerivAt (pairExpCoordinates (n := n) x y) (fderiv ℝ (pairExpCoordinates (n := n) x y) q₀)
      (stateChart x (⟨x,v+(0 : ℝ)•w⟩ : TangentBundle (model n) M)) := by
    simpa only [zero_smul,add_zero] using hD
  have hcomp := hD'.comp_hasDerivAt (l := pairExpCoordinates (n := n) x y)
    (f := fun s : ℝ => stateChart x (⟨x,v+s•w⟩ : TangentBundle (model n) M)) 0 hcurve
  rw [hk] at hcomp
  have hcomp' : HasDerivAt (fun s : ℝ => (chartAt (Model n) x x, chartAt (Model n) y (exp x (v+s•w)))) 0 0 := by
    convert hcomp using 1
    funext s
    exact (pairExpCoordinates_vertical x y _).symm
  have hc₀ := (ContinuousLinearMap.snd ℝ (Model n) (Model n)).hasFDerivAt.comp_hasDerivAt 0 hcomp'
  have hc : HasDerivAt (fun s : ℝ => chartAt (Model n) y (exp x (v+s•w))) 0 0 := by
    exact hc₀
  have hw := nonfocal_line_zero x y hn hy hc
  have hk₂ : k.2 = 0 := by rw [hw,map_zero] at hL; exact hL.symm
  exact Prod.ext hk₁ hk₂

 theorem pairExpCoordinates_inverse_of_nonfocal (x y : M) {v : TangentSpace (model n) x}
    (hn : Function.Injective (fderiv ℝ (fun w => chartAt (Model n) y (exp x w)) v)) (hy : exp x v ∈ (chartAt (Model n) y).source) :
    ∃ e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n),
      (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y ∧
      stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ e.source ∧
      e.source ⊆ pairExpDomain (n := n) x y ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let q := stateChart x (⟨x,v⟩ : TangentBundle (model n) M)
  have hsrc : (⟨x,v⟩ : TangentBundle (model n) M) ∈ (stateChart x).source :=
    (stateChart_source x _).mpr (mem_chart_source (Model n) x)
  have hdom : q ∈ pairExpDomain (n := n) x y := by
    refine ⟨(stateChart x).map_source hsrc,?_⟩
    dsimp only [q]
    rw [(stateChart x).left_inv hsrc]
    apply (stateChart_source y _).mpr
    change geodesic (⟨x,v⟩ : TangentBundle (model n) M) 1 ∈ (chartAt (Model n) y).source
    simpa only [← exp_eq_geodesic] using hy
  let A := fderiv ℝ (pairExpCoordinates (n := n) x y) q
  let D := (LinearEquiv.ofInjectiveEndo A.toLinearMap (pairExpCoordinates_injective_of_nonfocal x y hn hy)).toContinuousLinearEquiv
  have hD : HasFDerivAt (pairExpCoordinates (n := n) x y) (D : (Model n × Model n) →L[ℝ] (Model n × Model n)) q := by
    exact (((pairExpCoordinates_smooth x y _ hdom).contDiffAt ((pairExpDomain_open x y).mem_nhds hdom)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e,he,hev,hes,hei,_⟩ := NormalNeighborhood.exists_smooth_local_diffeomorph
    (pairExpDomain_open x y) (pairExpCoordinates_smooth x y) hdom hD
  exact ⟨e,he,hev,hes,hei⟩

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
