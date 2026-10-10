import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateGradient

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

 local instance tangentFiniteCoords (x : M) : FiniteDimensional ℝ (TangentSpace (model n) x) :=
   VectorBundle.finiteDimensional ℝ (Model n) _ x
 local instance tangentCompleteCoords (x : M) : CompleteSpace (TangentSpace (model n) x) :=
   FiniteDimensional.complete ℝ _

 theorem gradient_coordinate_pair {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ,ℝ) 1 f)
     (x y : M) (hy : y ∈ (chartAt (Model n) x).source) (v : TangentSpace (model n) y) :
     fderiv ℝ (fun X => f ((chartAt (Model n) x).symm X)) (chartAt (Model n) x y)
       (stateChart x ⟨y,v⟩).2 = inner ℝ (normalGradient f y) v := by
   let c := chartAt (Model n) x
   let q : TangentBundle (model n) M := ⟨y,v⟩
   have hγ := (geodesic_smooth q).mdifferentiable (by simp) 0
   have hγ₀ : geodesic q 0 = y := geodesic_zero q
   have hγsrc : geodesic q 0 ∈ c.source := hγ₀ ▸ hy
   have hdγ : HasDerivAt (c ∘ geodesic q) (stateChart x q).2 0 := by
     have hd := (mdifferentiableAt_iff_differentiableAt.mp
       ((((contMDiffOn_chart (n := ∞)).contMDiffAt (c.open_source.mem_nhds hγsrc)).mdifferentiableAt (by simp)).comp 0 hγ)).hasDerivAt
     rw [curveState_chart_deriv' x hγ hγsrc,geodesic_state_zero] at hd
     exact hd
   have hc : DifferentiableAt ℝ (fun X => f (c.symm X)) (c y) := by
     have hh : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) 1 (fun X => f (c.symm X)) (c y) :=
       hf.contMDiffAt.comp (c y) (contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source hy)))
     exact (contMDiffAt_iff_contDiffAt.mp hh).differentiableAt (by norm_num)
   have hd := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hdγ (by simp only [Function.comp_apply,hγ₀])
   have hD : HasDerivAt (fun t : ℝ => f (exp y (t•v)))
       (fderiv ℝ (fun h : TangentSpace (model n) y => f (exp y h)) 0 v) 0 := by
     have he := hf.comp ((exp_fibre_smooth y).of_le (by simp : (1:ℕ∞ω) ≤ ∞))
     have hh := ((contMDiffAt_iff_contDiffAt.mp (he 0)).differentiableAt
       (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0
       ((hasDerivAt_id (0:ℝ)).smul_const v) (by simp)
     simpa only [one_smul,Function.comp_def,id_eq] using hh
   have hn : (fun t => (fun X => f (c.symm X)) ((c ∘ geodesic q) t)) =ᶠ[𝓝 0]
       (fun t => f (exp y (t•v))) := by
     have hh := (geodesic_smooth q).continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hγsrc)
     filter_upwards [hh] with t ht
     simp only [Function.comp_apply,c.left_inv ht]
     exact congrArg f (exp_mul_eq_geodesic q t).symm
   have heq := (hd.congr_of_eventuallyEq hn.symm).unique hD
   have hir : inner ℝ (normalGradient f y) v =
       fderiv ℝ (fun h : TangentSpace (model n) y => f (exp y h)) 0 v := by
     exact congrArg (fun L : TangentSpace (model n) y →L[ℝ] ℝ => L v)
       ((InnerProductSpace.toDual ℝ (TangentSpace (model n) y)).apply_symm_apply _)
   exact heq.trans hir.symm

 theorem normalGradient_coordinates {f : M → ℝ} (hf : ContMDiff (model n) 𝓘(ℝ,ℝ) 1 f)
     (x y : M) (hy : y ∈ (chartAt (Model n) x).source) :
     (stateChart x (⟨y,normalGradient f y⟩ : TangentBundle (model n) M)).2 =
       (metric x (chartAt (Model n) x y)).inverse
         (fderiv ℝ (fun X => f ((chartAt (Model n) x).symm X)) (chartAt (Model n) x y)) := by
   let e := trivializationAt (Model n) (TangentSpace (model n)) x
   have hb : y ∈ e.baseSet := by simpa only [e,TangentBundle.trivializationAt_baseSet] using hy
   have hEq : metric x (chartAt (Model n) x y)
       (stateChart x (⟨y,normalGradient f y⟩ : TangentBundle (model n) M)).2 =
       fderiv ℝ (fun X => f ((chartAt (Model n) x).symm X)) (chartAt (Model n) x y) := by
     ext w
     let v := (e.continuousLinearEquivAt ℝ y hb).symm w
     have hv : (stateChart x (⟨y,v⟩ : TangentBundle (model n) M)).2 = w := by
       change e.continuousLinearEquivAt ℝ y hb v = w
       exact (e.continuousLinearEquivAt ℝ y hb).apply_symm_apply w
     rw [←hv,stateChart_pairing x y hy,gradient_coordinate_pair hf x y hy]
   rw [←hEq]
   exact ((metric_invertible (fun _ hv => metric_positive x ((chartAt (Model n) x).map_source hy) hv)).inverse_apply_self _).symm
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
