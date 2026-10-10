import OAI.Geometry.SurfaceImmersion.Geometry.LocalSardTransfer

namespace OAI

/-! Surjectivity in split coordinates is equivalent to surjectivity of
the vertical derivative when the first component is the first coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem split_linear_surjective {K : (ℝ × E) →L[ℝ] (ℝ × F)}
    (hfirst : ∀ v, (K v).1 = v.1)
    (hvert : Function.Surjective (fun v : E => (K (0,v)).2)) :
    Function.Surjective K := by
  rintro ⟨a,y⟩
  obtain ⟨v,hv⟩ := hvert (y-(K (a,0)).2)
  refine ⟨(a,v),?_⟩
  apply Prod.ext
  · exact hfirst _
  · have h := congrArg Prod.snd (map_add K (a,0) (0,v))
    simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.snd_add] at h
    dsimp only at hv
    rw [h,hv]
    abel

theorem slice_derivative_not_surjective {f : (ℝ × E) → ℝ × F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hfirst : ∀ z ∈ U, (f z).1 = z.1) (a : ℝ) (x : E) (hx : (a,x) ∈ U)
    (hcrit : ¬ Function.Surjective (fderiv ℝ f (a,x))) :
    ¬ Function.Surjective (fderiv ℝ (fun y : E => (f (a,y)).2) x) := by
  have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have he : (fun z => (f z).1) =ᶠ[𝓝 (a,x)] Prod.fst :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,hfirst⟩
  have he' : (ContinuousLinearMap.fst ℝ ℝ F).comp (fderiv ℝ f (a,x)) =
      ContinuousLinearMap.fst ℝ ℝ E := by
    rw [← fderiv.fst hfd,he.fderiv_eq (𝕜 := ℝ),fderiv_fst]
  have hpair : HasFDerivAt (fun y : E => (a,y)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have hv := ((hfd.hasFDerivAt.comp x hpair).snd).fderiv
  dsimp only [Function.comp_def] at hv
  intro hs
  apply hcrit
  apply split_linear_surjective (fun v => congrArg (fun L : (ℝ × E) →L[ℝ] ℝ => L v) he')
  intro y
  obtain ⟨v,hv'⟩ := hs y
  refine ⟨v,?_⟩
  rw [hv] at hv'
  exact hv'

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
