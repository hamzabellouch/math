import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Uniform local images for nearby parameters

Apply the ordinary submersion theorem to the joint map `(p,x) ↦ (p,f(p,x))`.
A surjective derivative in the second variable then gives a common image
neighborhood for all nearby parameters. This is the persistence step for
normalized generator product schemes.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set Metric
open scoped Topology

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace P] [CompleteSpace E] [CompleteSpace F] in
/-- Surjectivity in the second variable makes the parameter-preserving
joint differential surjective. -/
theorem parameter_joint_derivative_surjective (D : (P × E) →L[ℝ] F)
    (hD : Function.Surjective (fun v : E => D (0, v))) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ P E).prod D) := by
  rintro ⟨p, y⟩
  obtain ⟨v, hv⟩ := hD (y - D (p, 0))
  change D (0, v) = y - D (p, 0) at hv
  refine ⟨(p, v), ?_⟩
  change (p, D (p, v)) = (p, y)
  refine Prod.ext (by rfl) ?_
  change D (p, v) = y
  have he : (p, v) = (p, 0) + (0, v) := by simp
  rw [he, map_add, hv, add_sub_cancel]

/-- A fixed source ball covers a common target ball for all parameters in
one open neighborhood of the given parameter. -/
theorem exists_uniform_local_image (f : P × E → F) (p : P)
    (hf : ContDiffAt ℝ 1 f (p, 0)) (hz : f (p, 0) = 0)
    (hsurj : Function.Surjective (fun v : E => fderiv ℝ f (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ q ∈ U, ball (0 : F) ε ⊆ (fun x : E => f (q, x)) '' ball 0 R := by
  let H : P × E → P × F := fun z => (z.1, f z)
  have hH : ContDiffAt ℝ 1 H (p, 0) := contDiffAt_fst.prodMk hf
  have hderiv : fderiv ℝ H (p, 0) =
      (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ f (p, 0)) := by
    exact ((hasFDerivAt_fst (p := (p, (0 : E)))).prodMk
      (hf.differentiableAt one_ne_zero).hasFDerivAt).fderiv
  have hmap := (hH.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (by
      rw [hderiv]
      exact LinearMap.range_eq_top.mpr (parameter_joint_derivative_surjective _ hsurj))
  have hvalue : H (p, 0) = (p, 0) := by simp [H, hz]
  rw [hvalue] at hmap
  have hsource : (univ : Set P) ×ˢ ball (0 : E) R ∈ 𝓝 (p, 0) :=
    prod_mem_nhds Filter.univ_mem (ball_mem_nhds _ hR)
  have himage : H '' ((univ : Set P) ×ˢ ball (0 : E) R) ∈ 𝓝 (p, (0 : F)) := by
    rw [← hmap]
    exact Filter.image_mem_map hsource
  obtain ⟨U, V, hU, hp, _hV, h0, hUV⟩ := mem_nhds_prod_iff'.mp himage
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (_hV.mem_nhds h0)
  refine ⟨U, hU, hp, ε, hε, ?_⟩
  intro q hq y hy
  obtain ⟨⟨q', x⟩, hx, he⟩ := hUV (show (q, y) ∈ U ×ˢ V from ⟨hq, hεV hy⟩)
  have heq : q' = q := congrArg Prod.fst he
  subst q'
  exact ⟨x, hx.2, congrArg Prod.snd he⟩

end PolycyclicRecognition

end

end OAI
