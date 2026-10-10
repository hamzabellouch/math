import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParametricSubmersion
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! # Continuous local inverse sections with parameters

For the square amplitude map in a generator scheme, the parameter-preserving
inverse function theorem supplies a continuous choice of amplitudes, jointly
with the normalized group law. Its source bound is retained explicitly for
the subsequent measurable endpoint sampling.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Metric
open scoped Topology

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace P] [CompleteSpace E] [CompleteSpace F] in
theorem parameter_joint_derivative_bijective (D : (P × E) →L[ℝ] F)
    (hD : Function.Bijective (fun v : E => D (0, v))) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ P E).prod D) := by
  refine ⟨?_, parameter_joint_derivative_surjective D hD.2⟩
  rintro ⟨p, v⟩ ⟨q, w⟩ he
  have hp : p = q := congrArg Prod.fst he
  subst q
  have hs : D (p, v) = D (p, w) := congrArg Prod.snd he
  have hv : D (0, v) = D (0, w) := by
    have ha (t : E) : D (p, t) = D (p, 0) + D (0, t) := by
      rw [← map_add]
      congr 1
      simp
    rw [ha v, ha w] at hs
    exact add_left_cancel hs
  exact Prod.ext rfl (hD.1 hv)

/-- Nearby parameters admit a common target ball and continuous local
amplitude choices of the prescribed bounded size. -/
theorem exists_parametric_inverse_section (f : P × E → F) (p : P)
    (hf : ContDiffAt ℝ 1 f (p, 0)) (hz : f (p, 0) = 0)
    (hbij : Function.Bijective (fun v : E => fderiv ℝ f (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ s : P × F → E, ContinuousOn s (U ×ˢ ball 0 ε) ∧
        ∀ q ∈ U, ∀ y ∈ ball (0 : F) ε, f (q, s (q, y)) = y ∧ ‖s (q, y)‖ < R := by
  let H : P × E → P × F := fun z => (z.1, f z)
  let D := (ContinuousLinearMap.fst ℝ P E).prod (fderiv ℝ f (p, 0))
  have hD : Function.Bijective D := parameter_joint_derivative_bijective _ hbij
  let eD : (P × E) ≃L[ℝ] (P × F) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hD.1) (LinearMap.range_eq_top.mpr hD.2)
  have hderiv : HasStrictFDerivAt H (eD : (P × E) →L[ℝ] (P × F)) (p, 0) := by
    change HasStrictFDerivAt H D (p, 0)
    exact (hasStrictFDerivAt_fst (p := (p, (0 : E)))).prodMk
      (hf.hasStrictFDerivAt one_ne_zero)
  let e := hderiv.toOpenPartialHomeomorph H
  have hsource : (p, (0 : E)) ∈ e.source := hderiv.mem_toOpenPartialHomeomorph_source
  have hvalue : H (p, 0) = (p, (0 : F)) := by simp [H, hz]
  have htarget : (p, (0 : F)) ∈ e.target := by
    simpa only [hvalue] using hderiv.image_mem_toOpenPartialHomeomorph_target
  have hinv : e.symm (p, 0) = (p, (0 : E)) := by
    rw [← hvalue]
    exact e.left_inv hsource
  have hcont : ContinuousAt e.symm (p, (0 : F)) := e.continuousAt_symm htarget
  have hsmall : e.symm ⁻¹' ((univ : Set P) ×ˢ ball (0 : E) R) ∈ 𝓝 (p, (0 : F)) := by
    apply hcont.preimage_mem_nhds
    rw [hinv]
    exact prod_mem_nhds Filter.univ_mem (ball_mem_nhds _ hR)
  have hN := inter_mem (e.open_target.mem_nhds htarget) hsmall
  obtain ⟨U, V, hU, hp, hV, h0, hUV⟩ := mem_nhds_prod_iff'.mp hN
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let s : P × F → E := fun z => (e.symm z).2
  have hsub : U ×ˢ ball (0 : F) ε ⊆ e.target := fun z hz =>
    (hUV ⟨hz.1, hεV hz.2⟩).1
  refine ⟨U, hU, hp, ε, hε, s,
    continuous_snd.comp_continuousOn (e.symm.continuousOn.mono hsub), ?_⟩
  intro q hq y hy
  have ht := hsub (show (q, y) ∈ U ×ˢ ball (0 : F) ε from ⟨hq, hy⟩)
  have he := e.right_inv ht
  have hp' : (e.symm (q, y)).1 = q := congrArg Prod.fst he
  have hf' : f (e.symm (q, y)) = y := congrArg Prod.snd he
  have hpair : e.symm (q, y) = (q, s (q, y)) := Prod.ext hp' rfl
  refine ⟨?_, ?_⟩
  · rw [hpair] at hf'
    exact hf'
  · have hm := (hUV (show (q, y) ∈ U ×ˢ V from ⟨hq, hεV hy⟩)).2
    exact mem_ball_zero_iff.mp hm.2

end PolycyclicRecognition

end

end OAI
