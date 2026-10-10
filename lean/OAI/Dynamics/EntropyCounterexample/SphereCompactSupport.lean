import Mathlib

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem340
namespace SphereCompactSupport

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {v : E} (hv : ‖v‖ = 1)

def extension (F : (ℝ ∙ v)ᗮ → W) (x : sphere (0 : E) 1) : W :=
  by
  classical
  exact if (x : E) = v then 0 else F (stereoToFun v x)

omit [NormedSpace ℝ W] in
@[simp] theorem extension_pole (F : (ℝ ∙ v)ᗮ → W) :
    extension F (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) = 0 := by
  simp [extension]

omit [NormedSpace ℝ W] in
theorem extension_of_ne (F : (ℝ ∙ v)ᗮ → W) {x : sphere (0 : E) 1}
    (hx : (x : E) ≠ v) : extension F x = F (stereoToFun v x) := by
  simp [extension, hx]

include hv in

theorem exists_local_ambient_extension
    {F : (ℝ ∙ v)ᗮ → W} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (x : sphere (0 : E) 1) :
    ∃ U : Set E, IsOpen U ∧ (x : E) ∈ U ∧ ∃ A : E → W,
      ContDiffOn ℝ ∞ A U ∧
      ∀ y : sphere (0 : E) 1, (y : E) ∈ U → extension F y = A y := by
  by_cases hx : (x : E) = v
  · let K : Set E := (fun w : (ℝ ∙ v)ᗮ => (stereoInvFun hv w : E)) '' tsupport F
    have hK : IsCompact K := hFc.image
      (continuous_subtype_val.comp (continuous_stereoInvFun hv))
    have hvK : v ∉ K := by
      rintro ⟨w, hw, heq⟩
      exact stereoInvFun_ne_north_pole hv w (Subtype.ext heq)
    refine ⟨Kᶜ, hK.isClosed.isOpen_compl, ?_, fun _ => 0, contDiffOn_const, ?_⟩
    · simpa [hx] using hvK
    · intro y hy
      by_cases hyv : (y : E) = v
      · simp [extension, hyv]
      · rw [extension_of_ne F hyv]
        by_contra hne
        apply hy
        refine ⟨stereoToFun v y, subset_closure hne, ?_⟩
        exact congrArg Subtype.val (stereo_left_inv hv hyv)
  · let U : Set E := {y | innerSL ℝ v y ≠ (1 : ℝ)}
    have hU : IsOpen U := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
    have hxU : (x : E) ∈ U := by
      intro h
      exact hx ((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere x)).mp h).symm
    refine ⟨U, hU, hxU, F ∘ stereoToFun v, ?_, ?_⟩
    · exact hF.comp_contDiffOn contDiffOn_stereoToFun
    · intro y hy
      apply extension_of_ne
      intro hyv
      apply hy
      simp [hyv, hv]

include hv in

theorem continuous_extension {F : (ℝ ∙ v)ᗮ → W}
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) :
    Continuous (extension F) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, A, hA, hmatch⟩ := exists_local_ambient_extension hv hF hFc x
  have hAc : ContinuousAt A (x : E) :=
    (hA.contDiffAt (hU.mem_nhds hx)).continuousAt
  apply (hAc.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with y hy
  exact hmatch y hy

end SphereCompactSupport
end Problem340

end

end OAI
