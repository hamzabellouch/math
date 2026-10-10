import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

namespace OAI

/-! # The differential of group multiplication at the identity -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_mul_one (v : TangentSpace ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
    ((1 : G), (1 : G))) :
    mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (1, 1) v = v.1 + v.2 := by
  have hmul : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (1, 1) :=
    (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiableAt (by simp)
  have hl : (fun z : G => z * 1) = id := funext mul_one
  have hr : (fun z : G => 1 * z) = id := funext one_mul
  have hp := mfderiv_prod_eq_add_apply (v := v) hmul
  have hL : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => z * 1) 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [hl, mfderiv_id]
    rfl
  have hR : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun z : G => 1 * z) 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [hr, mfderiv_id]
    rfl
  let v₁ : E := v.1
  let v₂ : E := v.2
  exact hp.trans (congrArg₂ (fun a b : E => a + b)
    (congrArg (fun l : E →L[ℝ] E => l v₁) hL)
    (congrArg (fun l : E →L[ℝ] E => l v₂) hR))

theorem HasMFDerivAt.mul_at_one {f g : M → G} {x : M}
    {df dg : TangentSpace I x →L[ℝ] E}
    (hf : HasMFDerivAt I (𝓘(ℝ, E)) f x df)
    (hg : HasMFDerivAt I (𝓘(ℝ, E)) g x dg)
    (hf1 : f x = 1) (hg1 : g x = 1) :
    HasMFDerivAt I (𝓘(ℝ, E)) (fun y => f y * g y) x (df + dg) := by
  have hmul : MDifferentiableAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
      (fun p : G × G => p.1 * p.2) (f x, g x) :=
    (contMDiff_mul (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiableAt (by simp)
  have hh := hmul.hasMFDerivAt.comp x (hf.prodMk hg)
  apply hh.congr_mfderiv
  ext w
  change mfderiv ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E))
    (fun p : G × G => p.1 * p.2) (f x, g x) (df w, dg w) = df w + dg w
  rw [hf1, hg1]
  exact mfderiv_mul_one _

end PolycyclicRecognition

end

end OAI
