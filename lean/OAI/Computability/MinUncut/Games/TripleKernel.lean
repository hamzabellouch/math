import Mathlib
import OAI.Computability.MinUncut.Estimates.Density

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier OuterSmoothness
variable {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
local instance tripleKernelDecidableEq : DecidableEq W := Classical.decEq W
attribute [local instance] BinaryFourier.dualFintype

def tripleKernel (f : W → ℝ) (v : W × W × W) : ℝ :=
  f v.1 * f v.2.1 * f v.2.2 * f (v.1+v.2.1+v.2.2)

lemma tripleKernel_mean (f : W → ℝ) :
    (𝔼 v : W × W × W, tripleKernel f v) =
      ∑ α : Module.Dual F₂ W, coefficient f α ^ 4 := by
  unfold tripleKernel
  rw [expect_pair]
  simp_rw [expect_pair]
  exact fourth_moment f

omit [Module F₂ W] [Fintype W] in
lemma tripleKernel_abs (f : W → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ w, |f w| ≤ M) (v : W × W × W) : |tripleKernel f v| ≤ M^4 := by
  simp only [tripleKernel, abs_mul]
  calc _ ≤ M * M * M * M := by
         gcongr <;> exact hf _
       _ = _ := by ring

theorem adaptive_fourth_moment {B : Type*} [Fintype B] [Nonempty B]
    (p : Density (B × (W × W × W))) (f : B → W → ℝ) {M u : ℝ}
    (hM : 0 ≤ M) (hu : 0 < u) (hf : ∀ b w, |f b w| ≤ M) :
    (𝔼 z, p z * tripleKernel (remainder (f z.1) u) z.2) ≤
      u^2 * M^2 + 2 * p.tvUniform * (M + M^2/u)^4 := by
  let g : B × (W × W × W) → ℝ := fun z => tripleKernel (remainder (f z.1) u) z.2
  have hMr : 0 ≤ M + M^2/u := by positivity
  have hg (z : B × (W × W × W)) : |g z| ≤ (M + M^2/u)^4 :=
    tripleKernel_abs _ hMr (remainder_abs_bound (f z.1) hM hu (hf z.1)) z.2
  have hdiff := Density.expect_difference p g (pow_nonneg hMr _) hg
  have hmean : (𝔼 z, g z) ≤ u^2 * M^2 := by
    change (𝔼 z : B × (W × W × W), tripleKernel (remainder (f z.1) u) z.2) ≤ _
    rw [expect_pair]
    simp_rw [tripleKernel_mean]
    calc _ ≤ 𝔼 b : B, u^2 * M^2 := Finset.expect_le_expect (fun b _ =>
           remainder_fourth_bound (f b) hM hu (hf b))
         _ = _ := Fintype.expect_const _
  have habs := le_abs_self ((𝔼 z, p z * g z) - (𝔼 z, g z))
  dsimp only [g] at hdiff hmean habs
  linarith

end MinUncut.Composition

end

end OAI
