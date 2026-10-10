import Mathlib
import OAI.Geometry.WeakMTW.Variations.ParametricTaylor

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace MovingTaylor
variable {E F P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [Fintype ι]

 theorem collision_limits {B : E × F → ℝ} {C : ι → E × P → ℝ}
    {x₀ e : E} {y₀ : F} {a₀ : ι → P} {β₀ : ℝ} {θ₀ : ι → ℝ}
    (hB : ContDiffAt ℝ ∞ B (x₀,y₀)) (hC : ∀ i, ContDiffAt ℝ ∞ (C i) (x₀,a₀ i))
    {x d : ℕ → E} {y : ℕ → F} {a : ℕ → ι → P} {β l : ℕ → ℝ} {θ : ℕ → ι → ℝ}
    (hx : Tendsto x atTop (𝓝 x₀)) (hd : Tendsto d atTop (𝓝 e))
    (hy : Tendsto y atTop (𝓝 y₀)) (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (a₀ i)))
    (hβ : Tendsto β atTop (𝓝 β₀)) (hθ : ∀ i, Tendsto (fun j => θ j i) atTop (𝓝 (θ₀ i)))
    (hl : Tendsto l atTop (𝓝 0)) (hlpos : ∀ᶠ j in atTop, 0 < l j)
    (hθpos : ∀ᶠ j in atTop, ∀ i, 0 ≤ θ j i)
    (hineq : ∀ᶠ j in atTop, ∀ i,
      B (x j+l j•d j,y j)-B (x j,y j) -
      β j*(C i (x j+l j•d j,a j i)-C i (x j,a j i)) ≤ 0)
    (hcancel : ∀ᶠ j in atTop, ∑ i, θ j i *
      (fderiv ℝ B (x j,y j) (d j,0)-β j*fderiv ℝ (C i) (x j,a j i) (d j,0)) = 0) :
    (∀ i, fderiv ℝ B (x₀,y₀) (e,0)-β₀*fderiv ℝ (C i) (x₀,a₀ i) (e,0) ≤ 0) ∧
    (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) -
      β₀*fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0)) ≤ 0) := by
  have hlne := hlpos.mono (fun _ hj => hj.ne')
  constructor
  · intro i
    have hlim := (param_first_limit hB hx hd hy hl hlne).sub
      (hβ.mul (param_first_limit (hC i) hx hd (ha i) hl hlne))
    apply le_of_tendsto hlim
    filter_upwards [hlpos,hineq] with j hj hji
    have hh := div_nonpos_of_nonpos_of_nonneg (hji i) hj.le
    convert hh using 1
    ring
  · have hlimB := param_second_limit hB hx hd hy hl hlne
    have hlimC (i : ι) := param_second_limit (hC i) hx hd (ha i) hl hlne
    have hlim := tendsto_finsetSum Finset.univ (fun i _ => (hθ i).mul (hlimB.sub (hβ.mul (hlimC i))))
    have hle : ∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) / 2 -
        β₀*(fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0) / 2)) ≤ 0 := by
      apply le_of_tendsto hlim
      filter_upwards [hlpos,hθpos,hineq,hcancel] with j hj hjθ hji hjc
      let DB := fderiv ℝ B (x j,y j) (d j,0)
      let DC := fun i => fderiv ℝ (C i) (x j,a j i) (d j,0)
      let VB := B (x j+l j•d j,y j)-B (x j,y j)
      let VC := fun i => C i (x j+l j•d j,a j i)-C i (x j,a j i)
      change ∑ i, θ j i*((VB-l j*DB)/(l j)^2-β j*((VC i-l j*DC i)/(l j)^2)) ≤ 0
      have heq : (∑ i, θ j i*((VB-l j*DB)/(l j)^2-β j*((VC i-l j*DC i)/(l j)^2))) =
          ((∑ i, θ j i*(VB-β j*VC i))-l j*(∑ i, θ j i*(DB-β j*DC i)))/(l j)^2 := by
        rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [heq,hjc,mul_zero,sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg (Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hjθ i) (hji i))) (sq_nonneg _)
    have heq : (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) / 2 -
        β₀*(fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0) / 2))) =
        (∑ i, θ₀ i * (fderiv ℝ (fderiv ℝ B) (x₀,y₀) (e,0) (e,0) -
        β₀*fderiv ℝ (fderiv ℝ (C i)) (x₀,a₀ i) (e,0) (e,0))) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq] at hle
    linarith
end MovingTaylor
end

end WeakMTWGlobalSupport

end OAI
