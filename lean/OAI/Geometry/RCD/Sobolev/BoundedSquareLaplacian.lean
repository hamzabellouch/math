import OAI.Geometry.RCD.Sobolev.WeakLaplacianSquare

namespace OAI

/-! # Constructing the L² Laplacian of a bounded Lipschitz square -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A bounded function with bounded weak gradient has an actual L²
square-Laplacian, with the exact carré-du-champ formula. -/
theorem exists_weakLaplacian_square (f : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (C L : ℝ≥0) (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hgrad : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x ≤ L)
    (hd : IsWeakLaplacian μ hQ f d) :
    ∃ q : Lp ℝ 2 μ, IsWeakLaplacian μ hQ (SobolevSpace.square μ hQ f C) q ∧
      (q =ᵐ[μ] fun x => 2*(SobolevSpace.toLp μ hQ f x*d x+
        (SobolevSpace.minimalSlope μ hQ f x)^2)) := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.minimalSlope μ hQ f
  have hF : MemLp F ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable F) C
    (by simpa only [Real.norm_eq_abs] using hf)
  have hGs : MemLp (fun x => G x^2) 2 μ := by
    apply (Lp.memLp G).of_le_mul (c := (L:ℝ)) ((Lp.aestronglyMeasurable G).pow 2)
    filter_upwards [hgrad,(Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f)] with x hx h0
    change |G x^2| ≤ (L:ℝ)*|G x|
    change G x ≤ L at hx
    change 0 ≤ G x at h0
    rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg h0]
    nlinarith
  have hprod : MemLp (fun x => F x*d x) 2 μ := by
    simpa only [Pi.mul_apply,mul_comm] using! (Lp.memLp d).mul hF
  have hQ2 : MemLp (fun x => 2*(F x*d x+G x^2)) 2 μ := by
    simpa only [Pi.add_apply] using (hprod.add hGs).const_mul 2
  let q := hQ2.toLp (fun x => 2*(F x*d x+G x^2))
  have hq : q =ᵐ[μ] fun x => 2*(F x*d x+G x^2) := hQ2.coeFn_toLp
  refine ⟨q,weakLaplacian_square μ hQ f d q C hf hd ?_,hq⟩
  filter_upwards [hq,localGamma_self μ hQ f] with x hqx hγ
  rw [hqx,hγ]

end RegularPointCoordinates

end

end OAI
