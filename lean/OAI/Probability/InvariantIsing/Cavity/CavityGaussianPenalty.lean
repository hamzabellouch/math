import OAI.Probability.InvariantIsing.Cavity.CavityGaussianPenaltyAlgebra

namespace OAI

/-! Gaussian integration by parts with a nonuniform one-replica penalty.
The bound depends on the cavity projection size, not its maximum over
all spin configurations. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_gaussian_penalty_insertion {X : Type*} [Fintype X]
    {d : ℕ} {w : X → ℝ} (hw : GibbsReference w) (H D : X → ℝ)
    (A C : X → Fin (d + 1) → ℝ) :
    (∫ g, ∑ x, gaussianGibbs w H C g x * (D x + linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
    ∫ g, ∑ x, gaussianGibbs w H C g x *
      (D x + gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hiD (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x) μ := by
    apply (Integrable.of_bound (continuous_gaussianGibbs hw H C x).aestronglyMeasurable 1
      (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ gaussianGibbs w H C g x from
          finiteGibbs_nonneg hw _ x)]
        exact finiteGibbs_le_one hw _ x))).mul_const
  have hiL (x : X) : Integrable (fun g => gaussianGibbs w H C g x * linearGaussian A g x) μ := by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x
  have hiK (x : X) : Integrable (fun g => gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) μ := by
    simpa only [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
      integrable_replica_covariance (r := 1) hw H A C x (fun _ => x)
  have hleft (g : Fin (d + 1) → ℝ) :
      (∑ x, gaussianGibbs w H C g x * (D x + linearGaussian A g x)) =
        ∑ x, (gaussianGibbs w H C g x * D x + gaussianGibbs w H C g x * linearGaussian A g x) := by
    simp only [mul_add]
  have hright (g : Fin (d + 1) → ℝ) :
      (∑ x, gaussianGibbs w H C g x *
        (D x + gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) =
      ∑ x, (gaussianGibbs w H C g x * D x + gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hiLeft (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x +
      gaussianGibbs w H C g x * linearGaussian A g x) μ := (hiD x).add (hiL x)
  have hiRight (x : X) : Integrable (fun g => gaussianGibbs w H C g x * D x +
      gaussianGibbs w H C g x * (gaussianCross A C x x -
        ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)) μ := (hiD x).add (hiK x)
  simp_rw [hleft, hright]
  rw [integral_finsetSum _ (fun x _ => hiLeft x),
    integral_finsetSum _ (fun x _ => hiRight x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_add (hiD x) (hiL x), integral_add (hiD x) (hiK x)]
  congr 1
  simpa only [mul_comm] using gaussian_gibbs_insertion hw H A C x

/-- A penalty of `4c V` absorbs a covariance insertion bounded by
`c(V(x)+V(y))`, uniformly over the other base energy. -/
theorem cavity_gaussian_penalty_nonneg {X : Type*} [Fintype X]
    {d : ℕ} {w : X → ℝ} (hw : GibbsReference w) (H V : X → ℝ)
    (A C : X → Fin (d + 1) → ℝ) (c : ℝ)
    (hK : ∀ x y, |gaussianCross A C x y| ≤ c * (V x + V y)) :
    0 ≤ ∫ g, ∑ x, gaussianGibbs w H C g x * (4 * c * V x + linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  rw [cavity_gaussian_penalty_insertion hw H (fun x => 4 * c * V x) A C]
  apply integral_nonneg
  intro g
  exact cavity_covariance_penalty_nonneg (gaussianGibbs w H C g) V (gaussianCross A C)
    (fun x => finiteGibbs_nonneg hw _ x) (finiteGibbs_sum hw _) hK

end InvariantIsing

end

end OAI
