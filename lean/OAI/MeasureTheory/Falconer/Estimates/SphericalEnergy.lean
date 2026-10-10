import OAI.MeasureTheory.Falconer.Graphs.GraphSchur
import OAI.MeasureTheory.Falconer.Angular.SphereModel
import OAI.MeasureTheory.Falconer.Shells.RadialShellMass

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def sphereMoment {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖U (r,w)‖^2 ∂sphereMeasure d

theorem sphereMoment_nonneg {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) :
    0 ≤ sphereMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem sphereMoment_measurable {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) : Measurable (sphereMoment U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem sphere_norm_square_integrable {d : ℕ} (U : Sphere d → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w, ‖U w‖ ≤ C) :
    Integrable (fun w => ‖U w‖^2) (sphereMeasure d) := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb w)

theorem sphereMoment_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment U r ≤ C^2 * (sphereMeasure d).real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb (r,w))

noncomputable def independentAngularEnergy {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    (U V : ℝ × Sphere d → ℂ) : ℝ :=
  (2 : ℝ)^((d : ℝ)*(v-a)) *
    ∫ r, sphereMoment U r * sphereMoment V r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

theorem independentAngularEnergy_nonneg {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    (U V : ℝ × Sphere d → ℂ) : 0 ≤ independentAngularEnergy a v Ψ U V :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (integral_nonneg (fun r => mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r)))

theorem sphere_product_square_integral {d : ℕ} (U V : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d, ‖U z.1 * V z.2‖^2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, ‖U w‖^2 ∂sphereMeasure d) * (∫ w, ‖V w‖^2 ∂sphereMeasure d) := by
  simp only [norm_mul, mul_pow]
  exact integral_prod_mul (fun w => ‖U w‖^2) (fun w => ‖V w‖^2)

/-- Bounded measurable endpoint transforms give an integrable square on
the full radial and independent angular product. -/
theorem angular_product_square_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2)
      ((PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
        ((sphereMeasure d).prod (sphereMeasure d))) := by
  have hmU : Measurable (fun z : ℝ × (Sphere d × Sphere d) => U (z.1,z.2.1)) :=
    hU.comp (measurable_fst.prodMk measurable_snd.fst)
  have hmV : Measurable (fun z : ℝ × (Sphere d × Sphere d) => V (z.1,z.2.2)) :=
    hV.comp (measurable_fst.prodMk measurable_snd.snd)
  apply Integrable.of_bound ((hmU.mul hmV).norm.pow_const 2).aestronglyMeasurable ((C*D)^2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hD)).mpr
  change ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖ ≤ C * D
  rw [norm_mul]
  exact mul_le_mul (hbU _) (hbV _) (norm_nonneg _) hC

theorem independentAngularEnergy_product_integral {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V = (2 : ℝ)^((d : ℝ)*(v-a)) *
      ∫ z : ℝ × (Sphere d × Sphere d), ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d)) := by
  have hi := angular_product_square_integrable v Ψ U V hU hV hC hD hbU hbV
  rw [independentAngularEnergy, integral_prod _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  exact (sphere_product_square_integral (fun w => U (r,w)) (fun w => V (r,w))).symm

/-- Schur integration produces precisely the independent child energies
defined with the sphere measure in the original ambient dimension. -/
theorem independentAngularEnergy_graph_schur {d : ℕ} {ι κ : Type*}
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
    (U V : ι → ℝ × Sphere d → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ D i)
    (weight : κ → ℝ × (Sphere d × Sphere d) → ℝ) (degree : ℝ)
    (hweight : ∀ z k, k ∈ K → 0 ≤ weight k z)
    (hpartition : ∀ z, ∑ k ∈ K, weight k z = 1)
    (hrow : ∀ k ∈ K, ∀ i ∈ S, ((S.filter (G k i)).card : ℝ) ≤ degree)
    (hcol : ∀ k ∈ K, ∀ j ∈ S, ((S.filter (fun i => G k i j)).card : ℝ) ≤ degree) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      ‖∫ z : ℝ × (Sphere d × Sphere d), ∑ k ∈ K, weight k z •
        (∑ i ∈ S, ∑ j ∈ S, if G k i j then
          (U i (z.1,z.2.1) * V i (z.1,z.2.2)) *
            star (U j (z.1,z.2.1) * V j (z.1,z.2.2)) else 0)
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d))‖ ≤
      degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
  classical
  let μ := (PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
    ((sphereMeasure d).prod (sphereMeasure d))
  let F := fun i (z : ℝ × (Sphere d × Sphere d)) =>
    U i (z.1,z.2.1) * V i (z.1,z.2.2)
  have hF (i : ι) (hi : i ∈ S) : Integrable (fun z => ‖F i z‖^2) μ :=
    angular_product_square_integrable v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hb := integral_partition_graph_schur μ S K G F weight degree hF
    hweight hpartition hrow hcol
  have he (i : ι) (hi : i ∈ S) : independentAngularEnergy a v Ψ (U i) (V i) =
      (2 : ℝ)^((d : ℝ)*(v-a)) * ∫ z, ‖F i z‖^2 ∂μ :=
    independentAngularEnergy_product_integral a v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) * (degree * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
      have hs : (∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i)) =
          (2 : ℝ)^((d : ℝ)*(v-a)) * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl he
      rw [hs]
      ring

end Falconer

end OAI
