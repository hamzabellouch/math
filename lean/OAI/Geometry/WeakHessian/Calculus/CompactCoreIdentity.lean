import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCoreLocalization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile161
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_product_identity {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B)
    (g : X → ℝ) (hg : IsTestFunction m g) (u A : Lp ℝ 2 m)
    (hgu : g =ᵐ[m] u) (hgA : laplacian m g =ᵐ[m] A) :
    ⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ =
      ⟪f,boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) u -
        boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD u -
        (2:ℝ) • (memLp_gamma_of_lipschitz hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
          hχ.2.2.1.choose_spec (laplacian_isLaplacian hg.1).1).toLp (gamma m χ g)⟫_ℝ := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let L := hχ.2.2.1.choose
  have hL : LipschitzWith L χ := hχ.2.2.1.choose_spec
  have hgS := (laplacian_isLaplacian hg.1).1
  let G := (memLp_gamma_of_lipschitz hfin hpar hL hgS).toLp (gamma m χ g)
  have hG := (memLp_gamma_of_lipschitz hfin hpar hL hgS).coeFn_toLp
  have hP := hrcd.test_mul hN hfull hfin o hχ hg
  have hPc : HasCompactSupport (fun x => χ x*g x) := hχc.mul_right
  have hpe : (fun x => χ x*g x) =ᵐ[m] M u := by
    filter_upwards [hgu,boundedMulLp_ae _ (ae_of_all m hB) u] with x hu hp
    rw [hp,hu,mul_comm]
  have hgen := (laplacian_isLaplacian hχ.1).mul_lipschitz hfin hpar
    (laplacian_isLaplacian hg.1) hL hg.2.2.1.choose_spec hB hg.2.1.choose_spec
  have hAe : laplacian m (fun x => χ x*g x) =ᵐ[m] (T u+M A+(2:ℝ) • G : Lp ℝ 2 m) := by
    apply (hgen.ae_laplacian hfin).trans
    filter_upwards [hgu,hgA,boundedMulLp_ae _ hD u,boundedMulLp_ae _ (ae_of_all m hB) A,
      Lp.coeFn_add (T u) (M A),Lp.coeFn_add (T u+M A) ((2:ℝ) • G),Lp.coeFn_smul (2:ℝ) G,hG]
      with x hu hA ht hm h1 h2 h3 hgam
    change (T u) x = u x*laplacian m χ x at ht
    change (M A) x = A x*χ x at hm
    change G x = gamma m χ g x at hgam
    simp only [h2,Pi.add_apply,h1,h3,Pi.smul_apply,smul_eq_mul,hgam,ht,hm]
    rw [hu,hA]
    ring
  have hh := hof _ hP hPc (M u) (T u+M A+(2:ℝ) • G) hpe hAe
  change ⟪M f,A⟫_ℝ = ⟪f,M u-T u-(2:ℝ) • G⟫_ℝ
  rw [boundedMulLp_inner_swap]
  simp only [inner_sub_right,inner_add_right,real_inner_smul_right] at hh ⊢
  linarith only [hh]
end WeakHessian

end
end InlinedFile161

end OAI
