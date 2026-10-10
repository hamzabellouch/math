import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TestProduct
import OAI.Geometry.WeakHessian.HeatFlow.DriftResolvent

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile159
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma boundedMulLp_inner_swap {χ : X → ℝ} (hχ : AEStronglyMeasurable χ m)
    {B : ℝ} (hB : ∀ᵐ x ∂m,|χ x| ≤ B) (f g : Lp ℝ 2 m) :
    ⟪boundedMulLp hχ hB f,g⟫_ℝ = ⟪f,boundedMulLp hχ hB g⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_ae hχ hB f,boundedMulLp_ae hχ hB g] with x hf hg
  simp only [hf,hg,Real.inner_apply]
  ring

lemma RCD.compact_core_localized_pairing {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ g,IsTestFunction m g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A →
      |⟪boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) f,A⟫_ℝ|
        ≤ C*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal)) := by
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let L := hχ.2.2.1.choose
  have hL : LipschitzWith L χ := hχ.2.2.1.choose_spec
  refine ⟨‖f‖*(‖M‖+‖T‖+2*(L:ℝ)),by positivity,?_⟩
  intro g hg u A hgu hgA
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
  have he : ⟪M f,A⟫_ℝ = ⟪f,M u-T u-(2:ℝ) • G⟫_ℝ := by
    rw [boundedMulLp_inner_swap]
    simp only [inner_sub_right,inner_add_right,real_inner_smul_right] at hh ⊢
    linarith only [hh]
  have hgSn : Sobolev m (u : X → ℝ) := (sobolev_congr_ae hgu).mp hgS
  have hDge : ‖hgS.2.2.toLp (weakGradient m g)‖ =
      Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    rw [cheegerEnergy_congr_ae hgu.symm,hrcd.1.global_cheegerEnergy_toReal hfin o hrcd.2 hgS]
    have hid := norm_toLp_sq_eq_integral hgS.2.2
    rw [show 2*((∫ x,(weakGradient m g x)^2 ∂m)/2) = ∫ x,(weakGradient m g x)^2 ∂m by ring,← hid,
      Real.sqrt_sq (norm_nonneg _)]
  have hGn : ‖G‖ ≤ (L:ℝ)*Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    rw [← hDge]
    exact norm_gamma_toLp_le hfin hpar hL hgS
  rw [he]
  apply (abs_real_inner_le_norm _ _).trans
  have hn := (norm_sub_le (M u-T u) ((2:ℝ) • G)).trans
    (add_le_add (norm_sub_le (M u) (T u)) le_rfl)
  norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hn
  have hmu := M.le_opNorm u
  have htu := T.le_opNorm u
  have hn' : ‖M u-T u-(2:ℝ) • G‖ ≤
      (‖M‖+‖T‖)*‖u‖+2*(L:ℝ)*Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal) := by
    nlinarith only [hn,hmu,htu,hGn]
  apply (mul_le_mul_of_nonneg_left hn' (norm_nonneg f)).trans
  have hs := Real.sqrt_nonneg (2*(cheegerEnergy m (u : X → ℝ)).toReal)
  have ha := mul_nonneg (norm_nonneg M) hs
  have hb := mul_nonneg (norm_nonneg T) hs
  have hc := mul_nonneg (NNReal.coe_nonneg L) (norm_nonneg u)
  calc
    _ ≤ ‖f‖*((‖M‖+‖T‖+2*(L:ℝ))*(‖u‖+Real.sqrt (2*(cheegerEnergy m (u : X → ℝ)).toReal))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg f)
      nlinarith only [ha,hb,hc]
    _ = _ := by ring
end WeakHessian

end
end InlinedFile159

end OAI
