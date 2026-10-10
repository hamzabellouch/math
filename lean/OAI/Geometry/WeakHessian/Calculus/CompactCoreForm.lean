import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCoreRegularity
import OAI.Geometry.WeakHessian.Calculus.CompactCoreIdentity
import OAI.Geometry.WeakHessian.LocalBounds.FormCoreDense
import OAI.Geometry.WeakHessian.LocalBounds.FormGamma

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile164
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_form_identity {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {B : ℝ} (hB : ∀ x,|χ x| ≤ B)
    (v : (cheeger_closedQuadraticEnergy hrcd.2).domain) :
    (∫ x,gamma m (fun x => f x*χ x) (v : Lp ℝ 2 m) x ∂m) +
      ⟪f,boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB) v -
        boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD v -
        (2:ℝ) • hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec v⟫_ℝ = 0 := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hB)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let L := hχ.2.2.1.choose
  let G := hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec
  have hs := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have hsM : Sobolev m (M f : X → ℝ) := (sobolev_congr_ae (boundedMulLp_ae _ (ae_of_all m hB) f)).mpr hs
  let U : Q.domain := ⟨M f,(hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp (M f))).mp hsM⟩
  let F : Q.domain →ₗ[ℝ] ℝ := {
    toFun := fun w => 2*Q.form U w+⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ
    map_add' := by
      intro w z
      simp only [map_add,Submodule.coe_add,smul_add,inner_sub_right,inner_add_right,real_inner_smul_right]
      ring
    map_smul' := by
      intro c w
      simp only [map_smul,Submodule.coe_smul,smul_comm (2:ℝ) c,inner_sub_right,real_inner_smul_right,RingHom.id_apply,smul_eq_mul]
      ring }
  let C := 2*Real.sqrt (Q.realEnergy U)+‖f‖*(‖M‖+‖T‖+4*(L:ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : ∀ w,|F w| ≤ C*(‖(w : Lp ℝ 2 m)‖+Real.sqrt (Q.realEnergy w)) := by
    intro w
    have hQn := Q.realEnergy_quadratic.nonneg
    have hp : |Q.form U w| ≤ Real.sqrt (Q.realEnergy U)*Real.sqrt (Q.realEnergy w) := by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
      rw [sq_abs,mul_pow,Real.sq_sqrt (hQn U),Real.sq_sqrt (hQn w)]
      exact Q.form_cauchySchwarz U w
    have hG := hrcd.1.formGammaLp_norm_le hfin hrcd.2 o hχ.2.2.1.choose_spec w
    have hn := (norm_sub_le (M w-T w) ((2:ℝ) • G w)).trans
      (add_le_add (norm_sub_le (M w) (T w)) le_rfl)
    norm_num only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hn
    have hR : ‖M w-T w-(2:ℝ) • G w‖ ≤ (‖M‖+‖T‖)*‖(w:Lp ℝ 2 m)‖+4*(L:ℝ)*Real.sqrt (Q.realEnergy w) := by
      nlinarith only [hn,M.le_opNorm (w:Lp ℝ 2 m),T.le_opNorm (w:Lp ℝ 2 m),hG]
    have hi := (abs_real_inner_le_norm f (M w-T w-(2:ℝ) • G w)).trans
      (mul_le_mul_of_nonneg_left hR (norm_nonneg f))
    have htri := abs_add_le (2*Q.form U w) ⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
    change |2*Q.form U w+⟪f,M w-T w-(2:ℝ) • G w⟫_ℝ| ≤ _
    dsimp [C]
    nlinarith only [htri,hi,hp,
      mul_nonneg (Real.sqrt_nonneg (Q.realEnergy U)) (norm_nonneg (w:Lp ℝ 2 m)),
      mul_nonneg (mul_nonneg (norm_nonneg f) (add_nonneg (norm_nonneg M) (norm_nonneg T))) (Real.sqrt_nonneg (Q.realEnergy w)),
      mul_nonneg (mul_nonneg (norm_nonneg f) L.coe_nonneg) (norm_nonneg (w:Lp ℝ 2 m))]
  let S (u A : Lp ℝ 2 m) := ∃ g,IsTestFunction m g ∧ g =ᵐ[m] u ∧ laplacian m g =ᵐ[m] A
  have hS : ∀ u A,S u A → Q.IsFormGenerator u A := by
    intro u A ⟨g,hg,hgu,hgA⟩
    exact hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A
      ((laplacian_isLaplacian hg.1).congr_ae hgu hgA)
  have hd : ∀ u A,Q.IsFormGenerator u A → ∃ us As : ℕ → Lp ℝ 2 m,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
    intro u A hgen
    obtain ⟨gs,hgs,us,As,hgu,hgA,hu,hA⟩ := hrcd.original_test_graph_approx hN hfull hfin o
      (hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 u A hgen)
    exact ⟨us,As,fun n => ⟨gs n,hgs n,hgu n,hgA n⟩,hu,hA⟩
  have hz : ∀ u A,(hs : S u A) → F ⟨u,(hS u A hs).1⟩ = 0 := by
    intro u A hh
    obtain ⟨g,hg,hgu,hgA⟩ := hh
    let w : Q.domain := ⟨u,(hS u A ⟨g,hg,hgu,hgA⟩).1⟩
    have hprod := hrcd.compact_core_product_identity hN hfull hfin o f hof hχ hχc hD hB g hg u A hgu hgA
    let Gg := (memLp_gamma_of_lipschitz hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
      hχ.2.2.1.choose_spec (laplacian_isLaplacian hg.1).1).toLp (gamma m χ g)
    have hGe : Gg = G w := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans ((gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl hgu).trans
        (hrcd.1.formGammaLp_ae hfin hrcd.2 o hχ.2.2.1.choose_spec w).symm)
    change ⟪M f,A⟫_ℝ = ⟪f,M u-T u-(2:ℝ) • Gg⟫_ℝ at hprod
    rw [hGe] at hprod
    have hform := (hS u A ⟨g,hg,hgu,hgA⟩).2 U
    rw [Q.form_comm,real_inner_comm] at hform
    change 2*Q.form U w = -⟪M f,A⟫_ℝ at hform
    change 2*Q.form U w+⟪f,M u-T u-(2:ℝ) • G w⟫_ℝ = 0
    linarith only [hprod,hform]
  have hzero := Q.form_linear_zero_of_graph_core (cheeger_domain_dense hrcd.2) S hS hd F hC hb hz v
  have hgamma : (∫ x,gamma m (fun x => f x*χ x) (v : Lp ℝ 2 m) x ∂m) = 2*Q.form U v := by
    rw [← hrcd.1.global_integral_gamma_form hfin o hrcd.2 U v]
    apply integral_congr_ae
    exact gamma_congr_ae (boundedMulLp_ae _ (ae_of_all m hB) f).symm EventuallyEq.rfl
  rw [hgamma]
  exact hzero
end WeakHessian

end
end InlinedFile164

end OAI
