import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.ResolventSmoothing
import OAI.Geometry.WeakHessian.Calculus.CompactLipDense

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile156
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.resolvent_compactLip_test {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (u : Lp ℝ 2 m) (hu : u ∈ compactLipLp m) :
    ∃ g : X → ℝ,IsTestFunction m g ∧
      g =ᵐ[m] ((cheeger_closedQuadraticEnergy hrcd.2).scale zero_lt_one).resolvent u := by
  obtain ⟨f,⟨L,hf⟩,hfc,hfe⟩ := hu
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg (f o)).trans (hB (f o) ⟨o,rfl⟩)
  have hub : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hfe] with x hx
    rw [← hx]
    simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  let r := (Q.scale zero_lt_one).resolvent u
  obtain ⟨g,hg,hge⟩ := hrcd.cheeger_scaled_resolvent_lipschitz hN hfull hfin hrcd.2 o u hB0 hub zero_lt_one
  have hgen : Q.IsFormGenerator r (r-u) := by
    simpa only [inv_one,one_smul] using (Q.scaled_resolvent_iff zero_lt_one u r).mp rfl
  have hlap := hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 r (r-u) hgen
  have hgs : IsLaplacian m g (r-u : Lp ℝ 2 m) := hlap.congr_ae hge.symm EventuallyEq.rfl
  have hsu : Sobolev m u := (sobolev_congr_ae hfe).mp (sobolev_of_lipschitz_compactSupport hfin hf hfc)
  have hAs : Sobolev m (r-u : Lp ℝ 2 m) :=
    (sobolev_congr_ae (Lp.coeFn_sub r u).symm).mp (hlap.1.sub hfin hsu)
  have hgb : BoundedFunction g := by
    refine ⟨B,continuous_le_of_ae_le hfull hg.continuous.abs continuous_const ?_⟩
    filter_upwards [hge,cheeger_scaled_resolvent_bounded hrcd.2 zero_lt_one hB0 u hub] with x hx hb
    rwa [hx]
  exact ⟨g,⟨⟨(r-u : Lp ℝ 2 m),hgs⟩,hgb,⟨_,hg⟩,(sobolev_congr_ae (hgs.ae_laplacian hfin)).mpr hAs⟩,hge⟩

lemma RCD.original_test_graph_approx {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {u A : Lp ℝ 2 m} (hu : IsLaplacian m u A) :
    ∃ gs : ℕ → X → ℝ,(∀ n,IsTestFunction m (gs n)) ∧
      ∃ us As : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧
      (∀ n,laplacian m (gs n) =ᵐ[m] As n) ∧
      Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy hrcd.2
  obtain ⟨fs,hfs,hft⟩ := exists_compactLip_L2_approx hfin (u-A)
  let us (n : ℕ) := (Q.scale zero_lt_one).resolvent (fs n)
  let As (n : ℕ) := us n-fs n
  choose gs hgs hge using fun n => hrcd.resolvent_compactLip_test hN hfull hfin o (fs n) (hfs n)
  have hgen := hrcd.1.global_formGenerator_of_isLaplacian hfin o hrcd.2 u A hu
  have heu : (Q.scale zero_lt_one).resolvent (u-A) = u := by
    apply (Q.scaled_resolvent_iff zero_lt_one (u-A) u).mpr
    simpa only [inv_one,one_smul,sub_sub_cancel] using hgen
  have hT : Tendsto us atTop (𝓝 u) := by
    have H := (Q.scale zero_lt_one).resolventLinear.continuous.tendsto (u-A) |>.comp hft
    change Tendsto (fun n => (Q.scale zero_lt_one).resolvent (fs n)) atTop (𝓝 ((Q.scale zero_lt_one).resolvent (u-A))) at H
    rw [heu] at H
    exact H
  refine ⟨gs,hgs,us,As,hge,?_,hT,?_⟩
  · intro n
    have hG : Q.IsFormGenerator (us n) (As n) := by
      simpa only [inv_one,one_smul] using (Q.scaled_resolvent_iff zero_lt_one (fs n) (us n)).mp rfl
    have hL := hrcd.1.global_isLaplacian_of_formGenerator hfin o hrcd.2 (us n) (As n) hG
    exact (hL.congr_ae (hge n).symm EventuallyEq.rfl).ae_laplacian hfin
  · simpa only [sub_sub_cancel] using hT.sub hft
end WeakHessian

end
end InlinedFile156

end OAI
