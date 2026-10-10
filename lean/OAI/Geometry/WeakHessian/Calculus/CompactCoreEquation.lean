import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCoreForm
import OAI.Geometry.WeakHessian.Sobolev.LaplacianLocality

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile167
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.compact_core_weak_equation {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (f : Lp ℝ 2 m)
    (hof : ∀ g,IsTestFunction m g → HasCompactSupport g → ∀ u A : Lp ℝ 2 m,
      g =ᵐ[m] u → laplacian m g =ᵐ[m] A → ⟪f,u-A⟫_ℝ = 0)
    {χ η : X → ℝ} (hχ : IsTestFunction m χ) (hχc : HasCompactSupport χ)
    {D : ℝ} (hD : ∀ᵐ x ∂m,|laplacian m χ x| ≤ D)
    {L : ℝ≥0} (hη : LipschitzWith L η) (hη1 : ∀ x,|η x| ≤ 1)
    (hc : ∀ x,η x ≠ 0 → χ x = 1) :
    (∫ x,gamma m (fun y => f y*χ y) (fun y => (f y*χ y)*(η y*η y)) x ∂m) +
      (∫ x,((f x*χ x)*η x)^2 ∂m) = 0 := by
  let w := fun x => f x*χ x
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hw : Sobolev m w := hrcd.compact_core_localized_sobolev hN hfull hfin o f hof hχ hχc hD
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hDs : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  have hv : Sobolev m (fun x => w x*(η x*η x)) :=
    hw.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hB hDs
  let v := hv.1.toLp (fun x => w x*(η x*η x))
  have hve : (v : X → ℝ) =ᵐ[m] (fun x => w x*(η x*η x)) := hv.1.coeFn_toLp
  let V : (cheeger_closedQuadraticEnergy hrcd.2).domain := ⟨v,
    (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp v)).mp ((sobolev_congr_ae hve).mpr hv)⟩
  obtain ⟨Bχ,hBχ⟩ := hχ.2.1
  let M := boundedMulLp hχ.2.2.1.choose_spec.continuous.aestronglyMeasurable (ae_of_all m hBχ)
  let T := boundedMulLp (laplacian_isLaplacian hχ.1).2.1.aestronglyMeasurable hD
  let G := hrcd.1.formGammaLp hfin hrcd.2 o hχ.2.2.1.choose_spec
  have hT : T v = 0 := by
    apply Lp.ext
    filter_upwards [boundedMulLp_ae _ hD v,hve,
      hχ.laplacian_mul_eq_zero_on_plateau hfin hpar hη hη1 hc,Lp.coeFn_zero ℝ 2 m] with x ht hvx hl hz
    change (T v) x = v x*laplacian m χ x at ht
    rw [ht,hvx,hz]
    change w x*(η x*η x)*laplacian m χ x = 0
    calc
      _ = w x*η x*(laplacian m χ x*η x) := by ring
      _ = 0 := by rw [hl]; simp only [Pi.zero_apply,mul_zero]
  have hg0 : gamma m χ (fun x => w x*(η x*η x)) =ᵐ[m] 0 :=
    gamma_zero_of_const_on_support hfin hpar (laplacian_isLaplacian hχ.1).1.2.1 hv.2.1
      hη.continuous.measurable hc (fun x hx => by rw [hx]; ring)
  have hG : G V = 0 := by
    apply Lp.ext
    exact (hrcd.1.formGammaLp_ae hfin hrcd.2 o hχ.2.2.1.choose_spec V).trans
      ((gamma_congr_ae (m := m) (f := χ) EventuallyEq.rfl hve).trans (hg0.trans (Lp.coeFn_zero ℝ 2 m).symm))
  have H := hrcd.compact_core_form_identity hN hfull hfin o f hof hχ hχc hD hBχ V
  change (∫ x,gamma m w (v : X → ℝ) x ∂m)+⟪f,M v-T v-(2:ℝ) • G V⟫_ℝ = 0 at H
  rw [hT,hG,smul_zero,sub_zero,sub_zero] at H
  have hg : (∫ x,gamma m w (v : X → ℝ) x ∂m) =
      ∫ x,gamma m w (fun y => w y*(η y*η y)) x ∂m :=
    integral_congr_ae (gamma_congr_ae (m := m) (f := w) EventuallyEq.rfl hve)
  have hi : ⟪f,M v⟫_ℝ = ∫ x,(w x*η x)^2 ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae _ (ae_of_all m hBχ) v,hve] with x hm hvx
    change (M v) x = v x*χ x at hm
    simp only [RCLike.inner_apply,conj_trivial,hm,hvx]
    dsimp [w]
    by_cases he : η x=0
    · rw [he]; ring
    · rw [hc x he]; ring
  rw [hg,hi] at H
  exact H
end WeakHessian

end
end InlinedFile167

end OAI
