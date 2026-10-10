import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.CoreAlgebra
import OAI.Geometry.WeakHessian.HeatFlow.HeatAverage
import OAI.Geometry.WeakHessian.LocalBounds.AverageWeighted

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile119
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma bounded_of_vanishes_infinity (o : X) {g : X → ℝ} (hg : Continuous g)
    (hv : ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε) :
    BoundedFunction g := by
  obtain ⟨R,_hR,hgR⟩ := hv 1 zero_lt_one
  obtain ⟨B,hB⟩ := ((isCompact_closedBall o R).image hg).isBounded.exists_norm_le
  refine ⟨max B 1,fun x => ?_⟩
  by_cases hx : dist x o ≤ R
  · exact (show |g x| ≤ B from by simpa only [Real.norm_eq_abs] using hB (g x) ⟨x,hx,rfl⟩).trans (le_max_left _ _)
  · exact ((hgR x (lt_of_not_ge hx)).le).trans (le_max_right _ _)

lemma RCD.cheegerHeat_average_test {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m)
    {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,IsTestFunction m g ∧
      LipschitzWith (L*⟨Real.exp (|K| *t),(Real.exp_pos _).le⟩) g ∧
      g =ᵐ[m] (t⁻¹ • ∫ s in 0..t,cheegerHeat h s (hf2.toLp f) : Lp ℝ 2 m) ∧
      (∃ B : ℝ,∀ᵐ x ∂m,|laplacian m g x| ≤ B) ∧
      ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |g x| < ε := by
  obtain ⟨g,hg,hge,hgz⟩ := hrcd.cheegerHeat_average_compactDatum_CZero hN hfull hfin h o hf hfc hf2 ht
  let u := hf2.toLp f
  let v := t⁻¹ • ∫ s in 0..t,cheegerHeat h s u
  let A := t⁻¹ • (cheegerHeat h t u-u)
  have hgen := hrcd.1.global_isLaplacian_of_formGenerator hfin o h v A
    (cheegerHeat_average_formGenerator hfin h u ht.le)
  have hggen : IsLaplacian m g A := hgen.congr_ae hge.symm Filter.EventuallyEq.rfl
  have hsf := sobolev_of_lipschitz_compactSupport hfin hf hfc
  have hsu : Sobolev m u := (sobolev_congr_ae hf2.coeFn_toLp).mpr hsf
  have hPt : Sobolev m (cheegerHeat h t u) :=
    (hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp _)).mpr
      ((cheegerHeat_energy_le h ht.le u).trans_lt
        ((hrcd.1.global_sobolev_iff_cheeger_lt_top hfin o (Lp.memLp u)).mp hsu))
  have hAs : Sobolev m A := by
    have H := (hPt.sub hfin hsu).const_mul t⁻¹
    apply (sobolev_congr_ae ?_).mp H
    filter_upwards [Lp.coeFn_smul t⁻¹ (cheegerHeat h t u-u),Lp.coeFn_sub (cheegerHeat h t u) u] with x hx hy
    dsimp only [A]
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,hy] using hx.symm
  have hlap := hggen.ae_laplacian hfin
  have gtest : IsTestFunction m g := ⟨⟨A,hggen⟩,bounded_of_vanishes_infinity o hg.continuous hgz,
    ⟨_,hg⟩,(sobolev_congr_ae hlap).mpr hAs⟩
  refine ⟨g,gtest,hg,hge,?_,hgz⟩
  obtain ⟨B,hB⟩ := hfc.isCompact_range hf.continuous |>.isBounded.exists_norm_le
  have huB : ∀ᵐ x ∂m,|u x| ≤ B := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [show u x = f x from hx]
    simpa only [Real.norm_eq_abs] using hB (f x) ⟨x,rfl⟩
  have hptB := cheegerHeat_bounded h ht.le (le_trans (norm_nonneg (f o)) (hB (f o) ⟨o,rfl⟩)) u huB
  refine ⟨t⁻¹*(B+B),?_⟩
  filter_upwards [hlap,Lp.coeFn_smul t⁻¹ (cheegerHeat h t u-u),Lp.coeFn_sub (cheegerHeat h t u) u,huB,hptB] with x hl hx hy hu hp
  rw [hl]
  change |(t⁻¹ • (cheegerHeat h t u-u) : Lp ℝ 2 m) x| ≤ _
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,hy,Pi.sub_apply,abs_mul,abs_inv,abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hp hu)) (by positivity)
end WeakHessian

end
end InlinedFile119

end OAI
