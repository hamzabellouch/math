import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWeightedAdjoint

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (u : V → W) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (differential e a b u) x := by
  exact (ContDiffAt.sum (fun i _ => (ha i).clm_apply
    ((hu.fderiv_right (by simp)).clm_apply contDiffAt_const))).add (hb.clm_apply hu)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma weightedAdjoint_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (v : V → Q) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hv : ContDiffAt ℝ ∞ v x) (hρ0 : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (weightedAdjoint e a b ρ v) x := by
  let Adj : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact ((hρ.inv hρ0).neg.smul (ContDiffAt.sum (fun i _ =>
    ((((Adj.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_apply hv).fderiv_right
      (by simp)).clm_apply contDiffAt_const)))).add
        ((Adj.contDiff.contDiffAt.comp x hb).clm_apply hv)

variable (μ : Measure V) [IsAddHaarMeasure μ]
lemma integral_square_residual {U : Set V} (hU : IsOpen U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (k d r η : V → W)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
    (hd : ∀ x ∈ tsupport η, ContinuousAt d x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hsub : tsupport η ⊆ U)
    (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hres : ∀ x ∈ tsupport η, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
    (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) + (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
      ∫ x, ρ x * ⟪η x,r x⟫ ∂μ := by
  have hat (i : ι) (x : V) (hx : x ∈ U) := (ha i x hx).contDiffAt (hU.mem_nhds hx)
  have hbt (x : V) (hx : x ∈ U) := (hb x hx).contDiffAt (hU.mem_nhds hx)
  have hρt (x : V) (hx : x ∈ U) := (hρ x hx).contDiffAt (hU.mem_nhds hx)
  have hkt (x : V) (hx : x ∈ U) := (hk x hx).contDiffAt (hU.mem_nhds hx)
  have hDt (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (differential e a b k) x :=
    differential_contDiffAt e a b k (fun i => hat i x hx) (hbt x hx) (hkt x hx)
  have hD : ContDiffOn ℝ ∞ (differential e a b k) U := fun x hx => (hDt x hx).contDiffWithinAt
  have hAt (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (weightedAdjoint e a b ρ (differential e a b k)) x :=
    weightedAdjoint_contDiffAt e a b ρ _ (fun i => hat i x hx) (hbt x hx) (hρt x hx)
      (hDt x hx) (hρ0 x hx)
  have hi : Integrable (fun x => ρ x * ⟪η x,d x⟫) μ := by
    have hh := integrable_inner_compact_local μ hη.continuous
      (fun x hx => (hρt x (hsub hx)).continuousAt.smul (hd x hx)) hc
    change Integrable (fun x => ⟪η x,ρ x • d x⟫) μ at hh
    simpa only [inner_smul_right] using hh
  have hj : Integrable (fun x => ρ x * ⟪η x,weightedAdjoint e a b ρ (differential e a b k) x⟫) μ := by
    have hh := integrable_inner_compact_local μ hη.continuous
      (fun x hx => (hρt x (hsub hx)).continuousAt.smul (hAt x (hsub hx)).continuousAt) hc
    change Integrable (fun x => ⟪η x,ρ x • weightedAdjoint e a b ρ (differential e a b k) x⟫) μ at hh
    simpa only [inner_smul_right] using hh
  rw [← integral_weightedAdjoint_on μ hU e a b ρ η (differential e a b k) ha hb hρ hη hD hc hsub
    (fun x hx => hρ0 x (hsub (subset_tsupport _ hx))),← integral_add hi hj]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport η
  · rw [← mul_add,← inner_add_right,hres x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
