import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.SobolevSubdifferential
import OAI.Geometry.WeakHessian.LocalBounds.QuadraticPotentials
import OAI.Geometry.WeakHessian.Sobolev.QuadraticGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile34
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma planEnergy_le_of_restricted_contact {π η : Measure (Curve X)}
    [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    {φ ψ : X → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hiφπ : Integrable φ (interpolation π timeZero)) (hiφη : Integrable φ (interpolation η timeZero))
    (hiψπ : Integrable ψ (interpolation π timeOne))
    {S : Set X} (hs : ∀ᵐ γ ∂η, γ timeOne ∈ S)
    (hd : ∀ x y, y ∈ S → φ x+ψ y ≤ dist x y^2/2)
    (hc : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h1 : interpolation π timeOne = interpolation η timeOne) :
    planEnergy π-planEnergy η ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂interpolation η timeZero)) := by
  have hmap (p : Measure (Curve X)) (s : Time) (f : X → ℝ) (hf : Continuous f) :
      (∫ γ,f (γ s) ∂p) = ∫ x,f x ∂interpolation p s :=
    (integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable).symm
  have ip := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφπ
  have iq := (integrable_map_measure hφ.aestronglyMeasurable (continuous_eval_const timeZero).measurable.aemeasurable).mp hiφη
  have jp := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp hiψπ
  have jq := (integrable_map_measure hψ.aestronglyMeasurable (continuous_eval_const timeOne).measurable.aemeasurable).mp (h1 ▸ hiψπ)
  simp only [Function.comp_def] at ip iq jp jq
  have hC : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    rw [integral_congr_ae hc]
    exact integral_div _ _
  have hB : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂η) ≤ planEnergy η/2 := by
    apply le_trans (integral_mono_ae (iq.add jq) (hiη.div_const 2) (hs.mono fun γ hγ => hd _ _ hγ))
    exact le_of_eq (integral_div _ _)
  rw [integral_add ip jp,hmap π timeZero φ hφ,hmap π timeOne ψ hψ,h1] at hC
  rw [integral_add iq jq,hmap η timeZero φ hφ,hmap η timeOne ψ hψ] at hB
  linarith

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X]

lemma entropy_pairing_congr_squareDensity (hfin : FiniteOnBoundedSets m)
    {w φ ψ : X → ℝ} (hw : LocalSobolev m w) (hwm : Measurable w)
    (hφ : LocalSobolev m φ) (hψ : LocalSobolev m ψ)
    (hφm : Measurable φ) (hψm : Measurable ψ)
    (he : φ =ᵐ[squareDensityMeasure m w] ψ) :
    (fun x => 2*w x*gamma m φ w x) =ᵐ[m] fun x => 2*w x*gamma m ψ w x := by
  have he' := (ae_withDensity_iff (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)).mp he
  let S := {x | φ x = ψ x}
  have hS : MeasurableSet S := measurableSet_eq_fun hφm hψm
  have H := gamma_locality_left hfin hφ hψ hw hS (ae_of_all _ fun x hx => hx)
  filter_upwards [he',H] with x hx hg
  by_cases hz : w x = 0
  · simp [hz]
  have hn : ENNReal.ofReal (w x^2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero hz)
  rw [hg (hx hn)]

variable [ProperSpace X] [SigmaFinite m]

lemma RCD.compact_quadratic_entropy_subgradient {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R T : ℝ≥0) (hT : 0 < T)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), ∃ φ ψ : X → ℝ,
      BoundedTracks (π:Measure (Curve X)) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      QuadraticLipschitzBound o T φ ∧ φ o = 0 ∧
      (∃ L : ℝ≥0, LipschitzWith L ψ) ∧
      (∀ x y, y ∈ Metric.closedBall o T → φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂(π:Measure (Curve X)), φ (γ timeZero)+ψ (γ timeOne) =
        dist (γ timeZero) (γ timeOne)^2/2) ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        ∫ x,2*w x*gamma m φ w x ∂m := by
  have haμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (R:ℝ) ≤ (R+T:ℝ≥0))) hx
  have haν : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o (R+T:ℝ≥0) :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp : (T:ℝ) ≤ (R+T:ℝ≥0))) hx
  obtain ⟨π,f,g,hπ,hb,hgeo,ho,hf,hg,hd,hc,hent⟩ := hrcd.compact_sobolev_entropy_subdifferential
    hN hfin w hw hwm hB hwn hwB μ ν hμ o (R+T) (ae_iff.mp haμ) (ae_iff.mp haν) hCt hdν
  let S := Metric.closedBall o (T:ℝ)
  have hS : IsCompact S := isCompact_closedBall _ _
  have hne : S.Nonempty := Metric.nonempty_closedBall.mpr T.coe_nonneg
  let f' := compactCTransform S g
  have hq : QuadraticLipschitzBound o T f' := compactCTransform_difference_bound hS hne hg.continuous.continuousOn o (Subset.refl S)
  have hq' : QuadraticLipschitzBound o T (fun x => f' x-f' o) := by
    intro x y
    simpa only [sub_sub_sub_cancel_right] using hq x y
  have hg' : LipschitzWith (2*(R+T+2)) (fun y => g y+f' o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul x y
  have hsπ : ∀ᵐ γ ∂(π:Measure (Curve X)), γ timeOne ∈ S := by
    apply (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable hS.measurableSet).mp
    change ∀ᵐ x ∂interpolation (π:Measure (Curve X)) timeOne, x ∈ S
    rw [ho.1.interpolation_endpoints.2]
    exact ae_iff.mpr hsν
  have heπ : ∀ᵐ γ ∂(π:Measure (Curve X)), f' (γ timeZero) = f (γ timeZero) := by
    filter_upwards [hsπ,hc] with γ hs hc
    exact compactCTransform_contact hS hne hg.continuous.continuousOn hd hs hc
  have heμ : f' =ᵐ[(μ:Measure X)] f := by
    rw [← ho.1.interpolation_endpoints.1]
    exact (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable
      (isClosed_eq (hq.continuous T.coe_nonneg) hf.continuous).measurableSet).mpr heπ
  have hepair := entropy_pairing_congr_squareDensity hfin hw.2.1 hwm
    (hq.localSobolev hfin hT) (localSobolev_of_lipschitz hfin hf)
    (hq.continuous T.coe_nonneg).measurable hf.continuous.measurable (hμ ▸ heμ)
  have hshift : (fun x => 2*w x*gamma m (fun y => f' y-f' o) w x) =ᵐ[m]
      fun x => 2*w x*gamma m f' w x := by
    exact (gamma_add_const_left hfin (hq.localSobolev hfin hT) hw.2.1 (-f' o)).mono fun x hx => by
      simp only [sub_eq_add_neg,hx]
  refine ⟨π,(fun x => f' x-f' o),(fun y => g y+f' o),hb,ho,hq',sub_self _,⟨_,hg'⟩,?_,?_,?_⟩
  · intro x y hy
    have H := compactCTransform_le hS hne hg.continuous.continuousOn x hy
    dsimp [f']
    linarith
  · filter_upwards [heπ,hc] with γ he hc
    rw [he]
    linarith
  · rw [integral_congr_ae hshift,integral_congr_ae hepair]
    exact hent
end WeakHessian

end
end InlinedFile34

end OAI
