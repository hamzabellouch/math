import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiffLipschitz
import OAI.Geometry.WeakHessian.Entropy.EntropyContact
import OAI.Geometry.WeakHessian.Entropy.ZeroDensity
import OAI.Geometry.WeakHessian.Calculus.GammaLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile23
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [ProperSpace X]
variable {m : Measure X}

omit [ProperSpace X] in
lemma Sobolev.squareLogFloor_local (hfin : FiniteOnBoundedSets m)
    {w : X → ℝ} (hw : Sobolev m w) {a : ℝ} (ha : 0 < a) :
    LocalSobolev m (squareLogFloor a w) :=
  ((hw.comp_contDiff_lipschitz hfin (regularizedLog_contDiff ha)
    (regularizedLog_lipschitz ha) (regularizedLog_zero a)).2.1.add_const hfin (Real.log a)).const_mul 2

omit [ProperSpace X] in
lemma gamma_squareLogFloor_sobolev (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {φ w : X → ℝ} (hφ : LocalSobolev m φ) (hw : Sobolev m w)
    (hn : ∀ᵐ x ∂m, 0 ≤ w x) {a : ℝ} (ha : 0 < a) :
    gamma m φ (squareLogFloor a w) =ᵐ[m] fun x => 2/(w x+a)*gamma m φ w x := by
  have hrS := (hw.comp_contDiff_lipschitz hfin (regularizedLog_contDiff ha)
    (regularizedLog_lipschitz ha) (regularizedLog_zero a)).2.1
  have hchain := gamma_comp_contDiff hfin hpar hw.2.1 hφ (regularizedLog_contDiff ha)
    hrS.1 (ae_of_all _ fun x => regularizedLog_deriv_bound ha (w x))
  filter_upwards [gamma_comm (m := m) φ (squareLogFloor a w),
    gamma_const_mul_left hfin hpar (hrS.add_const hfin (Real.log a)) hφ 2,
    gamma_add_const_left hfin hrS hφ (Real.log a),hchain,gamma_comm (m := m) w φ,hn] with x hc hm ha' hh hs hn
  change gamma m (squareLogFloor a w) φ x = 2*gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x at hm
  change gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x = gamma m (regularizedLog a ∘ w) φ x at ha'
  rw [hc,hm,ha',hh,hs,regularizedLog_deriv ha,max_eq_right (by linarith)]
  simp only [div_eq_mul_inv]
  ring

lemma squareLogFloor_pairing_tendsto (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {φ w : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hw : Sobolev m w)
    (hwm : Measurable w) (hn : ∀ᵐ x ∂m, 0 ≤ w x) :
    Tendsto (fun n : ℕ => ∫ x,w x^2*gamma m φ (squareLogFloor (1/((n:ℝ)+1)) w) x ∂m)
      atTop (𝓝 (∫ x,2*w x*gamma m φ w x ∂m)) := by
  let a (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hΓ : MemLp (gamma m φ w) 2 m := (memLp_congr_ae (gamma_comm (m := m) w φ)).mp (memLp_gamma_lipschitz hfin hpar hw hφ)
  have hi : Integrable (fun x => 2*|w x*gamma m φ w x|) m := (hw.1.integrable_mul hΓ).abs.const_mul 2
  have he (n : ℕ) : (∫ x,w x^2*gamma m φ (squareLogFloor (a n) w) x ∂m) =
      ∫ x,w x^2*(2/(w x+a n))*gamma m φ w x ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_squareLogFloor_sobolev hfin hpar hφS hw hn (ha n)] with x hx
    rw [hx]; ring
  simp_rw [show ∀ n : ℕ, 1/((n:ℝ)+1) = a n from fun _ => rfl,he]
  apply tendsto_integral_of_dominated_convergence (fun x => 2*|w x*gamma m φ w x|)
  · intro n
    have hcoef : Measurable (fun x => w x^2*(2/(w x+a n))) := by fun_prop
    exact hcoef.aestronglyMeasurable.mul hΓ.aestronglyMeasurable
  · exact hi
  · intro n
    filter_upwards [hn] with x hx
    have hp : 0 < w x+a n := add_pos_of_nonneg_of_pos hx (ha n)
    have hb : w x^2*(2/(w x+a n)) ≤ 2*w x := by
      rw [← mul_div_assoc,div_le_iff₀ hp]
      nlinarith [mul_nonneg hx (ha n).le]
    simp only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg hx,
      abs_of_pos (div_pos (by norm_num : (0:ℝ)<2) hp)]
    nlinarith [mul_le_mul_of_nonneg_right hb (abs_nonneg (gamma m φ w x))]
  · filter_upwards [hn] with x hx
    by_cases hz : w x = 0
    · simp [hz]
    · have H := ((tendsto_const_nhds (x := (2:ℝ))).div
        ((tendsto_const_nhds (x := w x)).add hat) (by simpa using hz)).const_mul (w x^2) |>.mul_const (gamma m φ w x)
      have heq : w x^2*(2/w x)*gamma m φ w x = 2*w x*gamma m φ w x := by field_simp [hz]
      simpa only [add_zero,Pi.div_apply,heq] using H

omit [ProperSpace X] in
lemma IsTestPlan.contact_gamma_integral_eq (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ θ χ f : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hθ : LipschitzWith T θ)
    (hf : LocalSobolev m f)
    (hφd : ∀ x y,φ x+ψ y ≤ dist x y^2/2) (hθd : ∀ x y,θ x+χ y ≤ dist x y^2/2)
    (hφc : ∀ᵐ γ ∂π,φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (hθc : ∀ᵐ γ ∂π,θ (γ timeZero)+χ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ γ,gamma m φ f (γ timeZero) ∂π) = ∫ γ,gamma m θ f (γ timeZero) ∂π :=
  tendsto_nhds_unique (hπ.contact_first_variation_local hfin hpar hb hgeo hφ hf hφd hφc)
    (hπ.contact_first_variation_local hfin hpar hb hgeo hθ hf hθd hθc)

lemma IsTestPlan.contact_entropy_pairing_eq (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {φ ψ θ χ w : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hθ : LipschitzWith T θ)
    (hw : Sobolev m w) (hwm : Measurable w) (hn : ∀ᵐ x ∂m, 0 ≤ w x)
    (h0 : interpolation π timeZero = squareDensityMeasure m w)
    (hφd : ∀ x y,φ x+ψ y ≤ dist x y^2/2) (hθd : ∀ x y,θ x+χ y ≤ dist x y^2/2)
    (hφc : ∀ᵐ γ ∂π,φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (hθc : ∀ᵐ γ ∂π,θ (γ timeZero)+χ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2) :
    (∫ x,2*w x*gamma m φ w x ∂m) = ∫ x,2*w x*gamma m θ w x ∂m := by
  have hac : interpolation π timeZero ≪ m := (hπ.2.1.choose_spec timeZero).absolutelyContinuous.trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have he (a : ℝ) (ha : 0 < a) : (∫ x,w x^2*gamma m φ (squareLogFloor a w) x ∂m) =
      ∫ x,w x^2*gamma m θ (squareLogFloor a w) x ∂m := by
    have hf := hw.squareLogFloor_local hfin ha
    have H := hπ.contact_gamma_integral_eq hfin hpar hb hgeo hφ hθ hf hφd hθd hφc hθc
    have hm (u : X → ℝ) (hu : LocalSobolev m u) :
        (∫ γ,gamma m u (squareLogFloor a w) (γ timeZero) ∂π) =
          ∫ x,w x^2*gamma m u (squareLogFloor a w) x ∂m := by
      rw [← integral_map (continuous_eval_const timeZero).measurable.aemeasurable
        ((gamma_aestronglyMeasurable hfin hu hf).mono_ac hac)]
      change (∫ x,gamma m u (squareLogFloor a w) x ∂interpolation π timeZero) = _
      rw [h0,squareDensity_integral hwm]
    rwa [hm φ (localSobolev_of_lipschitz hfin hφ),hm θ (localSobolev_of_lipschitz hfin hθ)] at H
  apply tendsto_nhds_unique (squareLogFloor_pairing_tendsto hfin hpar hφ hw hwm hn)
  have H := squareLogFloor_pairing_tendsto hfin hpar hθ hw hwm hn
  exact H.congr (fun n => (he (1/((n:ℝ)+1)) (by positivity)).symm)
end WeakHessian

end
end InlinedFile23

end OAI
