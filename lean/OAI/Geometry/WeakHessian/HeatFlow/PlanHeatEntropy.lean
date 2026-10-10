import Mathlib
import OAI.Geometry.WeakHessian.Transport.EntropyAction
import OAI.Geometry.WeakHessian.Transport.PlanAction
import OAI.Geometry.WeakHessian.Transport.IntegratedAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

noncomputable def compactHopfDualBound (hfin : FiniteOnBoundedSets m) (o : X)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) : ℝ :=
  (compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)).choose_spec.choose

omit [SigmaFinite m] in
lemma compact_dual_of_entropy_actions
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E : ℝ → ℝ → ℝ} {P a : ℝ → ℝ} {τ : ℝ}
    (hu : ContinuousOn u (Icc 0 1))
    (hE : ∀ ε, 0 < ε → ContinuousOn (E ε) (Icc 0 1))
    (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (hA : ∀ ε, 0 < ε → ∀ s ∈ Ico (0:ℝ) 1, ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt (E ε) e s ∧
      FormActionBound m (fun x => u s x+ε) v (a s-2*τ*e))
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q) :
    ∀ ε, 0 < ε →
      (∫ x, u 1 x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, u 0 x*boundedHopfMap f q x ∂m)+τ*(E ε 1-E ε 0) ≤ P 1-P 0+ε*compactHopfDualBound hfin o f hf hq/2 := by
  let data := compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)
  let W := data.choose
  obtain ⟨hWe,hWc,hWS,hΓ,hD,hHJ⟩ := data.choose_spec.choose_spec
  intro ε hε
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc 0 1) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_action (W := fun s => W (q+s)) hq hε.le
    (hWc.comp (by fun_prop) hmap) hu (hE ε hε) hP hP'
    (fun s hs => hWS _ (by linarith [hs.1]))
    (fun s hs => hΓ _ (by linarith [hs.1]))
    (fun s hs => hD _ (hmap ⟨hs.1,hs.2.le⟩)) hun
    (fun s z hs hsz => by
      have H := hHJ (q+s) (q+z) (by linarith) (by linarith)
      simpa only [add_sub_add_left_eq_sub] using H) (hA ε hε)
  have hpair (s : ℝ) (hs : 0 ≤ s) : ⟪W (q+s),u s⟫_ℝ =
      ∫ x, u s x*boundedHopfMap f (q+s) x ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWe (q+s) (by linarith)] with x hx
    simp only [W,hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair 1 zero_le_one,hpair 0 le_rfl] at H
  simpa only [add_zero,compactHopfDualBound,data] using H

def backwardsHeatTime (δ T s : ℝ) : ℝ := δ+T*max (1-s) 0

lemma backwardsHeatTime_pos {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (s : ℝ) :
    0 < backwardsHeatTime δ T s := by
  dsimp [backwardsHeatTime]
  exact add_pos_of_pos_of_nonneg hδ (mul_nonneg hT (le_max_right _ _))

lemma backwardsHeatTime_hasDerivAt (δ T : ℝ) {s : ℝ} (hs : s < 1) :
    HasDerivAt (backwardsHeatTime δ T) (-T) s := by
  have he : backwardsHeatTime δ T =ᶠ[𝓝 s] fun z => δ+T*(1-z) := by
    filter_upwards [eventually_lt_nhds hs] with z hz
    simp only [backwardsHeatTime,max_eq_left (by linarith : 0 ≤ 1-z)]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert (((hasDerivAt_id s).const_sub 1).const_mul T).const_add δ using 1 <;> simp

lemma cheegerHeat_plan_entropy_dual
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m) {k : ℝ}
    (hgrad : ∀ (f u : Lp ℝ 2 m), Sobolev m (f : X → ℝ) →
      (∀ᵐ x ∂m, 0 ≤ u x) → ∀ B : ℝ, 0 ≤ B → (∀ᵐ x ∂m, |u x| ≤ B) →
      ∀ t : ℝ, 0 ≤ t → Real.exp (2*k*t)*(∫ x, u x*(weakGradient m (cheegerHeat h t f) x)^2 ∂m) ≤
        ∫ x, cheegerHeat h t u x*(weakGradient m f x)^2 ∂m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {B : ℝ≥0} (hB : ∀ t : Time, π.map (fun γ => γ t) ≤ (B : ℝ≥0∞) • m)
    {u : Time → Lp ℝ 2 m} (hu : StronglyMeasurable u)
    (hun : ∀ t, ∀ᵐ x ∂m, 0 ≤ u t x)
    (hlaw : ∀ t, densityMeasure m (u t) = π.map (fun γ => γ t))
    (hnorm : ∀ t, ‖u t‖^2 ≤ (B : ℝ))
    {κ : ℝ → ℝ} (hκ : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (hn : ∀ r, 0 ≤ κ r) (hm : ∫ r, κ r = 1)
    {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) :
    ∀ ε, 0 < ε →
      (∫ x, cheegerHeat h δ (smoothDensity κ u 1) x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, cheegerHeat h (δ+T) (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) (smoothDensity κ u 0) x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ (smoothDensity κ u 1) x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, planKineticCost π/Real.exp (2*k*(δ+T*(1-s)))/2)+
        ε*compactHopfDualBound hfin o f hf hq/2 := by
  let θ := backwardsHeatTime δ T
  let U := fun s => cheegerHeat h (θ s) (smoothDensity κ u s)
  let E := fun ε s => ∫ x, regularizedEntropy ε (U s x) ∂m
  let A := fun s => planKineticCost π/Real.exp (2*k*(δ+T*(1-s)))
  let P := fun s => ∫ r in (0:ℝ)..s, A r/2
  have hAcont : Continuous (fun s => A s/2) := by
    dsimp [A]
    exact (continuous_const.div (by fun_prop) (fun _ => Real.exp_ne_zero _)).div_const 2
  have hPd (s : ℝ) : HasDerivAt P (A s/2) s :=
    intervalIntegral.integral_hasDerivAt_right (hAcont.intervalIntegrable 0 s)
      (hAcont.stronglyMeasurableAtFilter volume (𝓝 s)) hAcont.continuousAt
  have hθc : Continuous θ := by
    change Continuous (fun s => δ+T*max (1-s) 0)
    fun_prop
  have hUcont : Continuous U := by
    rw [continuous_iff_continuousAt]
    intro s
    exact cheegerHeat_tendsto_joint hfin h (backwardsHeatTime_pos hδ hT s)
      hθc.continuousAt ((smoothDensity_hasDerivAt hκ hc hu hnorm s).continuousAt)
  have hEc (ε : ℝ) (hε : 0 < ε) : Continuous (E ε) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (regularizedEntropy_hasFDeriv hε (U s)).continuousAt.comp hUcont.continuousAt
  have hprop := fun s => hπ.smoothDensity_properties hB hu hun hlaw hnorm
    hc.continuous (hc.continuous.integrable_of_hasCompactSupport hκ) hn hm s
  have hUn (s : ℝ) : ∀ᵐ x ∂m, 0 ≤ U s x :=
    cheegerHeat_nonneg h (backwardsHeatTime_pos hδ hT s).le _ (hprop s).1
  have hθeq (s : ℝ) (hs : s ≤ 1) : θ s = δ+T*(1-s) := by
    simp only [θ,backwardsHeatTime,max_eq_left (by linarith : 0 ≤ 1-s)]
  have hD := compact_dual_of_entropy_actions hfin o hUcont.continuousOn
    (fun ε hε => (hEc ε hε).continuousOn)
    (show ContinuousOn P (Icc 0 1) from (show Continuous P from
      continuous_iff_continuousAt.mpr fun s => (hPd s).continuousAt).continuousOn)
    (fun s _ => hPd s) (fun s _ => hUn s) (τ := -T) (a := A) (E := E) (by
      intro ε hε s hs
      have HH := cheegerHeat_diagonal_entropy_action hfin hID hpar h
        (backwardsHeatTime_hasDerivAt δ T hs.2)
        (smoothDensity_hasDerivAt hκ hc hu hnorm s) (backwardsHeatTime_pos hδ hT s)
        B.coe_nonneg (hprop s).2.1 (hprop s).1 (Real.exp_pos (2*k*θ s))
        (fun g hg => hgrad g _ hg (hprop s).1 B B.coe_nonneg (hprop s).2.1 (θ s)
          (backwardsHeatTime_pos hδ hT s).le)
        (hπ.smoothDensity_action hfin hb hgeo hB hu hun hlaw hnorm hκ hc hn hm s) hε
      simpa only [U,E,A,θ,backwardsHeatTime,
        max_eq_left (by linarith [hs.2] : 0 ≤ 1-s)] using HH) f hf hq
  intro ε hε
  have H := hD ε hε
  have hθ0 : θ 0 = δ+T := by rw [hθeq 0 zero_le_one]; ring
  have hθ1 : θ 1 = δ := by rw [hθeq 1 le_rfl]; ring
  dsimp only [U,E,P,A] at H
  rw [hθ0,hθ1,intervalIntegral.integral_same] at H
  linarith

end WeakHessian

end
end

end OAI
