import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PlanHeatEntropy
import OAI.Geometry.WeakHessian.Transport.TestAction
import OAI.Geometry.WeakHessian.Transport.PerturbedAction

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

def hopfUniformLip (f : X →ᵇ ℝ) (q : ℝ) : ℝ :=
  Real.sqrt (4*(q+1)*‖f‖)/q+1/(2*q)+2*‖f‖

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma hopfUniformLip_nonneg (f : X →ᵇ ℝ) {q : ℝ} (hq : 0 < q) : 0 ≤ hopfUniformLip f q := by
  dsimp [hopfUniformLip]; positivity

omit [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X] in
lemma boundedHopfMap_lipschitz_uniform (f : X →ᵇ ℝ) {q t : ℝ}
    (hq : 0 < q) (ht : t ∈ Icc q (q+1)) :
    LipschitzWith ⟨hopfUniformLip f q,hopfUniformLip_nonneg f hq⟩ (boundedHopfMap f t : X → ℝ) := by
  have ht0 := hq.trans_le ht.1
  let D := Real.sqrt (4*(q+1)*‖f‖)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDs : D^2 = 4*(q+1)*‖f‖ := Real.sq_sqrt (by positivity)
  have H := hopfLax_lipschitz_radius f.continuous
    (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
    (by linarith [norm_nonneg f]) ht0 hD (by rw [hDs]; nlinarith [norm_nonneg f,ht.2])
  have hL : (⟨D/t+1/(2*t)+(‖f‖-(-‖f‖)),by simp only [sub_neg_eq_add]; positivity⟩ : ℝ≥0) ≤
      ⟨hopfUniformLip f q,hopfUniformLip_nonneg f hq⟩ := by
    change D/t+1/(2*t)+(‖f‖-(-‖f‖)) ≤ D/q+1/(2*q)+2*‖f‖
    have h1 := div_le_div_of_nonneg_left hD hq ht.1
    have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by positivity : 0 < 2*q) (by linarith [ht.1] : 2*q ≤ 2*t)
    linarith
  convert H.weaken hL using 1
  funext x
  exact boundedHopfMap_apply_pos f ht0 x

omit [SigmaFinite m] in
lemma compact_dual_of_entropy_test_actions
    (hfin : FiniteOnBoundedSets m) (o : X)
    {u : ℝ → Lp ℝ 2 m} {E : ℝ → ℝ → ℝ} {P a : ℝ → ℝ} {τ : ℝ}
    (hu : ContinuousOn u (Icc 0 1))
    (hE : ∀ ε, 0 < ε → ContinuousOn (E ε) (Icc 0 1))
    (hP : ContinuousOn P (Icc 0 1))
    (hP' : ∀ s ∈ Ico (0:ℝ) 1, HasDerivAt P (a s/2) s)
    (hun : ∀ z, 0 ≤ z → ∀ᵐ x ∂m, 0 ≤ u z x)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {q : ℝ} (hq : 0 < q)
    (hA : ∀ ε, 0 < ε → ∀ s ∈ Ico (0:ℝ) 1, ∀ w : Lp ℝ 2 m,
      Sobolev m (w : X → ℝ) →
      (∀ᵐ x ∂m,|weakGradient m w x| ≤ hopfUniformLip f q) →
      ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt u v s ∧ HasDerivAt (E ε) e s ∧
      2*⟪v,w⟫_ℝ ≤ a s-2*τ*e+∫ x,(u s x+ε)*(weakGradient m w x)^2 ∂m) :
    ∀ ε, 0 < ε →
      (∫ x, u 1 x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, u 0 x*boundedHopfMap f q x ∂m)+τ*(E ε 1-E ε 0) ≤ P 1-P 0+ε*compactHopfDualBound hfin o f hf hq/2 := by
  let data := compactHopf_exists_L2_curve hfin f o hf hq (by linarith : q ≤ q+1)
  let W := data.choose
  obtain ⟨hWe,hWc,hWS,hΓ,hD,hHJ⟩ := data.choose_spec.choose_spec
  intro ε hε
  have hmap : MapsTo (fun s : ℝ => q+s) (Icc 0 1) (Icc q (q+1)) := by
    intro s hs; constructor <;> linarith [hs.1,hs.2]
  have H := integrated_hamiltonJacobi_test_action (W := fun s => W (q+s)) hq hε.le
    (hWc.comp (by fun_prop) hmap) hu (hE ε hε) hP hP'
    (fun s hs => hWS _ (by linarith [hs.1]))
    (fun s hs => hΓ _ (by linarith [hs.1]))
    (fun s hs => hD _ (hmap ⟨hs.1,hs.2.le⟩)) hun
    (fun s z hs hsz => by
      have H := hHJ (q+s) (q+z) (by linarith) (by linarith)
      simpa only [add_sub_add_left_eq_sub] using H) (by
      intro s hs
      apply hA ε hε s hs _ (hWS _ (by linarith [hs.1]))
      filter_upwards [weakGradient_congr_ae (hWe (q+s) (by linarith [hs.1])),
        weakGradient_le_lipschitz hfin (boundedHopfMap_lipschitz_uniform f hq (hmap ⟨hs.1,hs.2.le⟩)),
        weakGradient_nonneg (m := m) (W (q+s))] with x he hb hn
      rw [abs_of_nonneg hn,he]; exact hb)
  have hpair (s : ℝ) (hs : 0 ≤ s) : ⟪W (q+s),u s⟫_ℝ =
      ∫ x, u s x*boundedHopfMap f (q+s) x ∂m := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWe (q+s) (by linarith)] with x hx
    simp only [W,hx,RCLike.inner_apply,RCLike.conj_to_real]
  rw [hpair 1 zero_le_one,hpair 0 le_rfl] at H
  simpa only [add_zero,compactHopfDualBound,data] using H

lemma cheegerHeat_plan_entropy_dual_error
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
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
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ))
    {b : ℝ → ℝ} (hbc : ContinuousOn b (Ici 0)) (hbp : ∀ t,0 ≤ t → 0 < b t)
    {R : ℝ → Lp ℝ 2 m → ℝ} {Eerror : ℝ}
    (hgrad : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m, Sobolev m (v : X → ℝ) →
      b (backwardsHeatTime δ T s)*(∫ x,smoothDensity κ u s x*
        (weakGradient m (cheegerHeat h (backwardsHeatTime δ T s) v) x)^2 ∂m) ≤
        (∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)+R s v)
    (hsplit : ∀ s ∈ Ico (0:ℝ) 1, ∀ v w : Lp ℝ 2 m,Sobolev m (v : X → ℝ) → Sobolev m (w : X → ℝ) →
      ∀ t : ℝ,R s (v+t•w) ≤ 2*R s v+2*t^2*R s w)
    (hrelative : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      2*R s v ≤ ∫ x,cheegerHeat h (backwardsHeatTime δ T s) (smoothDensity κ u s) x*(weakGradient m v x)^2 ∂m)
    (herror : ∀ s ∈ Ico (0:ℝ) 1, ∀ v : Lp ℝ 2 m,Sobolev m (v : X → ℝ) →
      (∀ᵐ x ∂m,|weakGradient m v x| ≤ hopfUniformLip f q) → R s v ≤ Eerror) :
    ∀ ε, 0 < ε →
      (∫ x, cheegerHeat h δ (smoothDensity κ u 1) x*boundedHopfMap f (q+1) x ∂m)-
        (∫ x, cheegerHeat h (δ+T) (smoothDensity κ u 0) x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) (smoothDensity κ u 0) x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ (smoothDensity κ u 1) x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, planKineticCost π/b (backwardsHeatTime δ T s)/2)+Eerror+
        ε*compactHopfDualBound hfin o f hf hq/2 := by
  let θ := backwardsHeatTime δ T
  let U := fun s => cheegerHeat h (θ s) (smoothDensity κ u s)
  let E := fun ε s => ∫ x, regularizedEntropy ε (U s x) ∂m
  let A := fun s => planKineticCost π/b (θ s)+2*Eerror
  let P := fun s => ∫ r in (0:ℝ)..s, A r/2
  have hθc : Continuous θ := by
    change Continuous (fun s => δ+T*max (1-s) 0); fun_prop
  have hbθ : Continuous (fun s => b (θ s)) := hbc.comp_continuous hθc (fun s => (backwardsHeatTime_pos hδ hT s).le)
  have hAcont : Continuous (fun s => A s/2) := by
    dsimp [A]
    exact ((continuous_const.div hbθ (fun s => (hbp _ (backwardsHeatTime_pos hδ hT s).le).ne')).add continuous_const).div_const 2
  have hPd (s : ℝ) : HasDerivAt P (A s/2) s :=
    intervalIntegral.integral_hasDerivAt_right (hAcont.intervalIntegrable 0 s)
      (hAcont.stronglyMeasurableAtFilter volume (𝓝 s)) hAcont.continuousAt
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
  have hD := compact_dual_of_entropy_test_actions hfin o hUcont.continuousOn
    (fun ε hε => (hEc ε hε).continuousOn)
    (show ContinuousOn P (Icc 0 1) from (show Continuous P from
      continuous_iff_continuousAt.mpr fun s => (hPd s).continuousAt).continuousOn)
    (fun s _ => hPd s) (fun s _ => hUn s) f hf hq (τ := -T) (a := A) (E := E) (by
      intro ε hε s hs v hv hvb
      have HH := cheegerHeat_diagonal_entropy_test_error hfin hID hpar h
        (backwardsHeatTime_hasDerivAt δ T hs.2)
        (smoothDensity_hasDerivAt hκ hc hu hnorm s) (backwardsHeatTime_pos hδ hT s)
        B.coe_nonneg (hprop s).2.1 (hprop s).1 (hbp _ (backwardsHeatTime_pos hδ hT s).le)
        (hgrad s hs) (hsplit s hs) (hrelative s hs)
        (hπ.smoothDensity_action hfin hb hgeo hB hu hun hlaw hnorm hκ hc hn hm s) hε hv (herror s hs v hv hvb)
      exact HH)
  intro ε hε
  have H := hD ε hε
  have hθ0 : θ 0 = δ+T := by simp [θ,backwardsHeatTime]
  have hθ1 : θ 1 = δ := by simp [θ,backwardsHeatTime]
  have hInt : P 1 = (∫ r in (0:ℝ)..1,planKineticCost π/b (θ r)/2)+Eerror := by
    dsimp [P,A]
    simp_rw [add_div,show 2*Eerror/2 = Eerror by ring]
    have hkinc : Continuous (fun r => planKineticCost π/b (θ r)/2) :=
      (continuous_const.div hbθ (fun s => (hbp _ (backwardsHeatTime_pos hδ hT s).le).ne')).div_const 2
    rw [intervalIntegral.integral_add (hkinc.intervalIntegrable 0 1)
      (intervalIntegrable_const (c := Eerror)),intervalIntegral.integral_const]
    simp
  rw [hInt] at H
  dsimp only [U,E,P] at H
  rw [hθ0,hθ1,intervalIntegral.integral_same] at H
  linarith

end WeakHessian

end
end

end OAI
