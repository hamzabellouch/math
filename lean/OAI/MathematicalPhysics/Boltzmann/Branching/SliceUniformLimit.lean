import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import Mathlib.Topology.MetricSpace.Cauchy

namespace OAI

/-! # Bounded measurable limits with uniform a.e. control on every time slice -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem exists_slice_uniform_limit {R : ℝ} (hR : 0 ≤ R)
    {F : ℕ → ℝ × JetPrototype.Phase → ℝ} {a : ℕ → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF : ∀ n u, 0 ≤ F n u ∧ F n u ≤ R)
    (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hclose : ∀ n m t, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |F n (t,p)-F m (t,p)| ≤ a n+a m) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧ (∀ u, 0 ≤ G u ∧ G u ≤ R) ∧
      (∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, |F n (t,p)-G (t,p)| ≤ a n) ∧
      ∀ v : (ℝ × JetPrototype.Phase) → ℝ × JetPrototype.Phase,
        (∀ n u, F n (v u) = F n u) → ∀ u, G (v u) = G u := by
  classical
  let P (u : ℝ × JetPrototype.Phase) := ∀ n m, |F n u-F m u| ≤ a n+a m
  let H (n : ℕ) (u : ℝ × JetPrototype.Phase) := if P u then F n u else 0
  have hPm : MeasurableSet {u | P u} := by
    simp only [P,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun m =>
      measurableSet_le ((hFm n).sub (hFm m)).abs measurable_const))
  have hHm (n) : Measurable (H n) := (hFm n).ite hPm measurable_const
  have hHb (n) (u) : 0 ≤ H n u ∧ H n u ≤ R := by
    dsimp [H]; split_ifs
    · exact hF n u
    · exact ⟨le_rfl,hR⟩
  have hHH (n m) (u) : |H n u-H m u| ≤ a n+a m := by
    by_cases hu : P u
    · simpa only [H,ite_eq_left hu] using hu n m
    · simpa only [H,ite_eq_right hu,sub_self,abs_zero] using add_nonneg (ha n) (ha m)
  have hCauchy (u) : CauchySeq (fun n => H n u) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have he : ∀ᶠ n in atTop, a n < ε/2 := (tendsto_order.mp ha0).2 _ (by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    refine ⟨N,fun n hn m hm => ?_⟩
    rw [Real.dist_eq]
    exact (hHH n m u).trans_lt (by linarith [hN n hn,hN m hm])
  have hex (u) : ∃ x : ℝ, Tendsto (fun n => H n u) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete (hCauchy u)
  let G (u : ℝ × JetPrototype.Phase) := Classical.choose (hex u)
  have hGlim (u) : Tendsto (fun n => H n u) atTop (𝓝 (G u)) := Classical.choose_spec (hex u)
  have hGm : Measurable G := measurable_of_tendsto_metrizable hHm (tendsto_pi_nhds.mpr hGlim)
  have hGb (u) : 0 ≤ G u ∧ G u ≤ R :=
    ⟨ge_of_tendsto' (hGlim u) (fun n => (hHb n u).1),
      le_of_tendsto' (hGlim u) (fun n => (hHb n u).2)⟩
  have hHG (n) (u) : |H n u-G u| ≤ a n := by
    have h := le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub (hGlim u)).abs)
      (tendsto_const_nhds.add ha0) (fun m => hHH n m u)
    simpa only [add_zero] using h
  refine ⟨G,hGm,hGb,?_,?_⟩
  · intro n t
    have hPa : ∀ᵐ p ∂FlightMeasure.phaseVolume, P (t,p) :=
      ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun m => hclose k m t))
    filter_upwards [hPa] with p hp
    simpa only [H,ite_eq_left hp] using hHG n (t,p)
  · intro v hv u
    have hPv : P (v u) ↔ P u := by
      simp only [P,hv]
    have hHv (n) : H n (v u) = H n u := by
      by_cases hp : P u
      · simp only [H,ite_eq_left hp,ite_eq_left (hPv.mpr hp),hv]
      · simp only [H,ite_eq_right hp,ite_eq_right (mt hPv.mp hp)]
    exact tendsto_nhds_unique (hGlim (v u)) (by simpa only [hHv] using hGlim u)

end BoltzmannNonuniqueness

end

end OAI
