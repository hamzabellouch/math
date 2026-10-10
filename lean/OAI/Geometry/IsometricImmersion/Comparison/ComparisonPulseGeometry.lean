import OAI.Geometry.IsometricImmersion.Comparison.ComparisonEnergyScaling

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem pulseStrip_subset_comparisonSlab
    {a delta tau speed : ℝ} (_ha : 0 ≤ a) (_hd : 0 ≤ delta) (_ht : 0 < tau)
    (hs : 0 ≤ speed) (htravel : speed*(2*delta/tau) ≤ 3*a) :
    pulseStrip a delta tau ⊆ shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed := by
  intro p hp
  have hpT : p 1 ∈ Icc (-(delta/tau)) (delta/tau) := hp.2
  have hm : speed*(p 1-(-(delta/tau))) ≤ speed*(2*delta/tau) := by
    apply mul_le_mul_of_nonneg_left _ hs
    calc
      _ ≤ delta/tau+delta/tau := by linarith [hpT.2]
      _ = _ := by ring
  refine ⟨hpT,?_⟩
  change -(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
    p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))
  constructor <;> linarith [hp.1.1,hp.1.2]

theorem comparisonSlab_subset_dataStrip
    {a delta tau speed : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ speed) :
    shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed ⊆
      pulseStrip (8*a) delta tau := by
  intro p hp
  have hinc : 0 ≤ speed*(p 1-(-(delta/tau))) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
  refine ⟨?_,hp.1⟩
  change -(8*a) ≤ p 0 ∧ p 0 ≤ 8*a
  change p 1 ∈ Icc (-(delta/tau)) (delta/tau) ∧
    (-(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
      p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))) at hp
  constructor <;> linarith [hp.2.1,hp.2.2]

theorem comparison_pulse_travel_bound
    {a delta tau speed : ℝ} (ha : 0 < a) (ht : 0 < tau)
    (hlarge : 2*speed*delta/(3*a) ≤ tau) : speed*(2*delta/tau) ≤ 3*a := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht).mpr
  convert (div_le_iff₀ (by positivity : 0 < 3*a)).mp hlarge using 1 <;> ring

theorem comparison_pulse_geometry_eventually
    {a speed : ℝ} (ha : 0 < a) (hs : 0 ≤ speed) (delta : ℝ) (hd : 0 ≤ delta) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
      speed*(2*delta/(tau : ℝ)) ≤ 3*a ∧
      pulseStrip a delta (tau : ℝ) ⊆
        shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ∧
      shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ⊆
        pulseStrip (8*a) delta (tau : ℝ) := by
  have hlarge : ∀ᶠ tau : ℕ in atTop, max 1 (2*speed*delta/(3*a)) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlarge] with tau htau
  have ht1 : 1 ≤ (tau : ℝ) := (le_max_left _ _).trans htau
  have ht : (0 : ℝ) < tau := zero_lt_one.trans_le ht1
  have htravel := comparison_pulse_travel_bound ha ht ((le_max_right _ _).trans htau)
  exact ⟨ht1,htravel,pulseStrip_subset_comparisonSlab ha.le hd ht hs htravel,
    comparisonSlab_subset_dataStrip ha.le hs⟩

end SmoothLocal.Pulse

end

end OAI
