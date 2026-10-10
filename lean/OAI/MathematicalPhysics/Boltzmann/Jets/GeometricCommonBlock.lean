import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxCommonDamping
import OAI.MathematicalPhysics.Boltzmann.Branching.CommonHistoryCore
import OAI.MathematicalPhysics.Boltzmann.Branching.WindowLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedHotMassGrowth

namespace OAI

/-! # A growing angular-history block with one clock and one core for all starts -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_common_block_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K b W s Δ a l : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(8*A₀) ≤ ε*K → 0 < b → W ≤ κ*b/200 →
      s ∈ Icc b (b+W) → (8*κ*A₀/K)*s ≤ Δ → Δ ≤ (16*κ*A₀/K)*s → Δ ≤ W →
      a ≤ s → 0 ≤ l →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d s →
      Real.exp η*l+6*Δ < ‖transverse x‖ →
      (6:ℝ≥0∞) < localizedHistoryBlockMass
        (beamCoefficients hθ hα hγ η (κ*b)) (K/(4*(κ*b)))
        (48*Real.pi*K/(κ*b)) (s+Δ) a η l s
        (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis))
        (lateBox κ d (s+Δ)) N
        (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V)))) := by
  have hdhalf : d ≤ 1/2 := by linarith
  obtain ⟨A₀,hA₀,hblock⟩ := lateBox_damped_duration_growth hd hdhalf hκ hκsmall hg
  obtain ⟨N,ε,γ₁,hε,hεsmall,hγ₁,hgrowth⟩ := hblock (12*referenceClock)
  have hM : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨γ₂,hγ₂,hcone⟩ := geometric_history_cone_conditions hε hεsmall hM
  refine ⟨A₀,hA₀,N,ε,min γ₁ γ₂,hε,hεsmall,lt_min hγ₁ hγ₂,?_⟩
  intro θ η α γ K b W s Δ a l hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge hb hW hs hlo hhi hΔW ha hl x v hp hcut
  let r := ‖transverse x‖
  let D := Real.toNNReal (192*Real.pi*r/(κ*b))
  have hspos : 0 < s := hb.trans_le hs.1
  have hscale := lateBox_geometric_scale hκ hκsmall.le hdhalf hspos hp
  have hr : 0 < r := hscale.1
  have hρ : 0 < K/(4*r) := by positivity
  have hΔ : 0 ≤ Δ := by
    apply le_trans _ hlo
    positivity
  have hdrange := window_damping_range hκ hκsmall.le hb hW hs hdhalf hp
  have hD0 : 0 ≤ 192*Real.pi*r/(κ*b) := referenceClock.property.trans hdrange.1
  have hDlo : referenceClock ≤ D := by
    apply (NNReal.coe_le_coe).mp
    simpa only [D,Real.coe_toNNReal _ hD0] using hdrange.1
  have hDhi : D ≤ 12*referenceClock := by
    apply (NNReal.coe_le_coe).mp
    simpa only [D,Real.coe_toNNReal _ hD0,NNReal.coe_mul,NNReal.coe_ofNat] using hdrange.2
  have hA := lateBox_duration_window hκ hspos hdhalf hK hA₀ hp hlo hhi
  have hshort : 6*Δ ≤ (ε/20)*r := by
    calc
      6*Δ ≤ 6*(8*A₀)/(K/(4*r)) := by
        apply (le_div_iff₀ hρ).mpr
        nlinarith [hA.2]
      _ ≤ _ := cylinder_small_of_density_scale hK hr hKlarge
  have hlocal := hcone hθ hη hηsmall hr hα hαsmall hγ
    (hγsmall.trans (min_le_right _ _)) hspos.le hscale.2.1 hshort ha hl hcut x (v:V) rfl hscale.2.2
  have hcomp := physicalBlock_le_localized hDlo (beamCoefficients hθ hα hγ η r)
    (Real.toNNReal (K/(4*r))) s Δ a η l κ d
    (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis)) x v hΔ
    ((show ‖(v:V)‖ ≤ 5 by simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right] using v.property).trans (by norm_num)) hp
    (fun q hq => boundedFlightCone_mem_commonCore hκ hκsmall.le hdsmall hb hW hs hΔW hp hq)
    hlocal N
  have hgr := hgrowth D hDlo hDhi hθ hη hηsmall hα hαsmall hγ
    (hγsmall.trans (min_le_left _ _)) hK hKlarge hspos hlo hhi x v hp
  have hρcoe : (Real.toNNReal (K/(4*r)):ℝ) = K/(4*r) := Real.coe_toNNReal _ hρ.le
  have hDcoe : (D:ℝ) = 192*Real.pi*r/(κ*b) := Real.coe_toNNReal _ hD0
  rw [hρcoe,hDcoe,window_damping_normalization hκ hb hr] at hcomp
  have hh := hgr.trans_le hcomp
  rw [localizedHistoryBlockMass_independent hθ hK.le hα hγ hr (mul_pos hκ hb)] at hh
  exact hh

end BoltzmannNonuniqueness.GeometricBackground

end

end OAI
