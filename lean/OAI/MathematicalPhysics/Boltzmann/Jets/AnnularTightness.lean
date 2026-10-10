import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.OuterTightness
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTailRegions

namespace OAI

section

/-! # Annular bounds imply uniform integrability of physical gain and loss -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AnnularEnvelope

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem annular_gainLoss_uniformIntegrable {s₀ η T q A B : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T)
    (hq : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hmoment : ∀ n, ∀ᵐ u ∂timePositionVolume T,
      VelocityMoment.moment (fun v => f n (u,v)) ≤
        ENNReal.ofReal (commonMoment s₀ η A B (torusChart u)))
    (houter : ∀ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      ∀ᵐ u ∂timePositionVolume T, ∀ᵐ v : Velocity,
        u ∉ torusTail s₀ η J → f n (u,v) ≤ D*H q v) :
    UniformIntegrable (fun n => gainDensity (f n)) 1
      ((timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun n => lossDensity (f n)) 1
      ((timePositionVolume T).prod (volume : Measure Velocity)) := by
  classical
  choose D hD hDom using houter
  apply collision_gainLoss_uniformIntegrable hq hfm hf
    (fun u => commonMoment_nonneg hA hB s₀ η (torusChart u)) hmoment
    (torusTail_measurable s₀ η) hD hDom
  have hm : Measurable (fun u : ℝ × Position =>
      ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2)) := by
    exact (((commonMoment_measurable s₀ η A B).comp torusChart_measurable).pow_const 2).const_mul 3 |>.ennreal_ofReal
  have ht := ENNReal.Tendsto.const_mul
    (common_collision_tail_tendsto hs₀ hη hηmax hT A B)
    (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (4*Real.pi) ≠ ⊤))
  simp only [mul_zero] at ht
  simpa only [lintegral_const_mul _ hm] using ht

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Uniform annular geometry for a short window around an expanding box -/

noncomputable section
open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem window_center_norm {κ b : ℝ} (hκ : 0 < κ) (hb : 0 < b) :
    ‖transverse ((κ*b) • firstAxis)‖ = κ*b ∧ axial ((κ*b) • firstAxis) = 0 := by
  have ha : axial ((κ*b) • firstAxis) = 0 := by
    simp [axial,firstAxis,EuclideanSpace.single]
  have hn : ‖(κ*b) • firstAxis‖ = κ*b := by
    simp [norm_smul,axis_norms.1,Real.norm_eq_abs,abs_of_pos hκ,abs_of_pos hb]
  have hs := norm_sq_split ((κ*b) • firstAxis)
  rw [hn,ha] at hs
  exact ⟨by nlinarith [norm_nonneg (transverse ((κ*b) • firstAxis)),mul_pos hκ hb],ha⟩

theorem annular_window_bounds {κ b W u : ℝ} (hκ : 0 < κ) (hκsmall : κ ≤ 1)
    (hb : 0 < b) (hW : W ≤ κ*b/200) (hu : u ∈ Icc b (b+W))
    {x : V} (hx : ‖x-(κ*b) • firstAxis‖ ≤ κ*b/2+7*W) :
    κ*b/4 ≤ ‖transverse x‖ ∧ u ≤ (16/κ)*‖transverse x‖/2 ∧
      |axial x| ≤ (16/κ)*‖transverse x‖/2 := by
  have hc := window_center_norm hκ hb
  have hdist : ‖transverse x-transverse ((κ*b) • firstAxis)‖ ≤ κ*b/2+7*W := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le _).trans hx
  have hrad := norm_sub_norm_le (transverse ((κ*b) • firstAxis)) (transverse x)
  rw [norm_sub_rev,hc.1] at hrad
  have hr : κ*b/4 ≤ ‖transverse x‖ := by nlinarith [mul_pos hκ hb]
  have hkb : κ*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hκsmall hb.le]
  have ht : u ≤ 2*b := by linarith [hu.2]
  have hax : |axial x| ≤ κ*b/2+7*W := by
    have hh := (SmallInputGeometry.abs_axial_le_norm (x-(κ*b) • firstAxis)).trans hx
    simpa only [PlaneChart.axial_sub,hc.2,sub_zero] using hh
  have hscale : 2*b ≤ (16/κ)*‖transverse x‖/2 := by
    rw [show (16/κ)*‖transverse x‖/2 = 8*‖transverse x‖/κ by ring]
    apply (le_div_iff₀ hκ).mpr
    nlinarith
  exact ⟨hr,ht.trans hscale,(by linarith : |axial x| ≤ 2*b).trans hscale⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Simultaneous tightness of the density, collision pairs, gain and loss -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AnnularEnvelope
open BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem annular_unifTight {s₀ η T q A B : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T)
    (hq : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hmoment : ∀ n, ∀ᵐ u ∂timePositionVolume T,
      VelocityMoment.moment (fun v => f n (u,v)) ≤
        ENNReal.ofReal (commonMoment s₀ η A B (torusChart u)))
    (houter : ∀ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      ∀ᵐ u ∂timePositionVolume T, ∀ᵐ v : Velocity,
        u ∉ torusTail s₀ η J → f n (u,v) ≤ D*H q v) :
    UnifTight f 1 ((timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => pairDensity (f n)) 1
      ((timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun n => gainDensity (f n)) 1 ((timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => lossDensity (f n)) 1 ((timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hM (u : ℝ × Position) : 0 ≤ commonMoment s₀ η A B (torusChart u) :=
    commonMoment_nonneg hA hB _ _ _
  have hpair (n) : ∀ᵐ u ∂timePositionVolume T,
      VelocityMoment.pairMoment (fun v => f n (u,v)) ≤
        ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2) := by
    filter_upwards [hmoment n] with u hu
    exact VelocityMoment.pairMoment_le_square
      ((hfm n).comp (measurable_const.prodMk measurable_id)) (fun v => hf n (u,v)) (hM u) hu
  have hmass (n) : ∀ᵐ u ∂timePositionVolume T,
      (∫⁻ v : Velocity, ENNReal.ofReal (f n (u,v))) ≤
        ENNReal.ofReal (commonMoment s₀ η A B (torusChart u)) := by
    filter_upwards [hmoment n] with u hu
    exact (lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left (hf n (u,v)) (VelocityMoment.weight_one_le v)))).trans hu
  have hcollision (n) : ∀ᵐ u ∂timePositionVolume T,
      (∫⁻ v : Velocity, ENNReal.ofReal (gainDensity (f n) (u,v))) ≤
        ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2) ∧
      (∫⁻ v : Velocity, ENNReal.ofReal (lossDensity (f n) (u,v))) ≤
        ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2) := by
    filter_upwards [hpair n] with u hu
    have h := gainLoss_slice_mass_le (hfm n) (hf n) u
    have hb := mul_le_mul' (le_refl (ENNReal.ofReal (4*Real.pi))) hu
    exact ⟨h.1.trans hb,h.2.trans hb⟩
  have htail := common_collision_tail_tendsto hs₀ hη hηmax hT A B
  have hctail : Tendsto (fun J => ∫⁻ u in torusTail s₀ η J,
      ENNReal.ofReal (4*Real.pi)*ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2)
        ∂timePositionVolume T) atTop (𝓝 0) := by
    have hm : Measurable (fun u : ℝ × Position =>
        ENNReal.ofReal (3*(commonMoment s₀ η A B (torusChart u))^2)) :=
      (((commonMoment_measurable s₀ η A B).comp torusChart_measurable).pow_const 2).const_mul 3 |>.ennreal_ofReal
    have ht := ENNReal.Tendsto.const_mul htail
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (4*Real.pi) ≠ ⊤))
    simpa only [mul_zero,lintegral_const_mul _ hm] using ht
  refine ⟨?_,?_,?_,?_⟩
  · apply unifTight_of_spatial_cutoffs hfm hf (torusTail_measurable s₀ η) hmass
    · intro J
      obtain ⟨D,hD,hDom⟩ := houter J
      exact outer_density_unifTight hq hD hfm hf (torusTail_measurable s₀ η J) hDom
    · exact torus_tail_lintegral_tendsto hs₀.le hη.le
        (torus_common_integrable hs₀ hη hηmax hT hA hB) hM
  · apply unifTight_of_spatial_cutoffs (fun n => pairDensity_measurable (hfm n))
      (fun n => pairDensity_nonneg (hf n)) (torusTail_measurable s₀ η) hpair
    · intro J
      obtain ⟨D,hD,hDom⟩ := houter J
      exact outer_pairs_unifTight hq hD hfm hf (torusTail_measurable s₀ η J) hDom
    · exact htail
  · apply unifTight_of_spatial_cutoffs (fun n => gainDensity_measurable (hfm n))
      (fun n => gainDensity_nonneg (hf n)) (torusTail_measurable s₀ η)
      (fun n => (hcollision n).mono (fun _ h => h.1))
    · intro J
      obtain ⟨D,hD,hDom⟩ := houter J
      exact (outer_gainLoss_unifTight hq hD hfm hf (torusTail_measurable s₀ η J) hDom).1
    · exact hctail
  · apply unifTight_of_spatial_cutoffs (fun n => lossDensity_measurable (hfm n))
      (fun n => lossDensity_nonneg (hf n)) (torusTail_measurable s₀ η)
      (fun n => (hcollision n).mono (fun _ h => h.2))
    · intro J
      obtain ⟨D,hD,hDom⟩ := houter J
      exact (outer_gainLoss_unifTight hq hD hfm hf (torusTail_measurable s₀ η J) hDom).2
    · exact hctail

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
