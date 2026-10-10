import OAI.NumberTheory.CubicMoment.Estimates.VaryingConductorSequences
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorUniform

namespace OAI

/-! Uniform exceptional moments hold throughout a fixed open neighborhood
of each exceptional conductor exponent. The neighborhoods are constructed by
contradiction from actual short-factor sequences, not assumed as analytic inputs. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma HasPowerExponent.of_shrinking_window {Y N δ : ℕ → ℝ} {a : ℝ}
    (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hb : ∀ j, (Y j)^(a-δ j) ≤ N j ∧ N j ≤ (Y j)^(a+δ j)) :
    HasPowerExponent Y N a := by
  have hlo : HasPowerExponent Y (fun j => (Y j)^(a-δ j)) a := by
    apply HasPowerExponent.variable_rpow hY
    simpa only [sub_zero] using tendsto_const_nhds.sub hδ
  have hhi : HasPowerExponent Y (fun j => (Y j)^(a+δ j)) a := by
    apply HasPowerExponent.variable_rpow hY
    simpa only [add_zero] using tendsto_const_nhds.add hδ
  apply hlo.squeeze' hhi
  · filter_upwards with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (Real.rpow_pos_of_pos (by linarith [hY₁ j]) _) (hb j).1)
      (Real.log_pos (hY₁ j)).le
  · filter_upwards with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log ((Real.rpow_pos_of_pos (by linarith [hY₁ j]) _).trans_le
        (hb j).1) (hb j).2) (Real.log_pos (hY₁ j)).le

private theorem neighborhood_saving_of_no_countersequence {T : Type*}
    (scale mass : T → ℝ) (valid : ℝ → T → Prop)
    (hno : ∀ x : ℕ → T, (∀ j : ℕ, valid (1/((j:ℝ)+1)) (x j)) →
      (∀ j : ℕ, (j:ℝ)+2 ≤ scale (x j)) →
      (∀ j : ℕ, (scale (x j))^(7/3-1/((j:ℝ)+1)) ≤ mass (x j)) → False) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ x : T,
      valid κ x → Y₀ ≤ scale x → mass x ≤ (scale x)^(7/3-ε) := by
  by_contra h
  push Not at h
  have hex (j : ℕ) : ∃ x : T, valid (1/((j:ℝ)+1)) x ∧
      (j:ℝ)+2 ≤ scale x ∧ (scale x)^(7/3-1/((j:ℝ)+1)) ≤ mass x := by
    obtain ⟨x,hx,hY,hm⟩ := h (1/((j:ℝ)+1)) (by positivity)
      (1/((j:ℝ)+1)) (by positivity) ((j:ℝ)+2)
    exact ⟨x,hx,hY,hm.le⟩
  choose x hx hY hm using hex
  exact hno x hx hY hm

private lemma neighborhood_scale_tendsto {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) : Tendsto Y atTop atTop :=
  tendsto_atTop_mono (fun j => by linarith [hY j])
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop)

private lemma neighborhood_lower_exponent {Y : ℕ → ℝ}
    (hY : Tendsto Y atTop atTop) :
    HasPowerExponent Y (fun j => (Y j)^(7/3-1/((j:ℝ)+1))) (7/3) := by
  apply HasPowerExponent.variable_rpow hY
  simpa only [sub_zero] using (tendsto_const_nhds (x := (7/3:ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma neighborhood_lower_ge_one {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) (j : ℕ) :
    1 ≤ (Y j)^(7/3-1/((j:ℝ)+1)) := by
  apply Real.one_le_rpow (by linarith [hY j,Nat.cast_nonneg (α := ℝ) j])
  have hdiv : 1/((j:ℝ)+1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  linarith

structure ConductorMomentInstance (ι κ : Type*) extends ShortMomentInstance ι κ where
  conductorScale : ℝ

private def neighborhoodFamily {ι κ : Type*} (x : ℕ → ConductorMomentInstance ι κ) :
    ShortFactorFamily ι where
  cutoff := fun j => (x j).family.cutoff 0
  length := fun j => (x j).family.length 0
  coefficient := fun j => (x j).family.coefficient 0
  twist := fun j => (x j).family.twist 0
  factor_spec := fun j => (x j).family.factor_spec 0
  length_ge_one := fun j => (x j).family.length_ge_one 0
  twist_bound := fun j => (x j).family.twist_bound 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubicNeighborhoodAdmissible (δ H D C κ : ℝ)
    (x : ConductorMomentInstance ι Eisenstein) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  (x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
  (∏ i, x.family.length 0 i) ≤ C*x.scale ∧
  1 ≤ x.conductorScale ∧
  (x.scale^(1-κ) ≤ x.conductorScale ∧ x.conductorScale ≤ x.scale^(1+κ)) ∧
  (∀ p ∈ x.rows, gramDyad x.conductorScale p) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.cubicValue 0 i p‖ ≤ x.scale^H)

theorem cubic_short_neighborhood_power {δ H D C : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ConductorMomentInstance ι Eisenstein,
        cubicNeighborhoodAdmissible δ H D C κ x → Y₀ ≤ x.scale →
          cubicInstanceMoment x.toShortMomentInstance ≤ x.scale^(7/3-ε) := by
  apply neighborhood_saving_of_no_countersequence
    (fun x : ConductorMomentInstance ι Eisenstein => x.scale)
    (fun x => cubicInstanceMoment x.toShortMomentInstance)
    (cubicNeighborhoodAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let N : ℕ → ℝ := fun j => (x j).conductorScale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := neighborhoodFamily x
  have hYlim : Tendsto Y atTop atTop := neighborhood_scale_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC
      (Eventually.of_forall (fun j => ⟨(hx j).2.1,(hx j).2.2.1⟩))
  have hNexp : HasPowerExponent Y N 1 :=
    HasPowerExponent.of_shrinking_window hYlim (fun j => by linarith [hY₂ j])
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun j => (hx j).2.2.2.2.1)
  exact F.first_varying_conductor_sequence_impossible Y N G (fun j => (x j).rows)
    hδ hH hD hYlim hY₂ (neighborhood_lower_ge_one hY)
    (neighborhood_lower_exponent hYlim) (fun j => (hx j).2.2.2.1) hNexp
    (fun j => (hx j).2.2.2.2.2.1) (fun j => (hx j).2.2.2.2.2.2.1)
    (fun j => (hx j).1) htotal (fun j => (hx j).2.2.2.2.2.2.2) hm

def mixedNeighborhoodAdmissible (δ H D C κ : ℝ)
    (x : ConductorMomentInstance ι (Eisenstein × Eisenstein)) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  (x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
  (∏ i, x.family.length 0 i) ≤ C*x.scale ∧
  1 ≤ x.conductorScale ∧
  (x.scale^(1/3-κ) ≤ x.conductorScale ∧ x.conductorScale ≤ x.scale^(1/3+κ)) ∧
  (∀ p ∈ x.rows, PrimarySquarefreePair p ∧
    norm p.1 ≤ x.conductorScale ∧ norm p.2 ≤ x.conductorScale) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.mixedValue 0 i p‖ ≤ x.scale^H)

theorem mixed_short_neighborhood_power (hHuxley : HuxleyAdditiveLargeSieve)
    {δ H D C : ℝ} (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ConductorMomentInstance ι (Eisenstein × Eisenstein),
        mixedNeighborhoodAdmissible δ H D C κ x → Y₀ ≤ x.scale →
          mixedInstanceMoment x.toShortMomentInstance ≤ x.scale^(7/3-ε) := by
  apply neighborhood_saving_of_no_countersequence
    (fun x : ConductorMomentInstance ι (Eisenstein × Eisenstein) => x.scale)
    (fun x => mixedInstanceMoment x.toShortMomentInstance)
    (mixedNeighborhoodAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let L : ℕ → ℝ := fun j => (x j).conductorScale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := neighborhoodFamily x
  have hYlim : Tendsto Y atTop atTop := neighborhood_scale_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC
      (Eventually.of_forall (fun j => ⟨(hx j).2.1,(hx j).2.2.1⟩))
  have hLexp : HasPowerExponent Y L (1/3) :=
    HasPowerExponent.of_shrinking_window hYlim (fun j => by linarith [hY₂ j])
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun j => (hx j).2.2.2.2.1)
  exact F.balanced_varying_conductor_sequence_impossible hHuxley Y L G
    (fun j => (x j).rows) hδ hH hD hYlim hY₂ (neighborhood_lower_ge_one hY)
    (neighborhood_lower_exponent hYlim) (fun j => (hx j).2.2.2.1) hLexp
    (fun j => (hx j).2.2.2.2.2.1) (fun j => (hx j).2.2.2.2.2.2.1)
    (fun j => (hx j).1) htotal (fun j => (hx j).2.2.2.2.2.2.2) hm

end CubicFirstMoment

end

end OAI
