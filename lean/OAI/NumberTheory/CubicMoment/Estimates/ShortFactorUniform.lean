import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorSequences

namespace OAI

/-! Uniform power saving from the proved actual-sequence contradictions. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private theorem power_saving_of_no_countersequence {T : Type*}
    (scale mass : T → ℝ) (valid : T → Prop)
    (hno : ∀ x : ℕ → T, (∀ j : ℕ, valid (x j)) →
      (∀ j : ℕ, (j:ℝ)+2 ≤ scale (x j)) →
      (∀ j : ℕ, (scale (x j))^(7/3-1/((j:ℝ)+1)) ≤ mass (x j)) → False) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ x : T,
      valid x → Y₀ ≤ scale x → mass x ≤ (scale x)^(7/3-ε) := by
  by_contra h
  push Not at h
  have hex (j : ℕ) : ∃ x : T, valid x ∧ (j:ℝ)+2 ≤ scale x ∧
      (scale x)^(7/3-1/((j:ℝ)+1)) ≤ mass x := by
    obtain ⟨x,hx,hY,hm⟩ := h (1/((j:ℝ)+1)) (by positivity) ((j:ℝ)+2)
    exact ⟨x,hx,hY,hm.le⟩
  choose x hx hY hm using hex
  exact hno x hx hY hm

private lemma countersequence_tendsto {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) : Tendsto Y atTop atTop :=
  tendsto_atTop_mono (fun j => by linarith [hY j])
    (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j:ℝ)) atTop atTop)

private lemma countersequence_lower_exponent {Y : ℕ → ℝ}
    (hY : Tendsto Y atTop atTop) :
    HasPowerExponent Y (fun j => (Y j)^(7/3-1/((j:ℝ)+1))) (7/3) := by
  apply HasPowerExponent.variable_rpow hY
  simpa only [sub_zero] using (tendsto_const_nhds (x := (7/3:ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private lemma countersequence_lower_ge_one {Y : ℕ → ℝ}
    (hY : ∀ j : ℕ, (j:ℝ)+2 ≤ Y j) (j : ℕ) : 1 ≤ (Y j)^(7/3-1/((j:ℝ)+1)) := by
  apply Real.one_le_rpow (by linarith [hY j,Nat.cast_nonneg (α := ℝ) j])
  have hdiv : 1/((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  linarith

/-- Multiplicative comparability is enough to identify the total logarithmic
length exponent; the bounded dyadic discrepancy disappears in the limit. -/
lemma HasPowerExponent.of_comparable {Y f : ℕ → ℝ} {C : ℝ}
    (hY : Tendsto Y atTop atTop) (hC : 0 < C)
    (hbound : ∀ᶠ j in atTop, Y j/C ≤ f j ∧ f j ≤ C*Y j) :
    HasPowerExponent Y f 1 := by
  have hbase : HasPowerExponent Y Y 1 := by
    simpa only [Real.rpow_one] using HasPowerExponent.variable_rpow hY
      (tendsto_const_nhds (x := (1:ℝ)))
  have hpos := hY.eventually_gt_atTop 0
  apply (hbase.const_mul hY (inv_pos.mpr hC) hpos).squeeze'
    (hbase.const_mul hY hC hpos)
  · filter_upwards [hbound,hY.eventually_gt_atTop 1] with j hj hYj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    apply Real.log_le_log (mul_pos (inv_pos.mpr hC) (by linarith))
    simpa only [div_eq_mul_inv,mul_comm] using hj.1
  · filter_upwards [hbound,hY.eventually_gt_atTop 1] with j hj hYj
    apply div_le_div_of_nonneg_right _ (Real.log_pos hYj).le
    exact Real.log_le_log ((div_pos (by linarith) hC).trans_le hj.1) hj.2

structure ShortMomentInstance (ι κ : Type*) where
  scale : ℝ
  family : ShortFactorFamily ι
  rows : Finset κ

private def assembleShortFamily {ι κ : Type*} (x : ℕ → ShortMomentInstance ι κ) :
    ShortFactorFamily ι where
  cutoff := fun j => (x j).family.cutoff 0
  length := fun j => (x j).family.length 0
  coefficient := fun j => (x j).family.coefficient 0
  twist := fun j => (x j).family.twist 0
  factor_spec := fun j => (x j).family.factor_spec 0
  length_ge_one := fun j => (x j).family.length_ge_one 0
  twist_bound := fun j => (x j).family.twist_bound 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubicInstanceMoment (x : ShortMomentInstance ι Eisenstein) : ℝ :=
  ∑ p ∈ x.rows, ‖∏ i, x.family.cubicValue 0 i p‖^2

def cubicInstanceAdmissible (δ H D C : ℝ) (x : ShortMomentInstance ι Eisenstein) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  ((x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
    (∏ i, x.family.length 0 i) ≤ C*x.scale) ∧
  (∀ p ∈ x.rows, gramDyad x.scale p) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.cubicValue 0 i p‖ ≤ x.scale^H)

/-- Uniform power saving for all actual first-configuration short factors
separated from length exponent one. The auxiliary size bounds are explicit. -/
theorem cubic_short_uniform_power {δ H D C : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ShortMomentInstance ι Eisenstein, cubicInstanceAdmissible δ H D C x →
        Y₀ ≤ x.scale → cubicInstanceMoment x ≤ x.scale^(7/3-ε) := by
  apply power_saving_of_no_countersequence ShortMomentInstance.scale cubicInstanceMoment
    (cubicInstanceAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := assembleShortFamily x
  have hYlim : Tendsto Y atTop atTop := countersequence_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC (Eventually.of_forall (fun j => (hx j).2.1))
  exact F.first_unsaved_sequence_impossible Y G (fun j => (x j).rows) hδ hH hD
    hYlim hY₂ (countersequence_lower_ge_one hY) (countersequence_lower_exponent hYlim)
    (fun j => (hx j).2.2.1) (fun j => (hx j).2.2.2.1) (fun j => (hx j).1) htotal
    (fun j => (hx j).2.2.2.2) hm

def mixedInstanceMoment (x : ShortMomentInstance ι (Eisenstein × Eisenstein)) : ℝ :=
  ∑ p ∈ x.rows, ‖∏ i, x.family.mixedValue 0 i p‖^2

def mixedInstanceAdmissible (δ H D C : ℝ)
    (x : ShortMomentInstance ι (Eisenstein × Eisenstein)) : Prop :=
  (∀ i, x.family.length 0 i ≤ x.scale^(1-δ)) ∧
  ((x.scale/C ≤ ∏ i, x.family.length 0 i) ∧
    (∏ i, x.family.length 0 i) ≤ C*x.scale) ∧
  (∀ p ∈ x.rows, PrimarySquarefreePair p ∧ norm p.1 ≤ x.scale^(1/3:ℝ) ∧
    norm p.2 ≤ x.scale^(1/3:ℝ)) ∧
  (x.rows.card:ℝ) ≤ x.scale^D ∧
  (∀ p ∈ x.rows, ∀ i, ‖x.family.mixedValue 0 i p‖ ≤ x.scale^H)

/-- The analogous uniform power saving in the balanced configuration. -/
theorem mixed_short_uniform_power (hHuxley : HuxleyAdditiveLargeSieve) {δ H D C : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ x : ShortMomentInstance ι (Eisenstein × Eisenstein),
        mixedInstanceAdmissible δ H D C x → Y₀ ≤ x.scale →
          mixedInstanceMoment x ≤ x.scale^(7/3-ε) := by
  apply power_saving_of_no_countersequence ShortMomentInstance.scale mixedInstanceMoment
    (mixedInstanceAdmissible δ H D C)
  intro x hx hY hm
  let Y : ℕ → ℝ := fun j => (x j).scale
  let G : ℕ → ℝ := fun j => (Y j)^(7/3-1/((j:ℝ)+1))
  let F := assembleShortFamily x
  have hYlim : Tendsto Y atTop atTop := countersequence_tendsto hY
  have hY₂ (j : ℕ) : 2 ≤ Y j := by linarith [hY j,Nat.cast_nonneg (α := ℝ) j]
  have htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1 :=
    HasPowerExponent.of_comparable hYlim hC (Eventually.of_forall (fun j => (hx j).2.1))
  exact F.balanced_unsaved_sequence_impossible hHuxley Y G (fun j => (x j).rows) hδ hH hD
    hYlim hY₂ (countersequence_lower_ge_one hY) (countersequence_lower_exponent hYlim)
    (fun j => (hx j).2.2.1) (fun j => (hx j).2.2.2.1) (fun j => (hx j).1) htotal
    (fun j => (hx j).2.2.2.2) hm

end CubicFirstMoment

end

end OAI
