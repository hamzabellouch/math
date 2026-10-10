import Mathlib

namespace OAI

universe uIota

open Filter Asymptotics
open scoped Topology

namespace Problem326

private lemma power_isLittleO_at_zero {a b : ℝ} (hab : a < b) :
    (fun h : ℝ => h ^ b) =o[𝓝[>] 0] (fun h => h ^ a) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact fun he => (ne_of_gt (Real.rpow_pos_of_pos hh a) he).elim
  · have hlim : Tendsto (fun h : ℝ => h ^ (b - a)) (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hp := hid.rpow tendsto_const_nhds (Or.inr (sub_pos.mpr hab))
      simpa only [Real.zero_rpow (ne_of_gt (sub_pos.mpr hab))] using hp
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact Real.rpow_sub hh b a

/-- Finitely many offsets with power decay strictly stronger than `h^t` share
one stronger decay exponent. The individual powers may vary with the label. -/
theorem exists_common_offset_decay {ι : Type uIota} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ → ℝ) (t : ℝ)
    (hc : ∀ i, ∃ β : ℝ, t < β ∧ c i =O[𝓝[>] 0] (fun h => h ^ β)) :
    ∃ η : ℝ, t < η ∧ ∀ i, c i =o[𝓝[>] 0] (fun h => h ^ η) := by
  classical
  choose β hβ hO using hc
  let μ := Finset.univ.inf' Finset.univ_nonempty β
  have htμ : t < μ := (Finset.lt_inf'_iff _).2 fun i _ => hβ i
  let η := (t + μ) / 2
  have htη : t < η := by dsimp [η]; linarith
  have hημ : η < μ := by dsimp [η]; linarith
  refine ⟨η, htη, fun i => ?_⟩
  have hηβ : η < β i := hημ.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  exact (hO i).trans_isLittleO (power_isLittleO_at_zero hηβ)

/-- A pre-existing localization radius can be shrunk so that all local offsets
are little-o of `h^(t+ρ)`, as required by the affine-family gluing argument. -/
theorem exists_radius_with_offset_decay {ι : Type uIota} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ → ℝ) (t ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hc : ∀ i, ∃ β : ℝ, t < β ∧ c i =O[𝓝[>] 0] (fun h => h ^ β)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧
      ∀ i, c i =o[𝓝[>] 0] (fun h => h ^ (t + ρ)) := by
  obtain ⟨η, htη, hη⟩ := exists_common_offset_decay c t hc
  let ρ := min (ρ₀ / 2) ((η - t) / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ₀' : ρ < ρ₀ := (min_le_left _ _).trans_lt (by linarith)
  have htρη : t + ρ < η := by
    have hle : ρ ≤ (η - t) / 2 := min_le_right _ _
    linarith
  refine ⟨ρ, hρ, hρ₀', fun i => ?_⟩
  exact (hη i).trans (power_isLittleO_at_zero htρη)

/-- The offsets produced by the type construction have the required big-O
bound even though the leading negative power prevents a little-o bound at
that same exponent. -/
theorem shifted_offset_isBigO {d : ℝ → ℝ} {β : ℝ}
    (hd : d =o[𝓝[>] 0] (fun h => h ^ β)) :
    (fun h => -(h ^ β) + d h) =O[𝓝[>] 0] (fun h => h ^ β) := by
  exact (isBigO_refl (fun h : ℝ => h ^ β) (𝓝[>] 0)).neg_left.add hd.isBigO

/-- Normalizing a constructed negative-shift offset by its leading power gives
limit `-1`; this is the exact sequential input used by fixed-minimum activity estimates. -/
theorem shifted_offset_normalized_limit {d : ℝ → ℝ} {β : ℝ}
    (hd : d =o[𝓝[>] 0] (fun h => h ^ β)) :
    Tendsto (fun h : ℝ => (-(h ^ β) + d h) / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by
  have hconst : Tendsto (fun _ : ℝ => (-1 : ℝ)) (𝓝[>] 0) (𝓝 (-1)) :=
    tendsto_const_nhds
  have hlim := hconst.add hd.tendsto_div_nhds_zero
  have hlim' : Tendsto (fun h : ℝ => -1 + d h / h ^ β)
      (𝓝[>] 0) (𝓝 (-1)) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : h ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh β)
  field_simp

end Problem326

end OAI
