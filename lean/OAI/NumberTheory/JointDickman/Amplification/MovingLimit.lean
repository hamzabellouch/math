import OAI.NumberTheory.JointDickman.MainStatements
import OAI.NumberTheory.JointDickman.Amplification.MovingThresholds
import OAI.NumberTheory.JointDickman.Arithmetic.DickmanDistribution
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Instances.Rat

namespace OAI

/-!
# From rational fixed thresholds to the manuscript's main limit

Rational approximation compares fixed-scale thresholds with moving
thresholds and extends the counting limit to real endpoints.
-/

namespace JointDickman

open Filter
open scoped Topology

noncomputable def fixedDensity (a b : ℝ) (N : ℕ) : ℝ :=
  (empiricalCount (fixedScaleEvent a b N) N : ℝ) / N

/-- The joint limit for rational fixed-scale thresholds. -/
def RationalFixedScaleLaw : Prop :=
  ∀ c d : ℚ, 0 < c → c < 1 → 0 < d → d < 1 →
    Tendsto (fixedDensity c d) atTop (𝓝 (dickmanCDF c * dickmanCDF d))

private theorem tendsto_of_approximating_bounds
    {f : ℕ → ℝ} {g h : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} {L : ℝ}
    (hgl : ∀ k, Tendsto (g k) atTop (𝓝 (l k)))
    (hhu : ∀ k, Tendsto (h k) atTop (𝓝 (u k)))
    (hl : Tendsto l atTop (𝓝 L)) (hu : Tendsto u atTop (𝓝 L))
    (hgf : ∀ k, ∀ᶠ n in atTop, g k n ≤ f n)
    (hfh : ∀ k, ∀ᶠ n in atTop, f n ≤ h k n) :
    Tendsto f atTop (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hl.eventually (Ioi_mem_nhds ha)).exists
    filter_upwards [hgf k, (hgl k).eventually (Ioi_mem_nhds hk)] with n hn hn'
    exact hn'.trans_le hn
  · intro b hb
    obtain ⟨k, hk⟩ := (hu.eventually (Iio_mem_nhds hb)).exists
    filter_upwards [hfh k, (hhu k).eventually (Iio_mem_nhds hk)] with n hn hn'
    exact hn.trans_lt hn'

private theorem fixedDensity_le_moving_add {δ a b c d : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hca : c < a) (hdb : d < b) :
    ∀ᶠ N : ℕ in atTop,
      fixedDensity c d N - δ ≤ empiricalDensity (movingEvent a b) N := by
  filter_upwards [fixedCount_le_moving_add_prefix hδ ha hb hca hdb,
    eventually_ge_atTop 1] with N hN hNpos
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : (⌊δ * (N : ℝ)⌋₊ : ℝ) ≤ δ * N :=
    Nat.floor_le (mul_nonneg hδ.le hpos.le)
  have hcount : (empiricalCount (fixedScaleEvent c d N) N : ℝ) ≤
      empiricalCount (movingEvent a b) N + (⌊δ * (N : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hN
  have hdiv := (div_le_div_iff_of_pos_right hpos).mpr hcount
  have hfdiv : (⌊δ * (N : ℝ)⌋₊ : ℝ) / N ≤ δ :=
    (div_le_iff₀ hpos).mpr hfloor
  unfold fixedDensity empiricalDensity
  rw [add_div] at hdiv
  linarith

private theorem movingDensity_le_fixed {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) (N : ℕ) :
    empiricalDensity (movingEvent a b) N ≤ fixedDensity c d N := by
  unfold empiricalDensity fixedDensity
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast movingCount_le_fixed ha hb hac hbd N) (Nat.cast_nonneg _)

/-- The rational fixed-scale law implies the moving-threshold joint law
at every real counting endpoint. -/
theorem jointDickmanLaw_of_rational_fixedScale (hfixed : RationalFixedScaleLaw) :
    JointDickmanLaw := by
  intro a b ha ha1 hb hb1
  obtain ⟨cl, _, hcl, hcllim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
    Rat.cast_strictMono.monotone ha
  obtain ⟨dl, _, hdl, hdllim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
    Rat.cast_strictMono.monotone hb
  obtain ⟨cu, _, hcu, hculim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone ha1
  obtain ⟨du, _, hdu, hdulim⟩ := Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone hb1
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hgl : ∀ k, Tendsto (fun N => fixedDensity (cl k) (dl k) N - δ k)
      atTop (𝓝 (dickmanCDF (cl k) * dickmanCDF (dl k) - δ k)) := by
    intro k
    apply Filter.Tendsto.sub _ tendsto_const_nhds
    apply hfixed
    · exact_mod_cast (hcl k).1
    · exact_mod_cast ((hcl k).2.trans ha1)
    · exact_mod_cast (hdl k).1
    · exact_mod_cast ((hdl k).2.trans hb1)
  have hhu : ∀ k, Tendsto (fixedDensity (cu k) (du k)) atTop
      (𝓝 (dickmanCDF (cu k) * dickmanCDF (du k))) := by
    intro k
    apply hfixed
    · exact_mod_cast (ha.trans (hcu k).1)
    · exact_mod_cast (hcu k).2
    · exact_mod_cast (hb.trans (hdu k).1)
    · exact_mod_cast (hdu k).2
  have hl := ((dickmanCDF_continuous.tendsto a).comp hcllim).mul
    ((dickmanCDF_continuous.tendsto b).comp hdllim)
  have hu := ((dickmanCDF_continuous.tendsto a).comp hculim).mul
    ((dickmanCDF_continuous.tendsto b).comp hdulim)
  have hnat : Tendsto (empiricalDensity (movingEvent a b)) atTop
      (𝓝 (dickmanCDF a * dickmanCDF b)) := by
    apply tendsto_of_approximating_bounds hgl hhu (by simpa using hl.sub hδ) hu
    · intro k
      exact fixedDensity_le_moving_add (by positivity) ha.le hb.le (hcl k).2 (hdl k).2
    · intro k
      exact Filter.Eventually.of_forall
        (movingDensity_le_fixed ha.le hb.le (hcu k).1.le (hdu k).1.le)
  have hreal := realDensity_tendsto_of_nat hnat
  simpa [dickmanCDF, not_le.mpr ha, not_le.mpr hb] using hreal

end JointDickman

end OAI
