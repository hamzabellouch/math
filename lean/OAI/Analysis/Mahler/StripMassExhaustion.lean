import OAI.Analysis.Mahler.StripRegularValues
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! An explicit regular-level exhaustion and
continuity from below for arbitrary nonnegative mass densities. -/
noncomputable section
namespace SymmetricMahler
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {I J : Type*} [Fintype I] [Fintype J]

def stripRegularLevel (k : ℕ) : ℝ := 1 - (1/2 : ℝ) * (1/2 : ℝ)^k

lemma stripRegularLevel_mem (k : ℕ) : stripRegularLevel k ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < (1/2 : ℝ)^k := pow_pos (by norm_num) _
  have hle : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> dsimp [stripRegularLevel] <;> nlinarith

lemma strictMono_stripRegularLevel : StrictMono stripRegularLevel := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp : 0 < (1/2 : ℝ)^k := pow_pos (by norm_num) _
  simp only [stripRegularLevel, pow_succ]
  nlinarith

lemma tendsto_stripRegularLevel : Tendsto stripRegularLevel atTop (𝓝 1) := by
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun k : ℕ => 1 - (1/2 : ℝ) * (1/2 : ℝ)^k) atTop (𝓝 1)
  simpa only [mul_zero, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (1/2 : ℝ))

/-- Explicit sequence for the actual tau, with no regular-value premise. -/
theorem strip_regular_value_sequence (A : J → I → ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m) :
    StrictMono stripRegularLevel ∧
    (∀ k, stripRegularLevel k ∈ Ioo (0 : ℝ) 1) ∧
    Tendsto stripRegularLevel atTop (𝓝 1) ∧
    ∀ k z, z ∈ stripDomain A → stripTau A m z = stripRegularLevel k →
      Function.Surjective (fderiv ℝ (stripTau A m) z) := by
  exact ⟨strictMono_stripRegularLevel, stripRegularLevel_mem, tendsto_stripRegularLevel,
    fun k _ hz he => stripTau_positive_regular A hA hm (stripRegularLevel_mem k).1 hz he⟩

lemma strip_regular_sublevels_monotone (A : J → I → ℝ) (m : ℕ) :
    Monotone (fun k => {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k}) := by
  intro a b hab z hz
  exact ⟨hz.1, hz.2.trans_le (strictMono_stripRegularLevel.monotone hab)⟩

lemma strip_regular_sublevels_union (A : J → I → ℝ) (m : ℕ) :
    (⋃ k, {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k}) =
      {z | z ∈ stripDomain A ∧ stripTau A m z < 1} := by
  ext z
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hz, ht⟩
    exact ⟨hz, ht.trans (stripRegularLevel_mem k).2⟩
  · rintro ⟨hz, ht⟩
    have h : ∀ᶠ k in atTop, stripTau A m z < stripRegularLevel k :=
      tendsto_stripRegularLevel.eventually (Ioi_mem_nhds ht)
    obtain ⟨k, hk⟩ := h.exists
    exact ⟨k, hz, hk⟩

/-- Continuity from below of nonnegative mass on the actual sublevels. No
finiteness of the mass over the limiting open set is imposed. -/
theorem strip_mass_exhaustion_iSup (A : J → I → ℝ) (m : ℕ)
    (μ : Measure ((I → ℝ) × (I → ℝ))) (ρ : ((I → ℝ) × (I → ℝ)) → ℝ≥0∞) :
    (∫⁻ z in {z | z ∈ stripDomain A ∧ stripTau A m z < 1}, ρ z ∂μ) =
      ⨆ k, ∫⁻ z in {z | z ∈ stripDomain A ∧ stripTau A m z < stripRegularLevel k}, ρ z ∂μ := by
  rw [← strip_regular_sublevels_union A m]
  exact setLIntegral_iUnion_of_directed ρ
    (strip_regular_sublevels_monotone A m).directed_le

end SymmetricMahler

end

end OAI
