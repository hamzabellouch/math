import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNearGroundCompactness

namespace OAI

/-! The actual planar well has a positive excitation gap once its zero-form
space is the line of the proved normalized ground mode. Compactness here is
proved directly, with no spectral or planar-gap input used. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instPlanarGapFromUniquenessMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instPlanarGapFromUniquenessBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instPlanarGapFromUniquenessMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

theorem normalized_gap_of_ground_uniqueness
    (hker : ∀ u : Sobolev, shiftedForm u.val = 0 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → u = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev, ‖u.val.1‖^2 = 1 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → γ ≤ shiftedForm u.val := by
  by_contra h
  push Not at h
  have hex (n : ℕ) : ∃ u : Sobolev, ‖u.val.1‖^2 = 1 ∧
      inner ℝ u.val.1 normalizedMode.val.1 = 0 ∧
        shiftedForm u.val < 1/((n:ℝ)+1) :=
    h (1/((n:ℝ)+1)) (by positivity)
  choose u hm ho hs using hex
  have ht : Tendsto (fun n => shiftedForm (u n).val) atTop (𝓝 0) :=
    squeeze_zero (fun n => shiftedForm_nonnegative (u n)) (fun n => (hs n).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmass (n : ℕ) : ‖(u n).val.1‖ ≤ 1 := by
    nlinarith [hm n,norm_nonneg (u n).val.1]
  have hbound (n : ℕ) : shiftedForm (u n).val ≤ 1 := by
    apply (hs n).le.trans
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨v,φ,hφ,hv⟩ := nearGround_subsequence u hmass hbound ht
  have hcv : Continuous (fun u : Sobolev => ‖u.val.1‖^2) :=
    (h1ToL2 (μ := volume) (E := PlanarPosition)).continuous.norm.pow 2
  have hmassv : ‖v.val.1‖^2 = 1 := by
    apply tendsto_nhds_unique (hcv.continuousAt.tendsto.comp hv)
    change Tendsto (fun n => ‖(u (φ n)).val.1‖^2) atTop (𝓝 1)
    simp_rw [hm]
    exact tendsto_const_nhds
  have hcs : Continuous (fun u : Sobolev => shiftedForm u.val) :=
    (form_continuous.comp continuous_subtype_val).add (continuous_const.mul hcv)
  have hzero : shiftedForm v.val = 0 :=
    tendsto_nhds_unique (hcs.continuousAt.tendsto.comp hv) (ht.comp hφ.tendsto_atTop)
  have hco : Continuous (fun u : Sobolev => inner ℝ u.val.1 normalizedMode.val.1) :=
    (h1ToL2 (μ := volume) (E := PlanarPosition)).continuous.inner continuous_const
  have hov : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
    apply tendsto_nhds_unique (hco.continuousAt.tendsto.comp hv)
    change Tendsto (fun n => inner ℝ (u (φ n)).val.1 normalizedMode.val.1) atTop (𝓝 0)
    simp_rw [ho]
    exact tendsto_const_nhds
  have hz := hker v hzero hov
  norm_num [hz] at hmassv

theorem shiftedForm_smul (c : ℝ) (u : Target) :
    shiftedForm (c • u) = c^2*shiftedForm u := by
  unfold shiftedForm
  rw [form_smul]
  change c^2*form u+(1/2:ℝ)*‖c • u.1‖^2 = _
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  ring

theorem planar_gap_of_ground_uniqueness
    (hker : ∀ u : Sobolev, shiftedForm u.val = 0 →
      inner ℝ u.val.1 normalizedMode.val.1 = 0 → u = 0) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u : Sobolev,
      inner ℝ u.val.1 normalizedMode.val.1 = 0 →
      ((-1/2:ℝ)+γ)*‖u.val.1‖^2 ≤ form u.val := by
  obtain ⟨γ,hγ,hgap⟩ := normalized_gap_of_ground_uniqueness hker
  refine ⟨γ,hγ,fun u ho => ?_⟩
  have h : γ*‖u.val.1‖^2 ≤ shiftedForm u.val := by
    by_cases hn : ‖u.val.1‖ = 0
    · simpa only [hn,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using shiftedForm_nonnegative u
    let v : Sobolev := ‖u.val.1‖⁻¹ • u
    have hm : ‖v.val.1‖^2 = 1 := by
      change ‖‖u.val.1‖⁻¹ • u.val.1‖^2 = 1
      rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hn)
    have hov : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
      change inner ℝ (‖u.val.1‖⁻¹ • u.val.1) normalizedMode.val.1 = 0
      rw [real_inner_smul_left,ho,mul_zero]
    calc
      _ ≤ shiftedForm v.val*‖u.val.1‖^2 :=
        mul_le_mul_of_nonneg_right (hgap v hm hov) (sq_nonneg _)
      _ = shiftedForm u.val := by
        change shiftedForm (‖u.val.1‖⁻¹ • u.val)*‖u.val.1‖^2 = _
        rw [shiftedForm_smul]
        field_simp [hn]
  unfold shiftedForm at h
  linarith

end ContinuumCoulomb.PlanarSobolev

end

end OAI
