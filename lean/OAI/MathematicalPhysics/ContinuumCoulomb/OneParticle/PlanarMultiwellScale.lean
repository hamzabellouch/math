import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellGap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! A fixed planar excitation gap for exponentially many separated sites.
The scale is chosen once from the isolated-well gap, independently of the
number of sites and the input instance. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ContinuumCoulomb

theorem planarSiteDerivativeBound_tendsto :
    Tendsto planarSiteDerivativeBound atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.const_mul (6 : ℝ)).const_mul (Real.pi / 2)
  have h' := h.mul_const PlanarSobolev.cutoffGradBound
  change Tendsto (fun D : ℝ => (Real.pi / 2 * (6 / D)) * PlanarSobolev.cutoffGradBound)
    atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero, zero_mul] using h'

/-- One fixed separation threshold controls both the IMS loss and the sum
of cutoff tails for all site counts at most `exp(19 D / 320)`. -/
theorem exists_planar_multiwell_loss_threshold {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : ℝ, 8 ≤ R ∧ ∀ D : ℝ, R ≤ D → ∀ m : ℕ,
      (m : ℝ) ≤ Real.exp ((19/320 : ℝ) * D) →
      planarSiteDerivativeBound D ^ 2 +
        γ * m * planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)) ≤ γ / 2 := by
  have hexp : Tendsto (fun D : ℝ => Real.exp (-(19/320 : ℝ) * D)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 19/320))
  have hlim : Tendsto (fun D : ℝ => planarSiteDerivativeBound D ^ 2 +
      γ * planarSiteTailConstant * Real.exp (-(19/320 : ℝ) * D)) atTop (𝓝 0) := by
    simpa using (planarSiteDerivativeBound_tendsto.pow 2).add
      (hexp.const_mul (γ * planarSiteTailConstant))
  have hevent : ∀ᶠ D : ℝ in atTop, planarSiteDerivativeBound D ^ 2 +
      γ * planarSiteTailConstant * Real.exp (-(19/320 : ℝ) * D) < γ / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 8 R, le_max_left _ _, fun D hD m hm => ?_⟩
  have htail : γ * m * planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)) ≤
      γ * planarSiteTailConstant * Real.exp (-(19/320 : ℝ) * D) := by
    have hC : 0 ≤ γ * planarSiteTailConstant :=
      mul_nonneg hγ.le planarSiteTailConstant_nonnegative
    calc
      _ = (γ * planarSiteTailConstant) *
        ((m : ℝ) * Real.exp (-(19/20 : ℝ) * (D/8))) := by ring
      _ ≤ (γ * planarSiteTailConstant) *
        (Real.exp ((19/320 : ℝ) * D) * Real.exp (-(19/20 : ℝ) * (D/8))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) hC
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hh := (hR D ((le_max_right _ _).trans hD)).le
  linarith


/-- A single polynomial exponent meets the fixed separation cutoff and
supports every polynomial site count for every input size at least two. -/
theorem exists_uniform_multiwell_scale (A : ℕ) (R : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      R ≤ c * ((k : ℝ) * Real.log N) ∧
      N ^ A ≤ Real.exp ((19/320 : ℝ) * (c * ((k : ℝ) * Real.log N))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < (19/320 : ℝ) * c := mul_pos (by norm_num) hc
  obtain ⟨k, hk⟩ := exists_nat_gt
    (max 0 (max (R / (c * Real.log 2)) ((A : ℝ) / ((19/320 : ℝ) * c))))
  have hk0 : (0 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkR : R / (c * Real.log 2) ≤ k :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hk.le
  have hkA : (A : ℝ) / ((19/320 : ℝ) * c) ≤ k :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hk.le
  have hR := (div_le_iff₀ (mul_pos hc hlog)).mp hkR
  have hA := (div_le_iff₀ hp).mp hkA
  refine ⟨k, by exact_mod_cast hk0, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hln : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hln0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  constructor
  · calc
      R ≤ c * ((k : ℝ) * Real.log 2) := by nlinarith [hR]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hln hk0.le) hc.le
  · calc
      N ^ A = Real.exp ((A : ℝ) * Real.log N) := by
        rw [Real.exp_nat_mul, Real.exp_log hN0]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hA hln0])

/-- Conditional only on the published isolated-well gap. The full spatial
multiwell geometry and the aggregate tail error have already been bounded. -/
theorem planarWellSum_uniform_test_complement_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ R : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ 8 ≤ R ∧
      ∀ (m : ℕ) (D : ℝ), R ≤ D → (m : ℝ) ≤ Real.exp ((19/320 : ℝ) * D) →
      ∀ u : Fin m → PlanarPosition, (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      ∀ f : PlanarPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (∀ i, (∫ x, f x * normalizedPlanarMode (x-u i)) = 0) →
      ((-1/2 : ℝ) + γ/2) * (∫ x, f x^2) ≤ planarTestForm (planarWellSum u) f := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := planarWellSum_test_complement_bound hpublished
  obtain ⟨R, hR, hloss⟩ := exists_planar_multiwell_loss_threshold hγ
  refine ⟨γ, R, hγ, hsmall, hR, fun m D hD hm u hsep f hf hc ho => ?_⟩
  have hl := hloss D hD m hm
  have hcoef : (-1/2 : ℝ) + γ/2 ≤ (-1/2 : ℝ) + γ - planarSiteDerivativeBound D^2 -
      γ * m * planarSiteTailConstant * Real.exp (-(19/20 : ℝ) * (D/8)) := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef (integral_nonneg (fun x => sq_nonneg _))).trans
    (hgap m D (hR.trans hD) u hsep f hf hc ho)

/-- Reduction-scale version: a fixed exponent works uniformly for all
input sizes and every separated configuration with polynomially many sites. -/
theorem planarWellSum_polynomial_test_complement_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap)
    (A : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      ∀ m : ℕ, (m : ℝ) ≤ N ^ A → ∀ u : Fin m → PlanarPosition,
      (∀ i j, i ≠ j → c*((k : ℝ)*Real.log N) ≤ ‖u i-u j‖) →
      ∀ f : PlanarPosition → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      (∀ i, (∫ x, f x*normalizedPlanarMode (x-u i)) = 0) →
      ((-1/2 : ℝ)+γ) * (∫ x, f x^2) ≤ planarTestForm (planarWellSum u) f := by
  obtain ⟨γ, R, hγ, _, _, hgap⟩ := planarWellSum_uniform_test_complement_gap hpublished
  obtain ⟨k, hk, hscale⟩ := exists_uniform_multiwell_scale A R hc
  refine ⟨γ/2, by positivity, k, hk, fun N hN m hm u hsep f hf hcf ho => ?_⟩
  obtain ⟨hR, hcount⟩ := hscale N hN
  exact hgap m (c*((k : ℝ)*Real.log N)) hR (hm.trans hcount) u hsep f hf hcf ho

end ContinuumCoulomb

end

end OAI
