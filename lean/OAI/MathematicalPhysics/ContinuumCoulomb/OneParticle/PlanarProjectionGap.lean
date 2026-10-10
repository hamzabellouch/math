import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSpectralInput
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarNormalized

namespace OAI

/-! The isolated-well orthogonal gap implies the actual rank-one projection
bound on every vector in the closed Sobolev graph. The ground cross term
vanishes by the proved variational minimum, without a further spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb.PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance : BorelSpace PlanarPosition := ⟨rfl⟩
local instance : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

def shiftedForm (u : Target) : ℝ := form u + (1/2 : ℝ) * ‖u.1‖ ^ 2

def shiftedCross (u g : Target) : ℝ :=
  inner ℝ u.2 g.2 + inner ℝ u.1 (wellMultiplier g.1) +
    inner ℝ g.1 (wellMultiplier u.1) + inner ℝ u.1 g.1

theorem shiftedForm_add_smul (u g : Target) (t : ℝ) :
    shiftedForm (u + t • g) = shiftedForm u + t * shiftedCross u g + t^2 * shiftedForm g := by
  change (1/2 : ℝ) * ‖u.2 + t • g.2‖ ^ 2 +
      inner ℝ (u.1 + t • g.1) (wellMultiplier (u.1 + t • g.1)) +
      (1/2 : ℝ) * ‖u.1 + t • g.1‖ ^ 2 = _
  rw [norm_add_sq_real, norm_add_sq_real, map_add, map_smul]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  unfold shiftedForm form shiftedCross
  ring

theorem shiftedForm_nonnegative (u : Sobolev) : 0 ≤ shiftedForm u.val := by
  have h := form_lower u
  unfold shiftedForm
  linarith

theorem shiftedForm_normalizedMode : shiftedForm normalizedMode.val = 0 := by
  rw [shiftedForm, normalizedMode_energy, normalizedMode_mass]
  norm_num

private theorem affine_nonnegative_slope_zero (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ a + t*b) : b = 0 := by
  by_contra hb
  have ht := h (-(a+1)/b)
  have he : a + (-(a+1)/b)*b = -1 := by field_simp [hb]; ring
  rw [he] at ht
  linarith

theorem shiftedCross_normalizedMode (u : Sobolev) : shiftedCross u.val normalizedMode.val = 0 := by
  apply affine_nonnegative_slope_zero (shiftedForm u.val)
  intro t
  have h := shiftedForm_nonnegative (u + t • normalizedMode)
  change 0 ≤ shiftedForm (u.val + t • normalizedMode.val) at h
  rw [shiftedForm_add_smul, shiftedForm_normalizedMode, mul_zero, add_zero] at h
  exact h

theorem shiftedForm_remove_ground (u : Sobolev) (t : ℝ) :
    shiftedForm (u - t • normalizedMode).val = shiftedForm u.val := by
  change shiftedForm (u.val - t • normalizedMode.val) = _
  rw [sub_eq_add_neg, ← neg_smul, shiftedForm_add_smul,
    shiftedCross_normalizedMode, shiftedForm_normalizedMode]
  ring

/-- The precise rank-one closed-form bound needed in the multiwell IMS
argument, derived from the already cited isolated spectral input. -/
theorem manufacturedPlanarWell_projection_gap (hpublished : ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ u : Sobolev,
      ((-1/2 : ℝ) + γ) * ‖u.val.1‖^2 -
        γ * (inner ℝ u.val.1 normalizedMode.val.1)^2 ≤ form u.val := by
  obtain ⟨γ₀, hγ₀, hgap₀⟩ := hpublished
  let γ := min γ₀ (1/4 : ℝ)
  have hγ : 0 < γ := lt_min hγ₀ (by norm_num)
  have hgap (u : Sobolev) (hu : inner ℝ u.val.1 normalizedMode.val.1 = 0) :
      ((-1/2 : ℝ) + γ) * ‖u.val.1‖^2 ≤ form u.val := by
    have hcoef : (-1/2 : ℝ) + γ ≤ -1/2 + γ₀ := by
      dsimp only [γ]
      linarith [min_le_left γ₀ (1/4 : ℝ)]
    exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖u.val.1‖)).trans (hgap₀ u hu)
  refine ⟨γ, hγ, min_le_right _ _, fun u => ?_⟩
  let c := inner ℝ u.val.1 normalizedMode.val.1
  let v : Sobolev := u - c • normalizedMode
  have hv : inner ℝ v.val.1 normalizedMode.val.1 = 0 := by
    change inner ℝ (u.val.1 - c • normalizedMode.val.1) normalizedMode.val.1 = 0
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, normalizedMode_mass]
    dsimp only [c]
    ring
  have hn : ‖v.val.1‖^2 = ‖u.val.1‖^2 - c^2 := by
    change ‖u.val.1 - c • normalizedMode.val.1‖^2 = _
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, normalizedMode_mass]
    dsimp only [c]
    ring
  have hshift : shiftedForm v.val = shiftedForm u.val := shiftedForm_remove_ground u c
  have hg := hgap v hv
  unfold shiftedForm at hshift
  rw [hn] at hg hshift
  dsimp only [c] at hg hshift
  linarith

theorem normalizedMode_ae : normalizedMode.val.1 =ᵐ[volume] normalizedPlanarMode := by
  have hs := Lp.coeFn_smul (Real.sqrt (‖mode.val.1‖^2))⁻¹ mode.val.1
  filter_upwards [hs, mode_memLp.coeFn_toLp] with x hx hm
  change (((Real.sqrt (‖mode.val.1‖^2))⁻¹ • mode.val.1 : Lp ℝ 2 volume) x) = _
  rw [hx]
  change (Real.sqrt (‖mode.val.1‖^2))⁻¹ * mode.val.1 x = _
  change mode.val.1 x = planarResolventMode x at hm
  rw [hm, mode_mass, normalizedPlanarMode_eq_const_mul]
  rfl

theorem graph_normalizedMode_inner (u : Test) :
    inner ℝ (graph (μ := volume) u).1 normalizedMode.val.1 =
      ∫ x, u.val x * normalizedPlanarMode x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
    normalizedMode_ae] with x hx hg
  change toL2 (μ := volume) u x = u.val x at hx
  change inner ℝ (toL2 (μ := volume) u x) (normalizedMode.val.1 x) = _
  rw [hx, hg, RCLike.inner_apply, conj_trivial]
  ring

/-- The rank-one inequality is attached to the actual normalized planar
function and actual test-function integrals used by localization. -/
theorem manufacturedPlanarWell_test_projection_gap (hpublished : ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ u : Test,
      ((-1/2 : ℝ) + γ) * (∫ x, u.val x ^ 2) -
        γ * (∫ x, u.val x * normalizedPlanarMode x)^2 ≤
          planarTestForm manufacturedPlanarWell u.val := by
  obtain ⟨γ, hγ, hsmall, hgap⟩ := manufacturedPlanarWell_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun u => ?_⟩
  let v : Sobolev := ⟨graph (μ := volume) u, subset_closure ⟨u, rfl⟩⟩
  have hg := hgap v
  change ((-1/2 : ℝ) + γ) * ‖(graph (μ := volume) u).1‖^2 -
      γ * (inner ℝ (graph (μ := volume) u).1 normalizedMode.val.1)^2 ≤
        form (graph (μ := volume) u) at hg
  rw [graph_mass, graph_normalizedMode_inner, graph_form] at hg
  exact hg

end ContinuumCoulomb.PlanarSobolev

namespace ContinuumCoulomb

/-- Export the isolated projection inequality with the ambient Euclidean
measure used by the actual continuum construction. -/
theorem manufacturedPlanarWell_actual_projection_gap
    (hpublished : PlanarSobolev.ManufacturedPlanarGroundGap) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1/4 ∧ ∀ f : PlanarPosition → ℝ,
      ContDiff ℝ 1 f → HasCompactSupport f →
      ((-1/2 : ℝ) + γ) * (∫ x, f x ^ 2) -
        γ * (∫ x, f x * normalizedPlanarMode x)^2 ≤
          planarTestForm manufacturedPlanarWell f := by
  let : MeasurableSpace PlanarPosition := borel PlanarPosition
  let : BorelSpace PlanarPosition := ⟨rfl⟩
  let : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace
  obtain ⟨γ, hγ, hsmall, hgap⟩ := PlanarSobolev.manufacturedPlanarWell_test_projection_gap hpublished
  refine ⟨γ, hγ, hsmall, fun f hf hc => ?_⟩
  have h := hgap ⟨f, hf, hc⟩
  have he (g : PlanarPosition → ℝ) := PlanarSobolev.planar_integral_change_borel
    (borel PlanarPosition) ⟨rfl⟩ g
  rw [he (fun x => f x ^ 2), he (fun x => f x * normalizedPlanarMode x)] at h
  exact h

end ContinuumCoulomb

end

end OAI
