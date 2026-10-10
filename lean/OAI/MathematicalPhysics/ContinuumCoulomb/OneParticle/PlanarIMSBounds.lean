import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarSiteCutoffs

namespace OAI

/-! Quantitative IMS lower bounds, attached to the actual separated-site
partition. The error constant depends on one fixed bump and D, not on the
number of sites. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem planar_localization_cost_integrable {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (u : PlanarPosition → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    (e : PlanarPosition) :
    Integrable (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := by
  have hs : HasCompactSupport (fun x => u x ^ 2) :=
    hc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have hm : HasCompactSupport (fun x => (∑ i, planarPartial (θ i) e x ^ 2) * u x ^ 2) := hs.mul_left
  have hd : Continuous (fun x => ∑ i, planarPartial (θ i) e x ^ 2) :=
    continuous_finsetSum _ (fun i _ => (planarPartial_continuous (hθ i) e).pow 2)
  exact (hd.mul (hu.pow 2)).integrable_of_hasCompactSupport hm

theorem planar_IMS_cost_bound {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (u : PlanarPosition → ℝ) (hu : Continuous u) (hc : HasCompactSupport u)
    {C : ℝ} (hbound : ∀ x, (∑ a : Fin 2, ∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) ≤ C) :
    (∑ a : Fin 2, ∫ x, (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2) ≤
      C * ∫ x, u x ^ 2 := by
  have hi (a : Fin 2) := planar_localization_cost_integrable θ hθ u hu hc (planarAxis a)
  have hs : Integrable (fun x => ∑ a : Fin 2,
      (∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) * u x ^ 2) :=
    integrable_finsetSum _ (fun a _ => hi a)
  have hm : Integrable (fun x => C * u x ^ 2) :=
    planar_potential_test_integrable (fun _ => C) u continuous_const hu hc
  rw [← integral_finsetSum _ (fun a _ => hi a), ← integral_const_mul]
  apply integral_mono hs hm
  intro x
  dsimp only
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hbound x) (sq_nonneg _)

theorem planar_IMS_lower {ι : Type*} [Fintype ι]
    (θ : ι → PlanarPosition → ℝ) (hθ : ∀ i, ContDiff ℝ 1 (θ i))
    (hpart : ∀ x, ∑ i, θ i x ^ 2 = 1)
    (W u : PlanarPosition → ℝ) (hW : Continuous W)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    {C : ℝ} (hbound : ∀ x, (∑ a : Fin 2, ∑ i, planarPartial (θ i) (planarAxis a) x ^ 2) ≤ C) :
    (∑ i, planarTestForm W (fun x => θ i x * u x)) - (C/2) * (∫ x, u x ^ 2) ≤
      planarTestForm W u := by
  have he := planar_IMS θ hθ hpart W u hW hu hc
  have hb := planar_IMS_cost_bound θ hθ u hu.continuous hc hbound
  linarith

/-- An actual multiwell localization estimate with fixed bump constant and
quadratic inverse-separation error. -/
theorem planarSitePartition_IMS_lower {ι : Type*} [Fintype ι] {D : ℝ} (hD : 0 < D)
    (u : ι → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (W f : PlanarPosition → ℝ) (hW : Continuous W)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∑ i, planarTestForm W (fun x => planarSitePartition D u i x * f x)) -
      planarSiteDerivativeBound D ^ 2 * (∫ x, f x ^ 2) ≤ planarTestForm W f := by
  have h := planar_IMS_lower (planarSitePartition D u) (planarSitePartition_C1 D u)
    (planarSitePartition_square_sum hD u hsep) W f hW hf hc
    (planarSitePartition_gradient_bound hD u hsep)
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
