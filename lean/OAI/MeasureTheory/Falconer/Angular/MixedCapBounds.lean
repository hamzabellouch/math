import OAI.MeasureTheory.Falconer.Angular.SmoothCapPartition
import OAI.MeasureTheory.Falconer.Estimates.LaplacianBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OAI

/-!
# Mixed ambient derivatives of the actual cap bumps

The fixed compactly supported bump is rescaled by an affine similarity.
This proves a bound for its full Fréchet derivative, not only the derivative
along one selected chart curve. No new regularity assumption is used.
-/

namespace Falconer
open Set
open scoped ContDiff

private noncomputable def mixedUnitCapBump (d : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := one_lt_two

private theorem capBump_eq_mixedUnit {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (c : Sphere d) (x : Space d) :
    capBump δ hδ c x = mixedUnitCapBump d ((δ/2)⁻¹ • (x-(c : Space d))) := by
  have hr : δ/(δ/2) = 2 := by field_simp
  simp only [ContDiffBump.apply, capBump, mixedUnitCapBump, hr,
    div_one, inv_one, one_smul, sub_zero]

theorem iteratedFDeriv_affine_scale_bound {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : Space d) (s : ℝ) (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (fun y => f (s • (y-c))) x‖ ≤
      ‖iteratedFDeriv ℝ k f (s • (x-c))‖ * |s|^k := by
  let L : Space d →L[ℝ] Space d := s • ContinuousLinearMap.id ℝ (Space d)
  have he : (fun y => f (s • (y-c))) = fun y => (f ∘ L) (-c+y) := by
    funext y
    simp [L, sub_eq_add_neg, add_comm]
  rw [he, iteratedFDeriv_comp_add_left]
  rw [L.iteratedFDeriv_comp_right hf _ (by simp)]
  have hL : ‖L‖ ≤ |s| := by
    calc
      ‖L‖ = |s| * ‖ContinuousLinearMap.id ℝ (Space d)‖ := by
        simp only [L, norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg s)
      _ = |s| := mul_one _
  have h := (iteratedFDeriv ℝ k f (L (-c+x))).norm_compContinuousLinearMap_le
    (fun _ : Fin k => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  have hp : ‖L‖^k ≤ |s|^k := pow_le_pow_left₀ (norm_nonneg L) hL k
  simpa only [L, smul_apply, ContinuousLinearMap.id_apply,
    sub_eq_add_neg, add_comm] using mul_le_mul_of_nonneg_left hp
      (norm_nonneg (iteratedFDeriv ℝ k f (L (-c+x))))

theorem capBump_ambient_derivatives (d k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) (x : Space d),
      ‖iteratedFDeriv ℝ k (capBump δ hδ c) x‖ ≤ C*(δ⁻¹)^k := by
  obtain ⟨B,hB,hBb⟩ := (mixedUnitCapBump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (mixedUnitCapBump d).contDiff k
  refine ⟨B*2^k, mul_nonneg hB (by positivity), ?_⟩
  intro δ hδ c x
  have he : (capBump δ hδ c : Space d → ℝ) =
      fun y => mixedUnitCapBump d ((δ/2)⁻¹ • (y-(c : Space d))) := by
    funext y
    exact capBump_eq_mixedUnit δ hδ c y
  rw [he]
  have hh := iteratedFDeriv_affine_scale_bound (mixedUnitCapBump d).contDiff
    (c : Space d) ((δ/2)⁻¹) k x
  have hs : |(δ/2)⁻¹| = 2*δ⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (half_pos hδ))]
    field_simp
  apply hh.trans
  rw [hs, mul_pow]
  calc
    _ ≤ B * (2^k*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right (hBb k le_rfl _) (by positivity)
    _ = _ := by ring

theorem capBump_ambient_derivative_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (c : Sphere d) (x : Space d) (hfar : δ < ‖x-(c : Space d)‖) (k : ℕ) :
    iteratedFDeriv ℝ k (capBump δ hδ c) x = 0 := by
  have hn : x ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ k
  simpa using he.self_of_nhds

end Falconer

end OAI
