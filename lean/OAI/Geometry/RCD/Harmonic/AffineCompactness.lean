import OAI.Geometry.RCD.Sobolev.FiniteMomentConvergence
import Mathlib.Topology.Sequences

namespace OAI

/-! # The compactness contradiction for a uniform affine improvement

Convergence of the joint L² moments transfers a strict Euclidean affine
improvement to the approximating harmonic functions.
-/

open Filter
open scoped InnerProductSpace Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- Target, constant and coordinate functions, in that order. -/
def affineMomentFamily {H : Type*} (n : ℕ) (f one : H) (u : Fin n → H) :
    Option (Option (Fin n)) → H
  | none => f
  | some none => one
  | some (some i) => u i

def affineErrorCoefficients {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    Option (Option (Fin n)) → ℝ
  | none => 1
  | some none => -c
  | some (some i) => -v i

theorem affineMomentFamily_sum {H : Type*} [AddCommGroup H] [Module ℝ H]
    {n : ℕ} (f one : H) (u : Fin n → H) (c : ℝ) (v : Fin n → ℝ) :
    (∑ i, affineErrorCoefficients c v i • affineMomentFamily n f one u i) =
      f - c • one - ∑ i, v i • u i := by
  simp only [Fintype.sum_option, affineErrorCoefficients, affineMomentFamily,
    one_smul, neg_smul, Finset.sum_neg_distrib]
  abel

/-- Strict improvement for the limiting model transfers to the same
coefficients in every sufficiently late actual function space. -/
theorem affine_error_tendsto_of_moments
    {n : ℕ} {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)]
    {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℝ Hlim]
    (f one : ∀ k, H k) (u : ∀ k, Fin n → H k)
    (flim onelim : Hlim) (ulim : Fin n → Hlim)
    (h : ∀ i j, Tendsto
      (fun k => ⟪affineMomentFamily n (f k) (one k) (u k) i,
        affineMomentFamily n (f k) (one k) (u k) j⟫_ℝ) atTop
      (𝓝 ⟪affineMomentFamily n flim onelim ulim i,
        affineMomentFamily n flim onelim ulim j⟫_ℝ))
    (c : ℝ) (v : Fin n → ℝ) :
    Tendsto (fun k => ‖f k - c • one k - ∑ i, v i • u k i‖) atTop
      (𝓝 ‖flim - c • onelim - ∑ i, v i • ulim i‖) := by
  simpa only [affineMomentFamily_sum] using
    norm_sum_smul_tendsto_of_inner_tendsto
      (fun k => affineMomentFamily n (f k) (one k) (u k))
      (affineMomentFamily n flim onelim ulim) h (affineErrorCoefficients c v)

/-- The uniform threshold follows by contradiction from subsequential
compactness of the finite moments and the strict Euclidean candidate bound.
The coefficient choices need not be bounded or continuous in the index. -/
theorem eventually_affine_fit_of_moment_compactness
    {n : ℕ} {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
    [∀ k, InnerProductSpace ℝ (H k)]
    {Hlim : Type*} [NormedAddCommGroup Hlim] [InnerProductSpace ℝ Hlim]
    (f one : ∀ k, H k) (u : ∀ k, Fin n → H k)
    {Models : Type*} (flim onelim : Models → Hlim) (ulim : Models → Fin n → Hlim)
    (hcompact : ∀ s : ℕ → ℕ, StrictMono s →
      ∃ (t : ℕ → ℕ), StrictMono t ∧ ∃ model : Models,
        ∀ i j, Tendsto
          (fun k => ⟪affineMomentFamily n (f (s (t k))) (one (s (t k))) (u (s (t k))) i,
            affineMomentFamily n (f (s (t k))) (one (s (t k))) (u (s (t k))) j⟫_ℝ) atTop
          (𝓝 ⟪affineMomentFamily n (flim model) (onelim model) (ulim model) i,
            affineMomentFamily n (flim model) (onelim model) (ulim model) j⟫_ℝ))
    {η : ℝ}
    (hmodel : ∀ model : Models, ∃ (c : ℝ) (v : Fin n → ℝ),
      ‖flim model - c • onelim model - ∑ i, v i • ulim model i‖ < η) :
    ∀ᶠ k in atTop, ∃ (c : ℝ) (v : Fin n → ℝ),
      ‖f k - c • one k - ∑ i, v i • u k i‖ < η := by
  by_contra hbad
  have hb : ∃ᶠ k in atTop, ¬ ∃ (c : ℝ) (v : Fin n → ℝ),
      ‖f k - c • one k - ∑ i, v i • u k i‖ < η := by
    simpa only [Filter.Frequently, not_not] using hbad
  obtain ⟨s, hs, hfail⟩ := extraction_of_frequently_atTop hb
  obtain ⟨t, _ht, model, hlimit⟩ := hcompact s hs
  obtain ⟨c, v, hcv⟩ := hmodel model
  have he := (affine_error_tendsto_of_moments
    (fun k => f (s (t k))) (fun k => one (s (t k))) (fun k => u (s (t k)))
    (flim model) (onelim model) (ulim model) hlimit c v).eventually (gt_mem_nhds hcv)
  obtain ⟨k, hk⟩ := he.exists
  exact hfail (t k) ⟨c, v, hk⟩

end RegularPointCoordinates

end

end OAI
