import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def directedBallDeviation {d : ℕ} (s t : Set (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sSup ((fun x => infDist x t) '' (ball a r ∩ s))

def bilateralPlaneError {d : ℕ} (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ)
    (S : AffineSubspace ℝ (Ambient d)) : ℝ :=
  (directedBallDeviation μ.support (S : Set (Ambient d)) a r +
    directedBallDeviation (S : Set (Ambient d)) μ.support a r) / r

def bilateralBeta {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) : ℝ :=
  sInf {t : ℝ | ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧ t = bilateralPlaneError μ a r S}

theorem directedBallDeviation_bddAbove {d : ℕ} (s t : Set (Ambient d)) (ht : t.Nonempty)
    (a : Ambient d) (r : ℝ) : BddAbove ((fun x => infDist x t) '' (ball a r ∩ s)) := by
  obtain ⟨y, hy⟩ := ht
  refine ⟨r + dist a y, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have hx' : dist x a ≤ r := hx.1.le
  exact (infDist_le_dist_of_mem hy).trans ((dist_triangle x a y).trans (by linarith))

theorem directedBallDeviation_nonneg {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r : ℝ) : 0 ≤ directedBallDeviation s t a r := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact infDist_nonneg

theorem directedBallDeviation_le {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r η : ℝ) (hη : 0 ≤ η)
    (hpoint : ∀ x ∈ ball a r, x ∈ s → infDist x t ≤ η) :
    directedBallDeviation s t a r ≤ η := by
  apply Real.sSup_le _ hη
  rintro v ⟨x, hx, rfl⟩
  exact hpoint x hx.1 hx.2

theorem bilateralPlaneError_nonneg {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) (S : AffineSubspace ℝ (Ambient d)) :
    0 ≤ bilateralPlaneError μ a r S :=
  div_nonneg (add_nonneg (directedBallDeviation_nonneg _ _ a r)
    (directedBallDeviation_nonneg _ _ a r)) hr

theorem bilateralBeta_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ bilateralBeta n μ a r := by
  apply Real.sInf_nonneg
  rintro v ⟨S, _, rfl⟩
  exact bilateralPlaneError_nonneg μ a r hr S

theorem bilateralBeta_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    bilateralBeta n μ a r ≤ bilateralPlaneError μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨T, _, rfl⟩
    exact bilateralPlaneError_nonneg μ a r hr T
  · exact ⟨S, hS, rfl⟩

theorem bilateralBeta_lt_of_support_tubes {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a r, x ∈ μ.support → infDist x (S : Set (Ambient d)) < ε * r / 4)
    (hreverse : ∀ x ∈ ball a r, x ∈ S → infDist x μ.support < ε * r / 4) :
    bilateralBeta n μ a r < ε := by
  apply (bilateralBeta_le_planeError n μ a r hr.le S hS).trans_lt
  have h1 := directedBallDeviation_le μ.support (S : Set (Ambient d)) a r (ε * r / 4)
    (by positivity) (fun x hx hs => (hforward x hx hs).le)
  have h2 := directedBallDeviation_le (S : Set (Ambient d)) μ.support a r (ε * r / 4)
    (by positivity) (fun x hx hs => (hreverse x hx hs).le)
  apply (div_lt_iff₀ hr).mpr
  nlinarith

end

end RieszRectifiability

end OAI
