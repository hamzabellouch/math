import OAI.Geometry.RCD.Metric.DiagonalMeasuredApproximation
import OAI.Geometry.RCD.Metric.MeasurablePointedApproximation
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # The published measured-coordinate input on one common sequence of maps -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem LocalMeasuredCoordinateInput.common_approximations {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hinput : LocalMeasuredCoordinateInput hX) (hn : 2 ≤ n)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hcurv : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, -δ ≤ K*(r k)^2)
    (hflat : ∀ S η : ℝ, 0 < S → 0 < η → ∀ᶠ k in atTop,
      ∃ f : X → Euclidean n, IsPointedApproximation (p k) 0 (r k) S η f) :
    ∃ (ε : ℕ → ℝ) (V : ℕ → X → Euclidean n),
      (∀ k, 0 < ε k ∧ ε k ≤ 1) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ j : ℕ, ∀ᶠ k in atTop,
        IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k)
          ((j : ℝ)+1) (ε k) (V k) := by
  apply diagonal_measured_approximations
  intro m η hη
  have hi (i : Fin (m+1)) := hinput hn ((i.val : ℝ)+1) η (by positivity) hη
  choose δ hδ happly using hi
  let δ₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hδ₀ : 0 < δ₀ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hδ i)
  have hδle (i : Fin (m+1)) : δ₀ ≤ δ i := Finset.inf'_le _ (Finset.mem_univ i)
  filter_upwards [hcurv δ₀ hδ₀,
    hflat (2*((m : ℝ)+1)) (δ₀/15) (by positivity) (by positivity)] with k hk hf
  obtain ⟨f,hf⟩ := hf
  obtain ⟨V,hVm,hV⟩ := hf.exists_measurable (hr k) (by positivity) (by positivity)
  refine ⟨V,?_⟩
  intro j hj
  let i : Fin (m+1) := ⟨j,by omega⟩
  apply happly i (p k) (r k) (hr k) (le_trans (neg_le_neg (hδle i)) hk) V hVm
  have hrad : 2*((j : ℝ)+1) ≤ 2*((m : ℝ)+1) := by exact_mod_cast (show 2*(j+1)≤2*(m+1) by omega)
  have hres := hV.restrict_radius (hr k) (show 0 ≤ 2*((j : ℝ)+1) by positivity)
    hrad (show 0 ≤ 5*(δ₀/15) by positivity)
  have herr : 3*(5*(δ₀/15)) ≤ δ i := by linarith [hδle i]
  exact hres.mono_error herr

end RegularPointCoordinates

end

end OAI
