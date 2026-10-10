import OAI.Probability.InvariantIsing.Pressure.RandomSpectralBound
import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! Turning a scalar edge-excess limit into the selected spectral hypotheses. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma selected_no_outliers_of_excess (N : ℕ → ℕ) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (a b : ℝ) (he : Tendsto (fun k => spectralExcess (eig k) a b) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i, a-ε ≤ eig k i ∧ eig k i ≤ b+ε := by
  intro ε hε
  filter_upwards [he.eventually (Iio_mem_nhds hε)] with k hk i
  have hb := spectralExcess_bounds (eig k) a b i
  constructor <;> linarith

lemma selected_spectralRadius_bounded (s : ℕ → ℕ)
    (eig : (k : ℕ) → Fin (s k+1) → ℝ) (a b : ℝ)
    (he : Tendsto (fun k => spectralExcess (eig k) a b) atTop (𝓝 0)) :
    ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig k) ≤ K := by
  refine ⟨max |a| |b|+1,?_⟩
  filter_upwards [selected_no_outliers_of_excess (fun k => s k+1) eig a b he 1 zero_lt_one]
    with k hk
  apply (spectralRadius_le_iff _ _).mpr
  intro i
  apply abs_le.mpr
  have ha := neg_abs_le a
  have hb := le_abs_self b
  have hma := le_max_left |a| |b|
  have hmb := le_max_right |a| |b|
  constructor <;> linarith [(hk i).1,(hk i).2]

end InvariantIsing

end

end OAI
