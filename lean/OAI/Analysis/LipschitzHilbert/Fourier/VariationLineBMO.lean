import OAI.Analysis.LipschitzHilbert.Estimates.VariationMeanOscillation
import OAI.Analysis.LipschitzHilbert.Estimates.VariationContinuous
import OAI.Analysis.LipschitzHilbert.Estimates.ContinuousBMOMoments
import OAI.Analysis.LipschitzHilbert.Estimates.SquareMean

namespace OAI

/-! Applying the interval John--Nirenberg theorem to a finite packet
variation, using the actual short/long decomposition on each cell. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_integrable_cell (g : FiniteLineGrid) {f : ℝ → ℝ}
    (hf : Continuous f) (level i : ℕ) : IntegrableOn f (g.cell level i) := by
  unfold cell
  exact hf.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem variation_full_mean_oscillation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : FiniteLineGrid) (F : ℕ → ℝ → E) (S L : ℕ → ℕ → ℕ → ℝ → E) (N : ℕ)
    (hS : ∀ level i n, Continuous (S level i n))
    (hL : ∀ level i n, Continuous (L level i n))
    (hdecomp : ∀ level i n x, F n x = S level i n x + L level i n x)
    {K C : ℝ} (hK : 0 < K)
    (hshort : ∀ level i, i < g.branching ^ level →
      (∫ x in g.cell level i, (cubicVariation (fun n => S level i n x) N) ^ 2) ≤
        K ^ 2 * g.meshWidth level)
    (hlong : ∀ level i, i < g.branching ^ level → ∀ x ∈ g.cell level i, ∀ y ∈ g.cell level i,
      cubicVariation (fun n => L level i n x - L level i n y) N ≤ C) :
    g.HasFullMeanOscillationBound (fun x => cubicVariation (fun n => F n x) N) (2 * K + C) := by
  intro level i hi
  have hscont := continuous_cubicVariation (S level i) (hS level i) N
  have hlcont := continuous_cubicVariation (L level i) (hL level i) N
  have hfcont := continuous_cubicVariation (fun n x => S level i n x + L level i n x)
    (fun n => (hS level i n).add (hL level i n)) N
  have hs := g.continuous_integrable_cell hscont level i
  have hl := g.continuous_integrable_cell hlcont level i
  have hf := g.continuous_integrable_cell hfcont level i
  have hs2 := g.continuous_integrable_cell (hscont.pow 2) level i
  have hmean := integral_le_of_square_mean_bound (volume.restrict (g.cell level i)) _ hs hs2 hK
    (by simpa only [g.cell_mass] using hshort level i hi)
  have hosc : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      cubicVariation (fun n => L level i n x - L level i n y) N ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact hlong level i hi x hx y hy
  have h := variation_short_long_mean_oscillation (volume.restrict (g.cell level i))
    (S level i) (L level i) N hs hl hf (by rw [g.cell_mass]; exact g.meshWidth_pos level) hmean hosc
  simp_rw [← hdecomp level i] at h
  simpa only [g.cell_mass, g.cellMean_eq_integralAverage] using h

theorem variation_centered_line_moment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : FiniteLineGrid) (hb : 1 < g.branching)
    (F : ℕ → ℝ → E) (S L : ℕ → ℕ → ℕ → ℝ → E) (N : ℕ)
    (hS : ∀ level i n, Continuous (S level i n))
    (hL : ∀ level i n, Continuous (L level i n))
    (hdecomp : ∀ level i n x, F n x = S level i n x + L level i n x)
    {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hshort : ∀ level i, i < g.branching ^ level →
      (∫ x in g.cell level i, (cubicVariation (fun n => S level i n x) N) ^ 2) ≤
        K ^ 2 * g.meshWidth level)
    (hlong : ∀ level i, i < g.branching ^ level → ∀ x ∈ g.cell level i, ∀ y ∈ g.cell level i,
      cubicVariation (fun n => L level i n x - L level i n y) N ≤ C)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (|cubicVariation (fun n => F n x) N -
      integralAverage g.lineMeasure (fun y => cubicVariation (fun n => F n y) N)| ^ p)
      ∂g.lineMeasure) ≤
      7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * (2 * K + C)) /
        Real.log (3 / 2)) ^ p) * g.lineMeasure univ := by
  have hF (n : ℕ) : Continuous (F n) := by
    have heq : F n = fun x => S 0 0 n x + L 0 0 n x := by funext x; exact hdecomp 0 0 n x
    rw [heq]
    exact (hS 0 0 n).add (hL 0 0 n)
  have hc := continuous_cubicVariation F hF N
  have hi := g.continuous_integrable_cell hc 0 0
  rw [g.cell_zero] at hi
  exact g.continuous_mean_oscillation_moment hb _ hc.measurable hi
    (fun x _ => hc.continuousAt) (by positivity)
    (g.variation_full_mean_oscillation F S L N hS hL hdecomp hK hshort hlong) hp

end LipschitzHilbert.FiniteLineGrid

end

end OAI
