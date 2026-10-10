import OAI.Analysis.LipschitzHilbert.Trees.LineGridBMO
import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleGoodLambda

namespace OAI

/-! The concrete cellwise mean-oscillation bound implies the conditional
oscillation hypothesis used by the finite martingale stopping argument. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem integrated_oscillation_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {n : ℕ} (hn : n ≤ g.depth) {s : Set ℝ} (hs : MeasurableSet[g.filtration n] s) :
    (∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure) ≤
      A * g.lineMeasure.real s := by
  let G := fun x => |f x - g.average g.lineMeasure f n x|
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have hG : Integrable G g.lineMeasure := (hf.sub havg).abs
  have hb : ∀ᵐ x ∂g.lineMeasure, g.average g.lineMeasure G n x ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    let i := (g.index n x).val
    have hi : i < g.branching ^ n := g.index_lt_level hn x
    have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
    rw [g.average_eq_cell_mean G hG hn hi hxc]
    have heq : (∫ y in g.cell n i, G y) =
        ∫ y in g.cell n i, |f y - g.cellMean f n i| := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro y hy
      simp only [G, g.average_eq_cellMean f hf hn hi hy]
    rw [heq]
    exact (div_le_iff₀ (g.meshWidth_pos n)).mpr (hA n i hn hi)
  change (∫ x in s, G x ∂g.lineMeasure) ≤ _
  rw [← setIntegral_condExp (g.filtration.le n) hG hs]
  have h := integral_mono_ae (μ := g.lineMeasure.restrict s)
    integrable_condExp.integrableOn (integrable_const A)
    (ae_restrict_of_ae hb)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using h

theorem terminal_mean_oscillation (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {N : ℕ} (hN : N ≤ g.depth) :
    TerminalMeanOscillationBound (g.average g.lineMeasure f) g.filtration g.lineMeasure N A := by
  intro n hn s hs
  have hsm : MeasurableSet[g.filtration N] s := g.filtration.mono hn _ hs
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have heq : g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] =ᵐ[g.lineMeasure]
      (fun x => g.average g.lineMeasure f N x - g.average g.lineMeasure f n x) := by
    have hsub := condExp_sub hf havg (g.filtration N)
    have hmeas : StronglyMeasurable[g.filtration N] (g.average g.lineMeasure f n) :=
      (g.average_martingale g.lineMeasure f).stronglyMeasurable n |>.mono (g.filtration.mono hn)
    rw [condExp_of_stronglyMeasurable (g.filtration.le N) hmeas havg] at hsub
    exact hsub
  calc
    _ = ∫ x in s, |g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] x|
        ∂g.lineMeasure := by
      apply setIntegral_congr_ae (g.filtration.le n _ hs)
      filter_upwards [heq] with x hx _
      rw [hx]
    _ ≤ ∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure :=
      setIntegral_abs_condExp_le hsm _
    _ ≤ _ := g.integrated_oscillation_le f hf hA (hn.trans hN) hs

end LipschitzHilbert.FiniteLineGrid

end

end OAI
