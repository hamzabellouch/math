import OAI.Probability.InvariantIsing.Spectral.CompactTestsInMeasure

namespace OAI

/-! A vanishing metric perturbation preserves convergence in probability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem tendstoInMeasure_zero_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : ℕ → Ω → ℝ) (hg : TendstoInMeasure P g atTop (fun _ => 0))
    (hbound : ∀ n ω, |f n ω| ≤ |g n ω|) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendstoInMeasure_iff_dist.mp hg ε hε) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  simp only [mem_ofPred_eq,Real.dist_eq,sub_zero] at hω ⊢
  exact hω.trans (hbound n ω)

theorem tendstoInMeasure_div_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : TendstoInMeasure P f atTop (fun _ => 0))
    {c : ℝ} (hc : 0 < c) :
    TendstoInMeasure P (fun n ω => f n ω/c) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  convert (tendstoInMeasure_iff_dist.mp hf) (ε*c) (mul_pos hε hc) using 1
  funext n
  congr 1
  ext ω
  simp only [Real.dist_eq,sub_zero,abs_div,abs_of_pos hc]
  exact le_div_iff₀ hc

theorem tendstoInMeasure_of_dist_le {Ω Y : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Y]
    (P : Measure Ω) (f g : ℕ → Ω → Y) (h : ℕ → Ω → ℝ) (z : Ω → Y)
    (hg : TendstoInMeasure P g atTop z) (hh : TendstoInMeasure P h atTop (fun _ => 0))
    (hbound : ∀ n ω, dist (f n ω) (g n ω) ≤ h n ω) :
    TendstoInMeasure P f atTop z := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := half_pos hε
  have ht₁ := tendstoInMeasure_iff_dist.mp hh (ε/2) hhalf
  have ht₂ := tendstoInMeasure_iff_dist.mp hg (ε/2) hhalf
  have hb (n : ℕ) : {ω | ε ≤ dist (f n ω) (z ω)} ⊆
      {ω | ε/2 ≤ dist (h n ω) 0} ∪ {ω | ε/2 ≤ dist (g n ω) (z ω)} := by
    intro ω hω
    by_cases hh' : ε/2 ≤ dist (h n ω) 0
    · exact Or.inl hh'
    · right
      have hp : h n ω < ε/2 := lt_of_le_of_lt (by simpa only [Real.dist_eq,sub_zero] using le_abs_self (h n ω))
        (lt_of_not_ge hh')
      have hx := dist_triangle (f n ω) (g n ω) (z ω)
      have hb' := hbound n ω
      change ε ≤ dist (f n ω) (z ω) at hω
      change ε/2 ≤ dist (g n ω) (z ω)
      linarith
  have ht : Tendsto (fun n => P {ω | ε/2 ≤ dist (h n ω) 0}+
      P {ω | ε/2 ≤ dist (g n ω) (z ω)}) atTop (𝓝 0) := by
    simpa only [zero_add] using ht₁.add ht₂
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun n => (measure_mono (hb n)).trans (measure_union_le _ _))

end InvariantIsing

end

end OAI
