import Mathlib
import OAI.Probability.LogConcave.Analysis.Operator

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory Filter
open scoped Topology NNReal

theorem measure_eq_of_smooth_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : E → ℝ),ContDiff ℝ 1 f → (∃ L : ℝ≥0,LipschitzWith L f) →
      (∃ B : ℝ,∀ x,‖f x‖≤B) → (∫ x,f x ∂μ)=(∫ x,f x ∂ν)) : μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have huf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  obtain ⟨B,hB⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hε (n : ℕ) : 0<1/((n:ℝ)+1) := by positivity
  choose g hgc hgd using fun n : ℕ => huf.exists_contDiff_dist_le (hε n)
  have hge (n : ℕ) : 1/((n:ℝ)+1)≤1 := by
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hgb : ∀ n x,‖g n x‖≤B+1 := by
    intro n x
    have hd := (hgd n x).le.trans (hge n)
    rw [dist_eq_norm] at hd
    exact (norm_le_norm_add_norm_sub' (g n x) (f x)).trans (add_le_add (hB x) hd)
  have hgt (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hgd n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let u : ℕ → E → ℝ := fun n => PoincareCutoff.truncation (g n) n
  have huc (n : ℕ) : ContDiff ℝ 1 (u n) :=
    PoincareCutoff.truncation_smooth ((hgc n).of_le (by simp)) n
  have huk (n : ℕ) : HasCompactSupport (u n) := PoincareCutoff.truncation_compact _ _
  have hub : ∀ n x,‖u n x‖≤B+1 := by
    intro n x
    exact (PoincareCutoff.truncation_abs (g n) n x).trans (hgb n x)
  have huL (n : ℕ) : ∃ L : ℝ≥0,LipschitzWith L (u n) := by
    obtain ⟨C,hC⟩ := ((huk n).fderiv ℝ).exists_bound_of_continuous
      ((huc n).continuous_fderiv (by norm_num))
    let L : ℝ≥0 := ⟨C,(norm_nonneg _).trans (hC 0)⟩
    exact ⟨L,lipschitzWith_of_nnnorm_fderiv_le ((huc n).differentiable (by norm_num)) hC⟩
  have hut (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (f x)) := by
    simpa only [u,PoincareCutoff.truncation,one_mul] using (PoincareCutoff.cutoff_tendsto x).mul (hgt x)
  have hlim (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫ x,u n x ∂η) atTop (𝓝 (∫ x,f x ∂η)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => B+1)
      (fun n => (huc n).continuous.aestronglyMeasurable) (integrable_const (B+1))
      (fun n => Eventually.of_forall (hub n)) (Eventually.of_forall hut)
  have he : (fun n => ∫ x,u n x ∂μ)=(fun n => ∫ x,u n x ∂ν) :=
    funext fun n => h (u n) (huc n) (huL n) ⟨B+1,hub n⟩
  exact tendsto_nhds_unique (hlim μ) (he ▸ hlim ν)
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
