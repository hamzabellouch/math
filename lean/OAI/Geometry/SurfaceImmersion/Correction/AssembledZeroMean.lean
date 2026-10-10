import OAI.Geometry.SurfaceImmersion.Correction.AssembledCombinedMean
import OAI.Geometry.SurfaceImmersion.Correction.CombinedZeroMean

namespace OAI

/-! The finite assembled mean correction is the actual quadratic zero-phase
error once the positive phase decomposition is supplied. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates FiniteMean
variable {s r ρ R₀ : ℝ} {reference : Base → Tensor} {n L : ℕ}

namespace CombinedMeanChart

def leading (c : CombinedMeanChart s r ρ R₀ reference n L) (A : Base → Tensor) : Base → Tensor :=
  c.source.indicator (chartLeadingTensor (RootMean.phaseAmplitude c.cutoff
    (PhaseMean.coefficient c.coefficient c.inverse A)) c.chart)

def quadraticMean (c : CombinedMeanChart s r ρ R₀ reference n L) (hρ : 0 < ρ)
    (δ τ ε : ℝ) (R : c.Operator) (q : ℕ) (A : Base → Tensor) : Base → Tensor :=
  c.source.indicator (localQuadraticMean c.localBounds hρ c.support_target c.polynomial c.jetMap δ τ ε R q A)

lemma mean_smooth (c : CombinedMeanChart s r ρ R₀ reference n L) (hρ : 0 < ρ)
    (δ τ ε : ℝ) (R : c.Operator) (q : ℕ) (A : Base → Tensor) :
    ContDiff ℝ ∞ (c.mean hρ δ τ ε R q A) :=
  extendedCombinedMean_smooth c.localBounds hρ c.support_target c.outer_closed c.outer_source c.support_chart
    c.jetSource_open c.coefficientDomain_open c.coefficients_smooth c.jetMap_smooth
    (fun _ hx => c.compactJets_domain (c.jetMap_range hx)) c.support_jetSource δ τ ε R q A

lemma quadraticMean_eq (c : CombinedMeanChart s r ρ R₀ reference n L) (hρ : 0 < ρ)
    (δ τ ε : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0) (R : c.Operator) (q : ℕ)
    {A : Base → Tensor} (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) :
    c.quadraticMean hρ δ τ ε R q A =
      fun x => δ ^ 2 • (c.leading A x + c.mean hρ δ τ ε R q A x) := by
  funext x
  by_cases hx : x ∈ c.source
  · simp only [quadraticMean, leading, mean, extendedCombinedMean, Set.indicator_of_mem hx]
    exact localQuadraticMean_eq c.localBounds hρ c.support_target c.polynomial c.jetMap δ τ ε hδ hτ R q
      hA.contDiffOn (fun p _ => hball p (Set.mem_univ p)) hx
  · simp only [quadraticMean, leading, mean, extendedCombinedMean, Set.indicator_of_notMem hx,
      zero_add, smul_zero]

end CombinedMeanChart

variable {ι : Type*}

def assembledQuadraticMean (a : Finset ι) (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hρ : 0 < ρ) (δ τ ε : ℝ) (R : ∀ i, (c i).Operator) (q : ℕ) (A : Base → Tensor) : Base → Tensor :=
  fun x => ∑ i ∈ a, (c i).quadraticMean hρ δ τ ε (R i) q A x

lemma assembledQuadraticMean_eq (a : Finset ι) (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hρ : 0 < ρ) (δ τ ε : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0) (R : ∀ i, (c i).Operator) (q : ℕ)
    {A : Base → Tensor} (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A)
    (hdecomp : ∀ x, ∑ i ∈ a, (c i).leading A x = A x) :
    assembledQuadraticMean a c hρ δ τ ε R q A =
      fun x => δ ^ 2 • (A x + assembledCombinedMean a c hρ δ τ ε R q A x) := by
  funext x
  simp only [assembledQuadraticMean, CombinedMeanChart.quadraticMean_eq _ hρ δ τ ε hδ hτ _ q hA hball]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, hdecomp x]
  rfl

lemma assembledQuadraticMean_residual (a : Finset ι) (c : ι → CombinedMeanChart s r ρ R₀ reference n L)
    (hρ : 0 < ρ) (δ τ ε : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0) (R : ∀ i, (c i).Operator) (q : ℕ)
    {A H : Base → Tensor} (hA : ContDiff ℝ ∞ A) (hH : ContDiff ℝ ∞ H)
    (hball : InTrialBall Set.univ reference r A)
    (hdecomp : ∀ x, ∑ i ∈ a, (c i).leading A x = A x) {m : ℕ} {C : ℝ}
    (hb : WeightedBound Set.univ s m C (A + assembledCombinedMean a c hρ δ τ ε R q A - H)) :
    WeightedBound Set.univ s m (δ ^ 2 * C)
      (assembledQuadraticMean a c hρ δ τ ε R q A - δ ^ 2 • H) := by
  have hT : ContDiff ℝ ∞ (assembledCombinedMean a c hρ δ τ ε R q A) :=
    ContDiff.sum (fun i _ => (c i).mean_smooth hρ δ τ ε (R i) q A)
  have hh := hb.const_smul isOpen_univ.uniqueDiffOn ((hA.add hT).sub hH).contDiffOn (δ ^ 2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  apply hh.congr
  intro x _
  rw [assembledQuadraticMean_eq a c hρ δ τ ε hδ hτ R q hA hball hdecomp]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_sub]

end ClosedSurfaceR4.PhaseMean

end

end OAI
