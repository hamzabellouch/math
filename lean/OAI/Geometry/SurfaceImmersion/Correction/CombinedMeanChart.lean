import OAI.Geometry.SurfaceImmersion.Correction.CombinedMeanMajorants

namespace OAI

/-! The concrete fixed data of one chart for the combined mean. This record
only groups the geometric, support and polynomial data used by the local
construction; its mean estimates are proved from those data. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates FiniteMean
open JetPolynomial (SupportedField supportedWeightedSeminorm)
open JetPolynomial.Perturbation (modeSupport)

structure CombinedMeanChart (s r ρ R₀ : ℝ) (reference : Base → Tensor) (n L : ℕ) where
  source : Set Base
  target : Set Base
  support : Compacts JetPolynomial.Base
  cutoff : SupportedField (F := ℝ) (modeSupport support)
  immersion : RField 4
  coefficient : Base → Tensor →L[ℝ] ℝ
  chart : Base → Base
  inverse : Base → Base
  localBounds : LocalBounds source target s r ρ R₀ reference immersion cutoff coefficient chart inverse
  budgets : Budgets source target s immersion cutoff coefficient chart inverse
  support_target : (modeSupport support : Set Base) ⊆ target
  outerSupport : Set Base
  outer_closed : IsClosed outerSupport
  outer_source : outerSupport ⊆ source
  support_chart : ∀ x ∈ source, chart x ∈ (modeSupport support : Set Base) → x ∈ outerSupport
  polynomial : Fin 3 → Fin n → JetPolynomial.Expression
  jetSource : Set JetPolynomial.Base
  coefficientDomain : Set JetPolynomial.LowJet
  compactJets : Set JetPolynomial.LowJet
  jetSource_open : IsOpen jetSource
  coefficientDomain_open : IsOpen coefficientDomain
  compactJets_compact : IsCompact compactJets
  compactJets_domain : compactJets ⊆ coefficientDomain
  coefficients_smooth : ∀ i l, (polynomial i l).SmoothCoeffs coefficientDomain
  support_jetSource : (support : Set JetPolynomial.Base) ⊆ jetSource
  jetMap : JetPolynomial.Base → JetPolynomial.Space
  jetMap_smooth : ContDiff ℝ ∞ jetMap
  jetMap_range : Set.MapsTo (JetPolynomial.lowJet jetMap) jetSource compactJets
  operatorBudget : ℕ → ℝ
  operatorBudget_nonneg : ∀ m, 0 ≤ operatorBudget m
  jetBudget : ℕ → ℝ
  jetBudget_pos : ∀ m, 1 ≤ jetBudget m
  jets_bound : ∀ m, WeightedBound jetSource s
    (m + JetPolynomial.Perturbation.tensorOrder polynomial) (jetBudget m) (JetPolynomial.lowJet jetMap)

namespace CombinedMeanChart
variable {s r ρ R₀ : ℝ} {reference : Base → Tensor} {n L : ℕ}

abbrev Operator (c : CombinedMeanChart s r ρ R₀ reference n L) :=
  SupportedField (F := Ambient 4) (modeSupport c.support) →ₗ[ℝ]
    SupportedField (F := Fin 3 → ℂ) (modeSupport c.support)

def mean (c : CombinedMeanChart s r ρ R₀ reference n L) (hρ : 0 < ρ)
    (δ τ ε : ℝ) (R : c.Operator) (q : ℕ) : (Base → Tensor) → Base → Tensor :=
  extendedCombinedMean c.localBounds hρ c.support_target c.polynomial c.jetMap δ τ ε R q

def loss (c : CombinedMeanChart s r ρ R₀ reference n L) (q : ℕ) : ℕ :=
  JetPolynomial.Perturbation.tensorOrder c.polynomial + 1 + (q + 1) * (L + 1)

def exponent (c : CombinedMeanChart s r ρ R₀ reference n L) : ℕ :=
  JetPolynomial.Perturbation.tensorLoss c.polynomial

def OperatorBound (c : CombinedMeanChart s r ρ R₀ reference n L) (hs : 0 < s)
    (τ ε : ℝ) (p : ℕ) (R : c.Operator) : Prop :=
  ∀ m Z, supportedWeightedSeminorm (modeSupport c.support) ⟨s, hs.le⟩ m (R Z) ≤
    ε / τ ^ p * c.operatorBudget m * supportedWeightedSeminorm (modeSupport c.support) ⟨s, hs.le⟩ (m + L) Z

theorem majorants (c : CombinedMeanChart s r ρ R₀ reference n L)
    (hs : 0 < s) (hs1 : s ≤ 1) (hρ : 0 < ρ) (q : ℕ) :
    ∃ B K : ℕ → ℝ → ℝ, ∀ δ τ ε : ℝ, ∀ p : ℕ,
      0 < δ → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → c.exponent ≤ p →
      τ / s + ε / τ ^ p ≤ 1 → ∀ R : c.Operator, c.OperatorBound hs τ ε p R →
      MeanBounds Set.univ s reference r (c.loss q)
        (rescaledMean (τ / s + ε / τ ^ p) (c.mean hρ δ τ ε R q)) B K :=
  extendedCombinedMean_majorants c.localBounds c.budgets hs hs1 hρ c.support_target
    c.outer_closed c.outer_source c.support_chart c.jetSource_open c.coefficientDomain_open
    c.compactJets_compact c.compactJets_domain c.coefficients_smooth c.support_jetSource
    c.jetMap_smooth c.jetMap_range c.operatorBudget c.jetBudget c.operatorBudget_nonneg c.jetBudget_pos c.jets_bound q

end CombinedMeanChart
end ClosedSurfaceR4.PhaseMean

end

end OAI
