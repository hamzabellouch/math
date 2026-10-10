import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AnalyticCentering

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset Filter OrdinaryCorrelations
open scoped ContDiff

theorem analytic_centering_limsup (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hNP : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0<h) (τ C₀ T : ℝ) (hτ1 : 1<τ) (hτ2 : τ<2)
    (hC₀ : 1≤C₀) (hT : 0<T) (phi : ℝ→ℝ) (hφ : ContDiff ℝ ∞ phi)
    (hφb : ∀x,0≤phi x ∧ phi x≤1) (hφs : Function.support phi⊆Set.Icc (-T) T) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ B : ℝ in atTop,
    ∀ H : ℝ, ∀ D : Finset ℕ, Admissible B C₀ τ H D →
    ∀ a : ℕ→ℂ, (∀d∈D,‖a d‖≤1) →
      limsup (fun X:ℝ=>‖rawSum phi B D a f g h X-centeredSum phi B D a f g h X‖/X) atTop
        ≤ C*L₀ B*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B):=by
  obtain ⟨C,hC,hM⟩:=analytic_centering f g hf hg hfm hgm hNP h hh τ C₀ T hτ1 hτ2 hC₀ hT phi hφ hφb hφs
  refine ⟨C,hC,?_⟩
  filter_upwards [hM] with B hB
  intro H D hD a ha
  have hb:∀ᶠ X:ℝ in atTop,
      ‖rawSum phi B D a f g h X-centeredSum phi B D a f g h X‖/X≤
        C*L₀ B*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B):=by
    filter_upwards [hB H D hD a ha,eventually_gt_atTop (0:ℝ)] with X hX hXp
    exact (div_le_iff₀ hXp).mpr hX
  have hn:∀ᶠ X:ℝ in atTop,
      0≤‖rawSum phi B D a f g h X-centeredSum phi B D a f g h X‖/X:=by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hXp
    exact div_nonneg (norm_nonneg _) hXp.le
  exact limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hn) hb
end OrdinaryAnalyticCentering

end

end OAI
