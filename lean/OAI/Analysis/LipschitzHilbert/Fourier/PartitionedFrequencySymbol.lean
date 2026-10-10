import OAI.Analysis.LipschitzHilbert.Estimates.FiniteMultiplierRecombination
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedBandForm

namespace OAI

/-! The concrete slope-partitioned frequency symbol is uniformly bounded
and measurable, including at the zero of its vertical denominator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def partitionedFrequencySymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℂ :=
  psi (l*(p.2.1+u p.1*p.2.2))*rho (-symbolX l p.2.1 p.2.2 theta/(w*p.2.2))*
    beta (symbolY W p.2.2 center)

def annularBandSymbol (psi beta : SchwartzMap ℝ ℂ)
    (l W center : ℝ) (u : ℝ×ℝ → ℝ) (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℂ :=
  psi (l*(p.2.1+u p.1*p.2.2))*beta (symbolY W p.2.2 center)

theorem partitionedFrequencySymbol_measurable (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (partitionedFrequencySymbol psi rho beta l W w theta center u) := by
  have hu' : Measurable (fun p : (ℝ×ℝ)×(ℝ×ℝ) => u p.1) := hu.comp measurable_fst
  unfold partitionedFrequencySymbol symbolX symbolY
  apply Measurable.mul
  · apply Measurable.mul
    · apply psi.continuous.measurable.comp
      fun_prop
    · apply rho.continuous.measurable.comp
      fun_prop
  · apply beta.continuous.measurable.comp
    fun_prop

theorem partitionedFrequencySymbol_bound (psi rho beta : SchwartzMap ℝ ℂ)
    (l W w theta center : ℝ) (u : ℝ×ℝ → ℝ) (z omega : ℝ×ℝ) :
    ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤
      SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta := by
  unfold partitionedFrequencySymbol
  rw [norm_mul,norm_mul]
  exact mul_le_mul
    (mul_le_mul (SchwartzMap.norm_le_seminorm ℝ psi _) (SchwartzMap.norm_le_seminorm ℝ rho _)
      (norm_nonneg _) (apply_nonneg _ _))
    (SchwartzMap.norm_le_seminorm ℝ beta _) (norm_nonneg _) (by positivity)

theorem sum_partitionedFrequencySymbol {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center : ℝ) (theta : ι → ℝ)
    (u : ℝ×ℝ → ℝ)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1) :
    (fun p => ∑ i, partitionedFrequencySymbol psi rho beta l W w (theta i) center u p)=
      annularBandSymbol psi beta l W center u := by
  classical
  funext p
  rcases p with ⟨z,omega⟩
  unfold partitionedFrequencySymbol annularBandSymbol
  by_cases hp : psi (l*(omega.1+u z*omega.2))=0
  · simp only [hp,zero_mul,Finset.sum_const_zero]
  by_cases hb : beta (symbolY W omega.2 center)=0
  · simp only [hb,mul_zero,Finset.sum_const_zero]
  rw [←Finset.sum_mul,←Finset.mul_sum,hpartition z omega hp hb,mul_one]

theorem recombine_partitioned_frequency_pairing {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center : ℝ) (theta : ι → ℝ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplier
      (partitionedFrequencySymbol psi rho beta l W w (theta i) center u) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplier (annularBandSymbol psi beta l W center u) f z*star (g z) ∂planeMeasure := by
  rw [finite_variableFrequencyMultiplier_pairing
    (fun i => partitionedFrequencySymbol psi rho beta l W w (theta i) center u)
    (fun i => partitionedFrequencySymbol_measurable psi rho beta l W w (theta i) center u hu)
    (fun _ => SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta)
    (fun i => partitionedFrequencySymbol_bound psi rho beta l W w (theta i) center u) f g hg,
    sum_partitionedFrequencySymbol psi rho beta l W w center theta u hpartition]

end LipschitzHilbert.PacketRepresentation

end

end OAI
