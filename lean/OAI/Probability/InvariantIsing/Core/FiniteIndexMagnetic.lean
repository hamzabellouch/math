import OAI.Probability.InvariantIsing.Core.FiniteIndexCoupling
import OAI.Probability.InvariantIsing.Spectral.MeasureMagneticTransport

namespace OAI

/-! The magnetic transportation estimate on a common probability space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace InvariantIsing

lemma finiteIndex_magnetic_sub_le {Ω A B : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → A) (h : Ω → B) (hg : Measurable g) (hh : Measurable h)
    (c : A → ℝ) (d : B → ℝ) (hpos : ∀ b, 0 < finiteIndexWeight P h b)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support) :
    (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) (finiteIndexWeight P g) c).toReal-
      (finiteMagneticFunctional (measureR (ν : Measure ℝ) b) (finiteIndexWeight P h) d).toReal ≤
      ∫ x, |c (g x)-d (h x)| ∂P := by
  have ht := measureMagnetic_transport_le ν a b hcompact hbound ha hb
    (finiteIndexCoupling P g h) (finiteIndexWeight P g) c (finiteIndexWeight P h) d
    (fun _ _ => measureReal_nonneg) (fun _ => measureReal_nonneg) hpos
    (finiteIndexWeight_sum P g hg) (finiteIndexWeight_sum P h hh)
    (finiteIndexCoupling_row P g h hh) (finiteIndexCoupling_col P g h hg)
  rw [← finiteIndexCoupling_integral P g h hg hh] at ht
  linarith

end InvariantIsing

end

end OAI
