import OAI.Probability.InvariantIsing.Fields.FieldGaussianFamilyLocal
import OAI.Probability.InvariantIsing.Fields.FieldScalarOrder

namespace OAI

/-! Radial order of the parameter derivative integrates to radial
order of payoff differences, without interchanging mixed derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem field_parameter_difference_order {I : Set ℝ} (hI : Convex ℝ I)
    {F D : ℝ → ℝ → ℝ}
    (hd : ∀ t ∈ I, ∀ z, HasDerivAt (fun s => F s z) (D t z) t)
    (hD : ∀ t ∈ I, AntitoneOn (D t) (Ici 0))
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    MonotoneOn (fun z => F t z - F s z) (Ici 0) := by
  intro x hx y hy hxy
  have hder (q : ℝ) (hq : q ∈ I) :
      HasDerivAt (fun r => F r y - F r x) (D q y - D q x) q :=
    (hd q hq y).sub (hd q hq x)
  have hanti : AntitoneOn (fun r => F r y - F r x) I :=
    antitoneOn_of_hasDerivWithinAt_nonpos hI
      (fun q hq => (hder q hq).continuousAt.continuousWithinAt)
      (fun q hq => (hder q (interior_subset hq)).hasDerivWithinAt)
      (fun q hq => sub_nonpos.mpr (hD q (interior_subset hq) hx hy hxy))
  have h := hanti ht hs hts
  linarith

end InvariantIsing

end

end OAI
