import OAI.Probability.InvariantIsing.Fields.FieldAdjacentDerivative
import OAI.Probability.InvariantIsing.Fields.FieldScalarSquareOrder
import OAI.Probability.InvariantIsing.Fields.FieldParameterOrder

namespace OAI

/-! The spatial consequence of the backward covariance derivative.
Radial antitonicity of that derivative gives ordering of the physical
conditional means, and hence ordering of all earlier squared means. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

theorem field_spatial_derivative_order {F : ℝ → ℝ} {f g : ℝ}
    (hF : HasDerivAt F f g) {H : ℝ → ℝ} {h : ℝ}
    (hH : HasDerivAt H h g) (hg : 0 ≤ g)
    (hmono : MonotoneOn (fun y => F y - H y) (Ici 0)) : h ≤ f := by
  have hd : HasDerivAt (fun y => F y - H y) (f - h) g := hF.sub hH
  have hn := hmono.derivWithin_nonneg (x := g)
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 g hg)] at hn
  exact sub_nonneg.mp hn

namespace FieldSmoothFamily

theorem physical_mean_antitone_parameter {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : Convex ℝ I) (hD : ∀ t ∈ I, AntitoneOn (fun z => F.T (t, z)) (Ici 0))
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    ∀ z ∈ Ici (0 : ℝ), F.X (s, z) ≤ F.X (t, z) := by
  have hp := field_parameter_difference_order hI
    (fun q hq z => F.parameter_derivative q z hq) hD ht hs hts
  intro z hz
  exact field_spatial_derivative_order (F.spatial t z) (F.spatial s z) hz hp

theorem earlier_squares_antitone_parameter {I : Set ℝ} (F : FieldSmoothFamily I)
    (hI : Convex ℝ I) (hD : ∀ t ∈ I, AntitoneOn (fun z => F.T (t, z)) (Ici 0))
    (hUe : ∀ t ∈ I, Function.Even (fun z => F.U (t, z)))
    (hXo : ∀ t ∈ I, Function.Odd (fun z => F.X (t, z)))
    (hXm : ∀ t ∈ I, MonotoneOn (fun z => F.X (t, z)) (Ici 0))
    (hXp : ∀ t ∈ I, ∀ z ∈ Ici (0 : ℝ), 0 ≤ F.X (t, z))
    (hXb : ∀ p, |F.X p| ≤ 1)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    {t s : ℝ} (ht : t ∈ I) (hs : s ∈ I) (hts : t ≤ s) :
    ∀ i z, fieldScalarSquares L (fun y => F.U (s, y)) (fun y => F.X (s, y)) i z ≤
      fieldScalarSquares L (fun y => F.U (t, y)) (fun y => F.X (t, y)) i z := by
  have hp := field_parameter_difference_order hI
    (fun q hq z => F.parameter_derivative q z hq) hD ht hs hts
  exact fieldScalarSquares_order L hL
    (F := fun y => F.U (s, y)) (G := fun y => F.U (t, y))
    (a := fun y => F.X (s, y)) (b := fun y => F.X (t, y))
    (F.mU.comp (by fun_prop)) (F.mU.comp (by fun_prop)) (F.growth s) (F.growth t)
    (hUe s hs) (hUe t ht) hp
    (F.mX.comp (by fun_prop)) (F.mX.comp (by fun_prop))
    (hXo s hs) (hXo t ht) (hXm s hs) (hXm t ht) (hXp s hs) (hXp t ht)
    (fun z => hXb (s, z)) (fun z => hXb (t, z))
    (F.physical_mean_antitone_parameter hI hD ht hs hts)

end FieldSmoothFamily
end InvariantIsing

end

end OAI
