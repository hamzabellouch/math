import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.Rectangles
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CoverUniformBridges

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TangentRectangleCommutation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_rectangle_commutation_uniform (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u v : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (huv : u*v=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {A C D E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (R S : LabelledRectangle n) (w : CutRing),
      |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ C*(n:ℝ) →
      ∀ (d : Fin 2) (z : CutRing × CutRing),
      (∀ j, |(pointLabel z j+symmetricWindowStart s j-R.start j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (R.lower j)-ordinary (pointCoordinate z j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (R.upper j)-ordinary (pointCoordinate z j)| ≤ D/(n:ℝ)) →
      Nonempty (R.ChartFit s z) → Nonempty (S.ChartFit s (z+tangentOffset a d w)) →
      (∀ j, ordinary (signQuadrantLower s d true j)+ordinary (pointCoordinate z j) ≤ ordinary (R.lower j)) →
      (∀ j, ordinary (R.upper j) ≤ ordinary (signQuadrantUpper s d true j)+ordinary (pointCoordinate z j)) →
      (∀ j, ordinary (signQuadrantLower s d false j)+ordinary (pointCoordinate (z+tangentOffset a d w) j) ≤ ordinary (S.lower j)) →
      (∀ j, ordinary (S.upper j) ≤ ordinary (signQuadrantUpper s d false j)+ordinary (pointCoordinate (z+tangentOffset a d w) j)) →
      ∀ x y, Commute (B.rectangleCopy (by omega) g R x) (B.rectangleCopy (by omega) g S y) := by
  obtain ⟨N,hN,htransport⟩ := tangent_transport_uniform_cover_uniform
    (a := a) (hm := hm) hlarge hr s u v hs hsr huv hshort hA hC hD hE
  refine ⟨N,hN,?_⟩
  intro M B h n hn g R S w hw hw' d z hp hlo hup hfit hfit' hRL hRU hSL hSU
  obtain ⟨fit⟩ := hfit
  obtain ⟨fit'⟩ := hfit'
  have hsr' : ordinary s < ordinary r := by linarith [hr.1]
  have hcR := B.rectangleCopy_quadrant_control hlarge hr s u ⟨hs,hsr'⟩ h g R d z true fit hRL hRU
  have hcS := B.rectangleCopy_quadrant_control hlarge hr s u ⟨hs,hsr'⟩ h g S d
    (z+tangentOffset a d w) false fit' hSL hSU
  have hfinal := htransport M B h n hn g R.length R.length_le R.start R.lower R.upper
    R.ordered R.lower_label R.upper_label w hw hw' d z hp hlo hup
    (B.rectangleCopy (by omega) g R) (B.rectangleCopy_supported (by omega) g R)
    (B.rectangleCopy_axes_control (by omega) g R) hcR
  exact small_control_disjoint _ B.c B.constant_aligned B.disjoint_aligned
    (by simpa using hlarge) _ _ _ _
    (B.rectangleCopy_supported (by omega) g R) (B.rectangleCopy_supported (by omega) g S)
    (B.tangentSign_supported (by omega) _ _ u h d (z+tangentOffset a d w) true)
    hfinal hcS (B.tangentSign_opposite_commute (by omega) _ _ u h d (z+tangentOffset a d w))

end InitialCoverSystem
end TangentRectangleCommutation

end SimpleAmenable
end
end

end OAI
