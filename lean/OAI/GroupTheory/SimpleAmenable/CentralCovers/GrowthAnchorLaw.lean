import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AxisCutCommutation
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisAnchorFamily

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GrowthAnchorLaw
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem growth_anchor_law (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ (N : ℕ) (_hN : 1005 ≤ N), ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, ∀ hn : N ≤ n, ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (p : ℤ),
      CentralOn (coverMap M (alternatingGenerator a r m hm))
        (⨆ i : Fin (growthAnchorLength n), ⨆ j : Fin ((growthAnchorFamily n (by omega) p).count i+1),
          (((growthAnchorFamily n (by omega) p).cuts i).prefixCopy B (by omega) g d j.val).range) := by
  obtain ⟨N,hN,hcomm⟩ := axis_cut_sequence_commutations
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  refine ⟨N,hN,?_⟩
  intro M B h n hn g d p
  let A := growthAnchorFamily n (by omega) p
  have hlens := growth_lengths (show 1005 ≤ n by omega)
  apply A.prefixes_central B (by omega) g d hlens.2.2.2.1 hlens.2.2.2.2.1 _ hlarge
  intro i j k hjk x y
  have hh := hcomm M B h n hn g d (A.count i) (A.cuts i) ?_ (growthAnchorFamily.label_difference n (by omega) p i)
  · exact hh.2 j k hjk x y
  · apply (growthAnchorFamily.width n (by omega) p i).trans
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)

end InitialCoverSystem
end GrowthAnchorLaw

end SimpleAmenable
end
end

end OAI
