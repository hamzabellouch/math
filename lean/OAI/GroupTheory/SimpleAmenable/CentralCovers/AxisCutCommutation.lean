import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.DisjointPolygonAtoms
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.AxisCutSequences

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AxisCutCommutation
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axis_cut_sequence_commutations (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (K : ℕ) (D : AxisCutSequence n K),
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) ≤ C/(n:ℝ) →
      (∀ i j, |(endpointLabel (D.cut j-D.cut i):ℝ)| ≤ 6*(n:ℝ)/5) →
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 ∧
      ∀ i j : ℕ, i ≤ j → ∀ x y,
        Commute (D.prefixCopy B (by omega) g d i x) (D.suffix B (by omega) g d j y) := by
  obtain ⟨N₀,hN₀,hcomm⟩ := separated_axis_sectors_commute
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt C
  refine ⟨max N₀ N₁,by omega,?_⟩
  intro M B h n hn g d K D hwidth hlabels
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hCn : C < (n:ℝ) := hN₁.trans_le (by exact_mod_cast (show N₁ ≤ n by omega))
  have hlen : ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) < 1 :=
    hwidth.trans_lt ((div_lt_one hnp).mpr hCn)
  refine ⟨hlen,?_⟩
  intro i j hij x y
  have hle := D.index_mono hij
  rcases eq_or_lt_of_le hle with he | hlt
  · have hp : D.prefixCopy B (by omega) g d i = D.prefixCopy B (by omega) g d j := by
      simp only [AxisCutSequence.prefixCopy,he]
    rw [hp]
    exact D.prefix_suffix_self_commute B (by omega) g d hlen j x y
  · exact hcomm M B h n (by omega) g d _ _ (D.length_le _) (D.length_le _)
      _ _ _ _ _ _ (D.ordered _).1 (D.strictMono hlt) (D.ordered _).2
      (D.lower_label _) (D.cut_label _) (D.cut_label _) (D.upper_label _)
      hwidth (hlabels _ _) x y

end InitialCoverSystem
end AxisCutCommutation

section AxisCutLocalLaw
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axis_cut_sequence_central (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s w z : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hwz : w*z=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary w|+|ordinary (cutTau*w)|) < ordinary s/4)
    {C : ℝ} (hC : 1000 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 1005 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) w),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (K : ℕ) (D : AxisCutSequence n K),
      ordinary (D.cut (Fin.last K))-ordinary (D.cut 0) ≤ C/(n:ℝ) →
      (∀ i j, |(endpointLabel (D.cut j-D.cut i):ℝ)| ≤ 6*(n:ℝ)/5) →
      CentralOn (coverMap M (alternatingGenerator a r m hm))
        (⨆ i : Fin (K+1), (D.prefixCopy B (by omega) g d i.val).range) := by
  obtain ⟨N,hN,hcomm⟩ := axis_cut_sequence_commutations
    (a := a) (hm := hm) hlarge hr s w z hs hsr hwz hshort hC hSlope hconj
  refine ⟨N,hN,?_⟩
  intro M B h n hn g d K D hwidth hlabels
  obtain ⟨hlen,hc⟩ := hcomm M B h n hn g d K D hwidth hlabels
  exact D.cuts_central B (by omega) g d hlen hc

end InitialCoverSystem
end AxisCutLocalLaw

end SimpleAmenable
end
end

end OAI
