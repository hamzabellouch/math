import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandSeparation
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszGeneralMean

namespace OAI

/-! The chosen bands avoid every small correction or gcd divisor, and
passing to the completely multiplicative part preserves the exact distance. -/
namespace TwoPointCorrelations

open Finset

lemma major_arc_actual_prime_lower {P Q : ℝ} {J j p : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P)
    (hj : j ∈ Icc 1 J)
    (hp : p ∈ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) : P < (p:ℝ) := by
  have hlo := mrt_band_lower_monotone P Q 1 j (by decide) (mem_Icc.mp hj).1 hP hPQ hLP
  rw [mrtBandLower_one P Q (by linarith)] at hlo
  have hb := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
  exact hlo.trans_lt hb.1

lemma major_arc_actual_bands_avoid {P Q : ℝ} {J d : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P)
    (hd : 0 < d) (hdP : (d:ℝ) ≤ P) :
    mrtPrimeAvoids ((Icc 1 J).biUnion
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d := by
  apply mrtPrimeAvoids_of_lt _ hd
  intro p hp
  obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
  exact_mod_cast hdP.trans_lt (major_arc_actual_prime_lower hP hPQ hLP hj hp)

lemma major_arc_actual_bands_disjoint {P Q : ℝ} {J : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hLP : 1 < Real.log P) :
    Set.PairwiseDisjoint (Icc 1 J : Set ℕ)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) := by
  intro i hi j hj hij
  have hdis := mrt_actual_bands_pairwise_disjoint P Q J hP hPQ hLP
  exact hdis (x := ⟨i,hi⟩) (y := ⟨j,hj⟩) (by trivial) (by trivial)
    (fun h => hij (congrArg Subtype.val h))

lemma major_arc_first_prime_range {P Q W : ℝ} {H R₀ p : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hPW : 2*W ≤ P) (hPR : (2*R₀:ℕ) ≤ P)
    (hQH : Q ≤ (H:ℝ)/W)
    (hp : p ∈ mrtPrimeBand (mrtBandLower P Q 1) (mrtBandUpper Q 1)) :
    p ≠ 2 ∧ 2*R₀ ≤ p ∧ 2*W ≤ (p:ℝ) ∧ (p:ℝ) ≤ (H:ℝ)/W := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := hP0.trans_le hPQ
  have hp' : p ∈ mrtPrimeBand P Q := by
    simpa only [mrtBandLower_one P Q hP0,mrtBandUpper_one Q hQ0] using hp
  have hb := mrtPrimeBand_bounds hP0.le hQ0.le hp'
  refine ⟨?_,?_,hPW.trans hb.1.le,hb.2.trans hQH⟩
  · intro he
    norm_num [he] at hb
    linarith [hb.1]
  · exact_mod_cast hPR.trans hb.1.le

lemma major_arc_complete_distance {F : ℕ → ℂ} {X H : ℕ} {M : ℝ}
    (hd : MRTDistanceLowerBound F X H M) :
    MRTDistanceLowerBound (mrtCompletePart F) X H M := by
  intro q hq hqmax χ t ht
  rw [halasz_complete_distance]
  exact hd q hq hqmax χ t ht

end TwoPointCorrelations

end OAI
