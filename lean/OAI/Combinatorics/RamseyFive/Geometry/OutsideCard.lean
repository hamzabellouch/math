import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.LocalLines
import OAI.Combinatorics.RamseyFive.Geometry.MomentPolynomialTail
import OAI.Combinatorics.RamseyFive.Probability.PencilFactor
import OAI.Combinatorics.RamseyFive.Iteration.ScaleAgainstB

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GlobalRadial PoissonScore WeightedPrograms
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] (x : ℙ K V) [Fintype (RadialLine x)]

omit [FiniteDimensional K V] [Finite K] [Fintype (RadialLine x)] in
lemma outsideAt_card_le (S O : Finset (ℙ K V)) : (outsideAt x S O).card ≤ S.card := by
  unfold outsideAt
  rw [Finset.card_subtype]
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.sdiff_subset)

theorem score_pair_low_normalized (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) L Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)) :
    ((Finset.univ.filter fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0<Nat.card K)
  have hN : (δ:ℝ)*(outsideAt x S (O x)).card ≤ Nat.card K := by
    apply le_trans _ hmass
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast outsideAt_card_le x S (O x)) δ.coe_nonneg
  apply ScoreScalars.normalized_pair_low hn ha.le ha2 hlow hchi
  exact ScoreScalars.pair_power_two_hundred hq hn δ.coe_nonneg (Nat.cast_nonneg _) ha ha2 hN
    (score_pairs_off_radial_exception x hdim S O δ hδ F hF _ _ ha.le L hL Q hx hgood)

theorem score_pair_small_normalized (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n a χ : ℝ) (hn : 0<n) (ha : 0<a) (ha2 : a ≤ 2)
    (hmass : (δ:ℝ)*S.card ≤ Nat.card K) (hsmall : n*a^99 ≤ (Nat.card K:ℝ)^2)
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hgood : x∉badCenters S O δ (a/2) L Q ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(a/2)^100)) :
    ((Finset.univ.filter fun p : DistinctPairs F => a ≤
      strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p).card:ℝ)*a^200 ≤
      ((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ) := by
  have hq : (1:ℝ) ≤ Nat.card K := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.card_pos : 0<Nat.card K)
  have hN : (δ:ℝ)*(outsideAt x S (O x)).card ≤ Nat.card K := by
    apply le_trans _ hmass
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast outsideAt_card_le x S (O x)) δ.coe_nonneg
  apply ScoreScalars.normalized_pair_small hn ha.le hsmall hchi
  exact ScoreScalars.pair_power_two_hundred hq hn δ.coe_nonneg (Nat.cast_nonneg _) ha ha2 hN
    (score_pairs_off_radial_exception x hdim S O δ hδ F hF _ _ ha.le L hL Q hx hgood)

theorem score_pair_low_moment (hdim : finrank K V=5)
    (S : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V)) (δ : ℝ≥0) (hδ : 0<δ)
    (F : Finset (ℙ K (Dual K V))) (hF : ∀ H∈F,Incident x H)
    (n χ : ℝ) (hn : 0<n) (hmass : (δ:ℝ)*S.card ≤ Nat.card K)
    (hlow : n ≤ (Nat.card K:ℝ)^2*Real.exp (χ/2))
    (hchi : (11*2^200:ℝ) ≤ Real.exp χ)
    (L : Finset (Submodule K V)) (hL : ∀ l : RadialLine x,l.val∈L)
    (Q : Finset (ℙ K V)) (hx : x∈Q)
    (hm : ∀ H : F,mass (radialWeight x (outsideAt x S (O x)) δ) (pencilLines x F H) ≤ 2)
    (hgood : ∀ i∈boundedOverlapDyads x (outsideAt x S (O x)) δ 2,
      x∉badCenters S O δ (((δ:ℝ)*2^i)/2) L Q
        ((Nat.card K:ℝ)^4/n^2*Real.exp χ/(((δ:ℝ)*2^i)/2)^100))
    (R : ℕ) (hR : 200 ≤ R) :
    (∑ p : DistinctPairs F,strength (pencilLines x F) (radialWeight x (outsideAt x S (O x)) δ) p^R) ≤
      2^R*(Nat.clog 2 (outsideAt x S (O x)).card+1)*(((Nat.card K:ℝ)^4/n)^2*Real.exp (2*χ)) := by
  apply score_higher_power x _ δ hδ F hF _ (by positivity) 200 R (by norm_num) hR hm
  intro i hi
  exact score_pair_low_normalized x hdim S O δ hδ F hF n _ χ hn (by positivity)
    (Finset.mem_filter.mp hi).2 hmass hlow hchi L hL Q hx (hgood i hi)

end SharpRamseyFive.ScoreGeometry

end OAI
