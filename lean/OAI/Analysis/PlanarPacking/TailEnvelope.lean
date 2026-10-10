import OAI.Analysis.PlanarPacking.RationalEnvelopes
import OAI.Analysis.PlanarPacking.Certificate.TailCoefficients

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma direct_two_rat_cap : directRational 2 < 77 := by
  norm_num [directRational,piUpper,densityCap,densityNum,densityDen,Fin.sum_univ_succ]
lemma tail_second_rat_cap : (5:ℝ)/10^5*77+(23:ℝ)/10*transformRational 2 41+
    (17:ℝ)/1000*atomicRational 2 41 < 6/1000 := by
  norm_num [transformRational,atomicRational,pieceIntCap,atomIntCap,massRational,
    piUpper,densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomMass,atomBase,
    slopeCap,zCap,Fin.sum_univ_succ]
noncomputable def tailData (a : Bool) : CardinalData := positiveData (tailList (exactList a) 40)
noncomputable def tailErrorJet (a : Bool) (ell : ℕ) (s : ℝ) : ℝ :=
  cardinalSeries (tailData a) ell s+K (exactData (!a)) ell s
lemma tailErrorJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (tailErrorJet a ell) (tailErrorJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
lemma tail_second_bound (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    |tailErrorJet a 2 s| < 6/1000 := by
  have hs41 : (41:ℝ) ≤ s := by linarith
  have h0 : 0 ≤ s := by linarith
  have hD:=direct_positive_bound (tailList (exactList a) 40) 2 s
  change |cardinalSeries (tailData a) 2 s| ≤ ‖tailList (exactList a) 40‖*directEnvelope 2 at hD
  have hdr : directEnvelope 2 < 77 := (directEnvelope_le_rat 2).trans_lt direct_two_rat_cap
  have hDn := mul_le_mul (exact_tail_norm a).le hdr.le (directEnvelope_nonneg 2) (by norm_num : (0:ℝ) ≤ 5/10^5)
  have hK:=sharp_moment_bound (exactData (!a)) 2 h0
  change |K (exactData (!a)) 2 s| ≤
    (|(exactData (!a)).c₀|+|(exactData (!a)).d₀|+‖(exactData (!a)).x‖)*transformEnvelope 2 s+
      |(exactData (!a)).C| *atomicEnvelope 2 s at hK
  have ht := (transformEnvelope_antitone 2 (by norm_num : (0:ℝ) ≤ 41) hs41).trans (transformEnvelope_le_rat 2 41)
  have hA := (atomicEnvelope_antitone 2 hs41).trans (atomicEnvelope_le_rat 2 41)
  have ht' := mul_le_mul (exact_coeff_mass (!a)).le ht
    (transformEnvelope_nonneg 2 h0) (by norm_num : (0:ℝ) ≤ 23/10)
  have hA' := mul_le_mul (exact_constant_bound (!a)) hA
    (atomicEnvelope_nonneg 2 s) (by norm_num : (0:ℝ) ≤ 17/1000)
  have hh:=abs_add_le (cardinalSeries (tailData a) 2 s) (K (exactData (!a)) 2 s)
  change |tailErrorJet a 2 s| ≤ _ at hh
  linarith [tail_second_rat_cap]
end SharpPlanar

end OAI
