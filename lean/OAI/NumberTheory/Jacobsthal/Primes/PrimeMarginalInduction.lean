import OAI.NumberTheory.Jacobsthal.Partitions.MarginalTransport
import OAI.NumberTheory.Jacobsthal.Partitions.SourceParentBin

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.PrimeMarginalInduction

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalRecursion MarginalProfiles MarginalTransport SourceParentBin ExponentialMesh DerivativeWeights

theorem finite_marginal_profiles : ∃ κ₀ L : ℝ, 0 < κ₀ ∧ 0 < L ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ w₀ : ℝ, 1 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
    ∀ ell S : ℝ, 3 ≤ S → S ≤ (Real.log w)^3 → ∀ start : Node,
      1 ≤ ell → 0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      ∀ m : ℕ, 1 ≤ m → width m = mesh κ w → width m ≤ 1/100 →
      (∀ n,IsProbabilityMeasure (pathLaw w ell S start n)) ∧
      (∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
        ENNReal.ofReal (initialConstant*MarginalGrowth.factor L κ w S*width m*W (point m j)*weight .odd (point m j))) ∧
      (∀ n,2 ≤ n → ∀ j,lowerIndex m (sideAfter .even n) ≤ j → mass w ell S start m n j ≤
        ENNReal.ofReal ((24*initialConstant)*(MarginalGrowth.factor L κ w S)^n*width m*
          weight (sideAfter .even n) (point m j)*profile m (sideAfter .even n) (point m j))) := by
  obtain ⟨κ₀,L,hκ₀,hL,hcovered⟩ := covered_recursion
  refine ⟨κ₀,L,hκ₀,hL,?_⟩
  intro κ hκ hκle
  obtain ⟨wR,hwR,hrec⟩ := hcovered κ hκ hκle
  refine ⟨max wR normalizationThreshold,hwR.trans_le (le_max_left _ _),?_⟩
  intro w hw ell S hS3 hS start hell hr hi h199 h23 m hm hmesh hsmall
  have hwR' := (le_max_left _ _).trans hw
  have hnorm := (le_max_right _ _).trans hw
  have hs : Valid start.side start.ratio := by rw [hi,Valid]; linarith
  have hsS : start.ratio ≤ S := by linarith
  have hC0 := initialConstant_pos.le
  have hg := (MarginalGrowth.factor_pos L κ w S).le
  have hwidth := width_nonneg m
  refine ⟨fun n => pathLaw_isProbability hnorm hell (by linarith) hS hr hs hsS n,?_⟩
  have hfirst : ∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
      ENNReal.ofReal (initialConstant*MarginalGrowth.factor L κ w S*width m*W (point m j)*weight .odd (point m j)) := by
    intro j hjV
    by_cases hjS : point m j ≤ S
    · have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m 0 j hm hmesh .even {index m start}
        hjV hjS (source_coverage hm hsmall hi h199 j)
      rw [Finset.sum_singleton,source_grid_mass hm (by linarith : 0 ≤ start.ratio),mul_one] at hbase
      have hInv := source_inverse_weight hm hsmall start h199 h23
      have hkV := source_left_valid hm hsmall start h199
      have hWt := (WeightFutureIntegrals.W_pos (valid_pos hjV)).le
      have hφ := (weight_pos hjV).le
      have hFactor : 0 ≤ width m*W (point m j)*weight .odd (point m j) := by positivity
      refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
      calc
        _ = (rowFactor L κ w S*(width m*W (point m j)*weight .odd (point m j)))*
            (1/weight .even (point m (index m start))) := by unfold entry rowFactor; simp only [Side.flip]; ring
        _ ≤ (MarginalGrowth.factor L κ w S*(width m*W (point m j)*weight .odd (point m j)))*initialConstant :=
          mul_le_mul (mul_le_mul_of_nonneg_right (row_le_factor L κ w S) hFactor) hInv
            (one_div_nonneg.mpr (weight_pos hkV).le) (by positivity)
        _ = _ := by ring
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) 1]
      exact zero_le
  have hsecond : ∀ j,2*m ≤ j → mass w ell S start m 2 j ≤
      ENNReal.ofReal ((24*initialConstant)*(MarginalGrowth.factor L κ w S)^2*width m*weight .even (point m j)) := by
    intro j hj
    by_cases hjS : point m j ≤ S
    · have hjV : Valid .even (point m j) := index_valid hm .even hj
      have hcover := weak_coverage (w:=w) (ell:=ell) (S:=S) hs hi hm hsmall 1 (by omega) j
      have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m 1 j hm hmesh .odd (weakIndices m j .odd)
        hjV hjS (by simpa only [sideAfter,Side.flip] using hcover)
      exact hbase.trans (first_to_second L κ w S initialConstant hm j hj (fun k => mass w ell S start m 1 k) hC0 hfirst)
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) 2]
      exact zero_le
  refine ⟨hfirst,?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro j hj
    have hj' : 2*m ≤ j := hj
    simpa only [sideAfter,Side.flip,profile,mul_one] using hsecond j hj'
  | succ n hn ih =>
    intro j hj
    by_cases hjS : point m j ≤ S
    · let i := sideAfter .even n
      have hj' : lowerIndex m i.flip ≤ j := hj
      have hjV := index_valid hm i.flip hj'
      have hbase := hrec w hwR' ell S hS3 hS start hell hr hs hsS m n j hm hmesh i
        (Finset.Icc (lowerIndex m i) (j+m+1)) hjV hjS (regular_coverage hs hi hm n hn j)
      have hnext := profile_step L κ w S (24*initialConstant) hm hmesh n j i
        (fun k => mass w ell S start m n k) (by positivity) hj' (fun k hk => ih k hk)
      exact hbase.trans hnext
    · rw [mass_zero_above hsS (lt_of_not_ge hjS) (n+1)]
      exact zero_le

end NumberTheoryLean.PrimeMarginalInduction

end

end Erdos970

end OAI
