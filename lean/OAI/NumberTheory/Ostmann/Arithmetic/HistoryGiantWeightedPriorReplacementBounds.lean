import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacementSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement
open Construction HistorySignedResidues HistoryGiantPriorGrid

@[simp] theorem primeTest_weightedResidueTest {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (u : Bool → (ZMod M)ˣ) :
    primeTest (weightedResidueTest g V outside h k M hd W) u =
      W ((u false : ZMod M),(u true : ZMod M))*primeResidueTest g V outside h k M hd u := rfl

@[simp] theorem mixedTest_weightedResidueTest {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (r : ZMod M) (u : Unit → (ZMod M)ˣ) :
    mixedTest (weightedResidueTest g V outside h k M hd W) r u =
      W (r,(u () : ZMod M))*mixedResidueTest g V outside h k M hd r u := rfl

theorem norm_actual_weightedResidueTest_le {l : ℕ} (d : Decomposition) (V : ℕ → ℕ)
    (outside : List ℕ) (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M)
    (hout : ∀q∈outside,q.Prime) (W : ZMod M × ZMod M → ℂ)
    (BW : ℝ) (hBW : 0 ≤ BW) (hW : ∀z, ‖W z‖ ≤ BW) (z : ZMod M × ZMod M) :
    ‖weightedResidueTest (residueTransform d) V outside h k M hd W z‖ ≤
      BW*(outside.prod : ℝ)^(2^(l+1)) := by
  rw [weightedResidueTest,norm_mul]
  exact mul_le_mul (hW z) (norm_actual_liftedResidueTest_le d V outside h k M hd hout z)
    (norm_nonneg _) hBW

theorem sum_norm_primeTest_weighted_le {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (BW : ℝ) (hW : ∀z, ‖W z‖ ≤ BW) :
    (∑u : Bool → (ZMod M)ˣ, ‖primeTest (weightedResidueTest g V outside h k M hd W) u‖) ≤
      BW*∑u : Bool → (ZMod M)ˣ, ‖primeResidueTest g V outside h k M hd u‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  rw [primeTest_weightedResidueTest,norm_mul]
  exact mul_le_mul_of_nonneg_right (hW _) (norm_nonneg _)

theorem sum_norm_mixedTest_weighted_le {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (M : ℕ) [NeZero M] (hd : pairModulus h k outside ∣ M)
    (W : ZMod M × ZMod M → ℂ) (BW : ℝ) (hW : ∀z, ‖W z‖ ≤ BW) :
    (∑r : ZMod M, ∑u : Unit → (ZMod M)ˣ,
      ‖mixedTest (weightedResidueTest g V outside h k M hd W) r u‖) ≤
      BW*∑r : ZMod M, ∑u : Unit → (ZMod M)ˣ,
        ‖mixedResidueTest g V outside h k M hd r u‖ := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro u hu
  rw [mixedTest_weightedResidueTest,norm_mul]
  exact mul_le_mul_of_nonneg_right (hW _) (norm_nonneg _)

@[simp] theorem weightedResidueTest_one {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (M : ℕ) (hd : pairModulus h k outside ∣ M) :
    weightedResidueTest g V outside h k M hd (fun _ => 1) =
      liftedResidueTest g V outside h k M hd := by
  funext z
  simp only [weightedResidueTest,one_mul]

@[simp] theorem periodicSourcePrimeMean_unweighted {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (hd : pairModulus h k outside ∣ M) (f : (Bool → ℝ) → ℂ) :
    periodicSourcePrimeMean G E hZ M (liftedResidueTest g V outside h k M hd) f =
      sourcePrimeMean g V outside h k G E hZ M hd f := rfl

@[simp] theorem periodicSourceMixedMean_unweighted {l : ℕ}
    (g : (q : ℕ) → ZMod q → ℂ) (V : ℕ → ℕ) (outside : List ℕ)
    (h k : History l) (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (M : ℕ) (hd : pairModulus h k outside ∣ M) (f : (Option Unit → ℝ) → ℂ) :
    periodicSourceMixedMean G E hZ M (liftedResidueTest g V outside h k M hd) f =
      sourceMixedMean g V outside h k G E hZ M hd f := rfl

end Ostmann.Arithmetic.HistoryGiantWeightedPriorReplacement

end

end OAI
