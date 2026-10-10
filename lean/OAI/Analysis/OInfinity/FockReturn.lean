import OAI.Analysis.OInfinity.FockCompression
import OAI.Analysis.PureInfiniteness.CuntzGramMap

namespace OAI

/-! # The return map for the finite Fock approximation

The two coefficient families have complementary level weights. Their
Gram maps have sum equal to the unit after normalization.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _
local instance fockReturnComplexScalars : SMulWithZero ℂ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℂ OInfinity _ _
    (@Module.toMulActionWithZero ℂ OInfinity _ _ inferInstance)
local instance : Module ℝ OInfinity := Module.complexToReal _
local instance : SMulWithZero ℝ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℝ OInfinity _ _
    (@Module.toMulActionWithZero ℝ OInfinity _ _ (Module.complexToReal _))

local instance (n : Type*) [Fintype n] : Module ℝ (CStarMatrix n n OInfinity) :=
  Module.complexToReal _
local instance (n : Type*) [Fintype n] : SMulZeroClass ℝ (CStarMatrix n n OInfinity) where
  smul r M := (r : ℂ) • M
  smul_zero r := by
    apply CStarMatrix.ext
    intro i j
    change (r : ℂ) • (0 : OInfinity) = 0
    exact fockReturnComplexScalars.smul_zero (r : ℂ)

def finiteFockAlgebraWord {N m : ℕ} (i : FiniteFockIndex N m) : OInfinity :=
  oInfinityPositiveWord N i.2

def finiteFockUnweightedCoefficient {N m : ℕ} (i : FiniteFockIndex N m) : OInfinity :=
  star (finiteFockAlgebraWord i)

def finiteFockWeightedCoefficient {N m : ℕ} (i : FiniteFockIndex N m) : OInfinity :=
  ((Real.sqrt ((m : ℝ) - i.1.val) : ℝ) : ℂ) •
    (oInfinityFiniteVacuum N * star (finiteFockAlgebraWord i))

def finiteFockCuntzFamily (N m : ℕ) (i : FiniteFockIndex N m) : OInfinity :=
  oInfinityIsometry (Fintype.equivFin (FiniteFockIndex N m) i).val

lemma finiteFockCuntzFamily_relations (N m : ℕ) (i j : FiniteFockIndex N m) :
    star (finiteFockCuntzFamily N m i) * finiteFockCuntzFamily N m j =
      if i = j then 1 else 0 := by
  unfold finiteFockCuntzFamily
  rw [oInfinityIsometry_relations]
  have he : (Fintype.equivFin (FiniteFockIndex N m) i).val =
      (Fintype.equivFin (FiniteFockIndex N m) j).val ↔ i = j := by
    rw [Fin.val_inj, Equiv.apply_eq_iff_eq]
  simp only [he]

lemma finiteFockWeightedCoefficient_square {N m : ℕ} (i : FiniteFockIndex N m) :
    star (finiteFockWeightedCoefficient i) * finiteFockWeightedCoefficient i =
      ((m : ℝ) - i.1.val) •
        (finiteFockAlgebraWord i * oInfinityFiniteVacuum N * star (finiteFockAlgebraWord i)) := by
  have hr : 0 ≤ (m : ℝ) - i.1.val := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ i.1.isLt))
  have hc : star ((Real.sqrt ((m : ℝ) - i.1.val) : ℝ) : ℂ) *
      ((Real.sqrt ((m : ℝ) - i.1.val) : ℝ) : ℂ) = (((m : ℝ) - i.1.val : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hr]
  unfold finiteFockWeightedCoefficient
  rw [star_smul, smul_mul_smul_comm, hc]
  have hx : star (oInfinityFiniteVacuum N * star (finiteFockAlgebraWord i)) *
      (oInfinityFiniteVacuum N * star (finiteFockAlgebraWord i)) =
      finiteFockAlgebraWord i * oInfinityFiniteVacuum N * star (finiteFockAlgebraWord i) := by
    rw [star_mul, star_star, oInfinityFiniteVacuum_star]
    calc
      _ = finiteFockAlgebraWord i *
          (oInfinityFiniteVacuum N * oInfinityFiniteVacuum N) *
          star (finiteFockAlgebraWord i) := by noncomm_ring
      _ = _ := by rw [oInfinityFiniteVacuum_idempotent]
  rw [hx]
  rfl

lemma finiteFockCoefficient_normalization (N m : ℕ) :
    (∑ i : FiniteFockIndex N m,
      star (finiteFockUnweightedCoefficient i) * finiteFockUnweightedCoefficient i) +
    (∑ i : FiniteFockIndex N m,
      star (finiteFockWeightedCoefficient i) * finiteFockWeightedCoefficient i) =
      ((m : ℝ) + 1) • (1 : OInfinity) := by
  simp only [finiteFockUnweightedCoefficient, star_star,
    finiteFockWeightedCoefficient_square, Fintype.sum_sigma,
    finiteFockAlgebraWord, ← Finset.smul_sum,
    oInfinityPositiveWord_sum_range, oInfinityPositiveWord_sum_vacuum]
  change (∑ k : Fin (m + 1), oInfinityLevel N k.val) +
    (∑ k : Fin (m + 1), ((m : ℝ) - k.val) • oInfinityLevelDifference N k.val) = _
  have hfin : (∑ k : Fin (m + 1), ((m : ℝ) - k.val) • oInfinityLevelDifference N k.val) =
      ∑ k ∈ Finset.range (m + 1), ((m : ℝ) - k) • oInfinityLevelDifference N k := by
    exact Fin.sum_univ_eq_sum_range (fun k => ((m : ℝ) - k) • oInfinityLevelDifference N k) (m + 1)
  rw [hfin, Fin.sum_univ_eq_sum_range]
  exact oInfinityLevel_weighted_sum N m

def oInfinityFockReturn (N m : ℕ) :
    CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) ℂ →L[ℂ] OInfinity :=
  (ContinuousLinearMap.lsmul ℂ ℂ (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ))).comp
    (cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
        finiteFockUnweightedCoefficient +
      cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
        finiteFockWeightedCoefficient)

lemma oInfinityFockReturn_one (N m : ℕ) : oInfinityFockReturn N m 1 = 1 := by
  change (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
    ((cuntzGramMap _ _ finiteFockUnweightedCoefficient) 1 +
      (cuntzGramMap _ _ finiteFockWeightedCoefficient) 1)) = 1
  rw [cuntzGramMap_one, cuntzGramMap_one, finiteFockCoefficient_normalization]
  change ((m : ℝ) + 1)⁻¹ • (((m : ℝ) + 1) • (1 : OInfinity)) = 1
  rw [smul_smul, inv_mul_cancel₀ (by positivity : (m : ℝ) + 1 ≠ 0), one_smul]

lemma oInfinityFockReturn_cp (N m : ℕ) : CompletelyPositive (oInfinityFockReturn N m) := by
  intro k X hX
  let G := cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
    finiteFockUnweightedCoefficient
  let H := cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
    finiteFockWeightedCoefficient
  have hG : 0 ≤ CStarMatrix.ofMatrix (fun i j => G (X i j)) :=
    cuntzGramMap_cp _ _ _ k X hX
  have hH : 0 ≤ CStarMatrix.ofMatrix (fun i j => H (X i j)) :=
    cuntzGramMap_cp _ _ _ k X hX
  have he : CStarMatrix.ofMatrix (fun i j => oInfinityFockReturn N m (X i j)) =
      (((m : ℝ) + 1)⁻¹) •
        (CStarMatrix.ofMatrix (fun i j => G (X i j)) +
          CStarMatrix.ofMatrix (fun i j => H (X i j))) := by
    apply CStarMatrix.ext
    intro i j
    rfl
  rw [he]
  exact smul_nonneg (inv_nonneg.mpr (by positivity)) (add_nonneg hG hH)

lemma oInfinityFockReturn_norm_le (N m : ℕ) : ‖oInfinityFockReturn N m‖ ≤ 1 :=
  completelyPositive_norm_le_of_unital (oInfinityFockReturn_cp N m)
    (oInfinityFockReturn_one N m)

end WeakPureInfiniteness

end

end OAI
