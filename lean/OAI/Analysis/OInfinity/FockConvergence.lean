import OAI.Analysis.OInfinity.FockShift

namespace OAI

/-! # Error bounds for the finite Fock approximation of O∞ -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
open Filter Topology

namespace WeakPureInfiniteness

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _
local instance : DistribSMul ℂ OInfinity :=
  @DistribMulAction.toDistribSMul ℂ OInfinity _ _
    (@Module.toDistribMulAction ℂ OInfinity _ _ inferInstance)
local instance convergenceComplexScalars : SMulWithZero ℂ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℂ OInfinity _ _
    (@Module.toMulActionWithZero ℂ OInfinity _ _ inferInstance)
local instance : Algebra ℝ OInfinity := Algebra.compHom OInfinity Complex.ofRealHom
local instance : Module ℝ OInfinity := Module.complexToReal _
local instance : DistribSMul ℝ OInfinity :=
  @DistribMulAction.toDistribSMul ℝ OInfinity _ _
    (@Module.toDistribMulAction ℝ OInfinity _ _ (Module.complexToReal _))
local instance : SMulWithZero ℝ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℝ OInfinity _ _
    (@Module.toMulActionWithZero ℝ OInfinity _ _ (Module.complexToReal _))
local instance : SMulZeroClass ℝ OInfinity where
  smul r a := (r : ℂ) • a
  smul_zero r := convergenceComplexScalars.smul_zero (r : ℂ)

def fockGeneratorWeight (m k : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) - (k + 1)) * Real.sqrt ((m : ℝ) - k)

lemma fockGeneratorWeight_bounds {m k : ℕ} (hk : k < m) :
    (m : ℝ) - k - 1 ≤ fockGeneratorWeight m k ∧
      fockGeneratorWeight m k ≤ (m : ℝ) - k := by
  have hk' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.add_one_le_iff.mpr hk
  have ht : (1 : ℝ) ≤ (m : ℝ) - k := by linarith
  have h0 : 0 ≤ (m : ℝ) - (k + 1) := by linarith
  have h1 : 0 ≤ (m : ℝ) - k := by linarith
  have hs0 := Real.sq_sqrt h0
  have hs1 := Real.sq_sqrt h1
  have hp : 0 ≤ fockGeneratorWeight m k :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (fockGeneratorWeight m k) ^ 2 =
      ((m : ℝ) - (k + 1)) * ((m : ℝ) - k) := by
    unfold fockGeneratorWeight
    rw [mul_pow, hs0, hs1]
  constructor <;> nlinarith

lemma oInfinityLevelDifference_sum_before (N m : ℕ) :
    ∑ k ∈ Finset.range m, oInfinityLevelDifference N k = 1 - oInfinityLevel N m := by
  cases m with
  | zero => simp
  | succ m => exact oInfinityLevelDifference_sum N m

lemma weightedFockReturn_generator {N m : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockWeightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p)) =
      oInfinityIsometry p * ∑ k ∈ Finset.range m,
        (fockGeneratorWeight m k) • oInfinityLevelDifference N k := by
  rw [weightedFockReturn_generator_sum]
  simp only [Fintype.sum_sigma, finiteFockAlgebraWord]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, lt_self_iff_false, ite_false,
    Finset.sum_const_zero, add_zero]
  have hlevel (k : Fin m) : (∑ w : Fin k.val → Fin N,
      if k.val < m then
        (((Real.sqrt ((m : ℝ) - (k.val + 1)) * Real.sqrt ((m : ℝ) - k.val) : ℝ)) : ℂ) •
          (oInfinityIsometry p * oInfinityPositiveWord N w * oInfinityFiniteVacuum N *
            star (oInfinityPositiveWord N w)) else 0) =
      oInfinityIsometry p *
        ((fockGeneratorWeight m k.val) • oInfinityLevelDifference N k.val) := by
    simp only [ite_eq_left k.isLt, mul_assoc, ← Finset.smul_sum, ← Finset.mul_sum]
    rw [← mul_smul_comm]
    congr 1
    change (fockGeneratorWeight m k.val : ℂ) • _ = _
    rw [show (∑ w : Fin k.val → Fin N, oInfinityPositiveWord N w *
        (oInfinityFiniteVacuum N * star (oInfinityPositiveWord N w))) =
      oInfinityLevelDifference N k.val by
        simpa only [mul_assoc] using oInfinityPositiveWord_sum_vacuum N k.val]
    rfl
  simp only [hlevel, ← Finset.mul_sum]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun k => fockGeneratorWeight m k • oInfinityLevelDifference N k) m

def fockGeneratorError (N m : ℕ) : OInfinity :=
  oInfinityLevel N m + ∑ k ∈ Finset.range m,
    ((m : ℝ) - k - fockGeneratorWeight m k) • oInfinityLevelDifference N k

lemma fockGeneratorError_nonneg (N m : ℕ) : 0 ≤ fockGeneratorError N m := by
  apply add_nonneg (oInfinityLevel_nonneg N m)
  apply Finset.sum_nonneg
  intro k hk
  exact smul_nonneg (sub_nonneg.mpr (fockGeneratorWeight_bounds
    (Finset.mem_range.mp hk)).2) (oInfinityLevelDifference_nonneg N k)

lemma fockGeneratorError_le_one (N m : ℕ) : fockGeneratorError N m ≤ 1 := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range m,
      (1 - ((m : ℝ) - k - fockGeneratorWeight m k)) • oInfinityLevelDifference N k := by
    apply Finset.sum_nonneg
    intro k hk
    have hb := (fockGeneratorWeight_bounds (Finset.mem_range.mp hk)).1
    exact smul_nonneg (by linarith) (oInfinityLevelDifference_nonneg N k)
  have he : 1 - fockGeneratorError N m = ∑ k ∈ Finset.range m,
      (1 - ((m : ℝ) - k - fockGeneratorWeight m k)) • oInfinityLevelDifference N k := by
    calc
      _ = (1 - oInfinityLevel N m) - ∑ k ∈ Finset.range m,
          ((m : ℝ) - k - fockGeneratorWeight m k) • oInfinityLevelDifference N k := by
        unfold fockGeneratorError
        abel
      _ = (∑ k ∈ Finset.range m, oInfinityLevelDifference N k) - ∑ k ∈ Finset.range m,
          ((m : ℝ) - k - fockGeneratorWeight m k) • oInfinityLevelDifference N k := by
        rw [oInfinityLevelDifference_sum_before]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        module
  exact sub_nonneg.mp (he.symm ▸ hsum)

lemma fockGeneratorError_norm_le (N m : ℕ) : ‖fockGeneratorError N m‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (fockGeneratorError_nonneg N m)).mpr
    (fockGeneratorError_le_one N m)

lemma fockGenerator_normalization (N m : ℕ) :
    (∑ k ∈ Finset.range m, oInfinityLevel N k) +
      (∑ k ∈ Finset.range m, fockGeneratorWeight m k • oInfinityLevelDifference N k) +
        fockGeneratorError N m = ((m : ℝ) + 1) • (1 : OInfinity) := by
  have h := oInfinityLevel_weighted_sum N m
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
  simp only [sub_self, zero_smul, add_zero] at h
  rw [← h]
  unfold fockGeneratorError
  have hs : (∑ k ∈ Finset.range m, fockGeneratorWeight m k • oInfinityLevelDifference N k) +
      (∑ k ∈ Finset.range m,
        ((m : ℝ) - k - fockGeneratorWeight m k) • oInfinityLevelDifference N k) =
      ∑ k ∈ Finset.range m, ((m : ℝ) - k) • oInfinityLevelDifference N k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    module
  calc
    _ = ((∑ k ∈ Finset.range m, oInfinityLevel N k) + oInfinityLevel N m) +
        ((∑ k ∈ Finset.range m, fockGeneratorWeight m k • oInfinityLevelDifference N k) +
          ∑ k ∈ Finset.range m,
            ((m : ℝ) - k - fockGeneratorWeight m k) • oInfinityLevelDifference N k) := by abel
    _ = _ := by rw [hs]

def oInfinityFockApproximation (N m : ℕ) : OInfinity →L[ℂ] OInfinity :=
  (oInfinityFockReturn N m).comp (oInfinityFockCompression N m)

lemma oInfinityFockApproximation_one (N m : ℕ) :
    oInfinityFockApproximation N m 1 = 1 := by
  change oInfinityFockReturn N m (oInfinityFockCompression N m 1) = 1
  rw [oInfinityFockCompression_one, oInfinityFockReturn_one]

lemma oInfinityFockApproximation_cp (N m : ℕ) :
    CompletelyPositive (oInfinityFockApproximation N m) := by
  intro k X hX
  exact oInfinityFockReturn_cp N m k _ (oInfinityFockCompression_cp N m k X hX)

lemma oInfinityFockApproximation_norm_le (N m : ℕ) :
    ‖oInfinityFockApproximation N m‖ ≤ 1 :=
  completelyPositive_norm_le_of_unital (oInfinityFockApproximation_cp N m)
    (oInfinityFockApproximation_one N m)

private lemma sub_eq_neg_of_sum {G : Type*} [AddCommGroup G]
    (x y z : G) (h : x + y = z) : x - z = -y := by
  rw [← h]
  abel

lemma oInfinityFockApproximation_generator_error {N m : ℕ} (p : Fin N) :
    oInfinityFockApproximation N m (oInfinityIsometry p) - oInfinityIsometry p =
      -(((m : ℝ) + 1)⁻¹ • (oInfinityIsometry p * fockGeneratorError N m)) := by
  have hs :
      oInfinityIsometry p *
        ((∑ k ∈ Finset.range m, oInfinityLevel N k) +
          ∑ k ∈ Finset.range m, fockGeneratorWeight m k • oInfinityLevelDifference N k) +
      oInfinityIsometry p * fockGeneratorError N m =
        ((m : ℝ) + 1) • oInfinityIsometry p := by
    rw [← mul_add, fockGenerator_normalization, mul_smul_comm, mul_one]
  have ht := congrArg (fun a : OInfinity => ((m : ℝ) + 1)⁻¹ • a) hs
  rw [smul_add, smul_smul, inv_mul_cancel₀ (by positivity : (m : ℝ) + 1 ≠ 0), one_smul] at ht
  have he : oInfinityFockApproximation N m (oInfinityIsometry p) =
      ((m : ℝ) + 1)⁻¹ • (oInfinityIsometry p *
        ((∑ k ∈ Finset.range m, oInfinityLevel N k) +
          ∑ k ∈ Finset.range m, fockGeneratorWeight m k • oInfinityLevelDifference N k)) := by
    change (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ)) •
      (cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
          finiteFockUnweightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p)) +
        cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
          finiteFockWeightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p))) = _
    rw [unweightedFockReturn_generator, weightedFockReturn_generator, ← mul_add]
    rfl
  rw [he]
  exact sub_eq_neg_of_sum _ _ _ ht

lemma oInfinityFockApproximation_generator_norm_le {N m : ℕ} (p : Fin N) :
    ‖oInfinityFockApproximation N m (oInfinityIsometry p) - oInfinityIsometry p‖ ≤
      ((m : ℝ) + 1)⁻¹ := by
  have hp : ‖oInfinityIsometry p‖ ≤ 1 := by
    have h := congrArg norm (oInfinityIsometry_relations p p)
    simp only [ite_true, CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg (oInfinityIsometry p), cstar_norm_one_le_one (A := OInfinity)]
  rw [oInfinityFockApproximation_generator_error, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc
    _ ≤ ((m : ℝ) + 1)⁻¹ * (‖oInfinityIsometry p‖ * ‖fockGeneratorError N m‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
    _ ≤ ((m : ℝ) + 1)⁻¹ * (1 * 1) := by
      gcongr
      exact fockGeneratorError_norm_le N m
    _ = _ := by ring

lemma oInfinityFockApproximation_generator_tendsto {N : ℕ} (p : Fin N) :
    Tendsto (fun m => oInfinityFockApproximation N m (oInfinityIsometry p))
      atTop (𝓝 (oInfinityIsometry p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun m =>
    oInfinityFockApproximation_generator_norm_le (m := m) p)
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

end WeakPureInfiniteness

end

end OAI
