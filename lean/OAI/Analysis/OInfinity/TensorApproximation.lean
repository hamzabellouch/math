import OAI.Analysis.OInfinity.CPAP
import OAI.Analysis.OInfinity.TensorGram
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorCrossNorm

namespace OAI

/-! # The finite Fock approximations in arbitrary tensor completions

Pointwise convergence is independent of the C*-norm on the algebraic tensor
product.  The uniform compression bound is a separate step in proving
uniqueness of that norm.
-/

noncomputable section
open scoped CStarAlgebra TensorProduct
open Filter Topology

namespace WeakPureInfiniteness

private lemma linearMap_error_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (x y : V) :
    T (x + y) - (x + y) = (T x - x) + (T y - y) := by
  rw [T.map_add, add_sub_add_comm]

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _

lemma finiteFockCoefficient_norm_le (N m : ℕ) :
    ‖∑ i : FiniteFockIndex N m,
      star (finiteFockUnweightedCoefficient i) * finiteFockUnweightedCoefficient i‖ ≤ (m : ℝ) + 1 ∧
    ‖∑ i : FiniteFockIndex N m,
      star (finiteFockWeightedCoefficient i) * finiteFockWeightedCoefficient i‖ ≤ (m : ℝ) + 1 := by
  let x : OInfinity := ∑ i : FiniteFockIndex N m,
    star (finiteFockUnweightedCoefficient i) * finiteFockUnweightedCoefficient i
  let y : OInfinity := ∑ i : FiniteFockIndex N m,
    star (finiteFockWeightedCoefficient i) * finiteFockWeightedCoefficient i
  have hx : 0 ≤ x := Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hy : 0 ≤ y := Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have he : x + y = ((m : ℝ) + 1) • (1 : OInfinity) := finiteFockCoefficient_normalization N m
  have hn : ‖x + y‖ = (m : ℝ) + 1 := by
    rw [he]
    change ‖(((((m : ℝ) + 1) : ℝ) : ℂ)) • (1 : OInfinity)‖ = _
    rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  constructor
  · exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (le_add_of_nonneg_right hy) hx).trans_eq hn
  · exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (le_add_of_nonneg_left hx) hy).trans_eq hn

lemma oInfinityFockReturn_mem_adjoin (N m : ℕ)
    (M : CStarMatrix (FiniteFockIndex N m) (FiniteFockIndex N m) ℂ) :
    oInfinityFockReturn N m M ∈ StarAlgebra.adjoin ℂ (Set.range oInfinityIsometry) := by
  let S := StarAlgebra.adjoin ℂ (Set.range oInfinityIsometry)
  have hgen (i : ℕ) : oInfinityIsometry i ∈ S := StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩
  have hword (k : ℕ) (w : Fin k → Fin N) : oInfinityPositiveWord N w ∈ S := by
    induction k with
    | zero => exact S.one_mem
    | succ k ih => exact S.mul_mem (hgen _) (ih (Fin.tail w))
  have hlevel (k : ℕ) : oInfinityLevel N k ∈ S := by
    induction k with
    | zero => exact S.one_mem
    | succ k ih =>
      change (∑ i : Fin N, oInfinityIsometry i * oInfinityLevel N k *
        star (oInfinityIsometry i)) ∈ S
      exact S.sum_mem (fun i _ => S.mul_mem (S.mul_mem (hgen _) ih) (S.star_mem' (hgen _)))
  have hvac : oInfinityFiniteVacuum N ∈ S := S.sub_mem S.one_mem (hlevel 1)
  have hu (i : FiniteFockIndex N m) : finiteFockUnweightedCoefficient i ∈ S :=
    S.star_mem' (hword _ i.2)
  have hw (i : FiniteFockIndex N m) : finiteFockWeightedCoefficient i ∈ S :=
    S.smul_mem (S.mul_mem hvac (S.star_mem' (hword _ i.2))) _
  have hgram (c : FiniteFockIndex N m → OInfinity) (hc : ∀ i, c i ∈ S) :
      cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m) c M ∈ S := by
    rw [cuntzGramMap_apply]
    exact S.sum_mem (fun i _ => S.sum_mem (fun j _ =>
      S.smul_mem (S.mul_mem (S.star_mem' (hc i)) (hc j)) _))
  change (((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
    (cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockUnweightedCoefficient M +
     cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockWeightedCoefficient M)) ∈ S
  exact S.smul_mem (S.add_mem (hgram _ hu) (hgram _ hw)) _

lemma exists_oInfinityApproximation_polynomial (n : ℕ) (a : OInfinity) :
    ∃ c : List (ℕ × Bool) →₀ ℂ,
      cuntzPolynomial oInfinityIsometry c = oInfinityApproximationSequence n a := by
  apply exists_cuntzPolynomial_of_mem_adjoin
  exact oInfinityFockReturn_mem_adjoin n (n + 1) (oInfinityFockCompression n (n + 1) a)

theorem fockOperatorRepresentation_injective : Function.Injective fockOperatorRepresentation := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hcompression (N m : ℕ) : oInfinityFockCompression N m a = 0 := by
    ext i j
    rw [oInfinityFockCompression_apply, ha]
    simp
  have happ (n : ℕ) : oInfinityApproximationSequence n a = 0 := by
    change oInfinityFockReturn n (n + 1) (oInfinityFockCompression n (n + 1) a) = 0
    rw [hcompression, map_zero]
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp (oInfinityApproximationSequence_tendsto a)
  simp only [happ, zero_sub, norm_neg] at ht
  apply norm_eq_zero.mp
  exact tendsto_nhds_unique tendsto_const_nhds ht

variable {B : Type*} [CStarAlgebra B]

def oInfinityTensorApproximation (n : ℕ) :
    OInfinity ⊗[ℂ] B →ₗ[ℂ] OInfinity ⊗[ℂ] B :=
  TensorProduct.map (oInfinityApproximationSequence n).toLinearMap LinearMap.id

@[simp] lemma oInfinityTensorApproximation_tmul (n : ℕ) (a : OInfinity) (b : B) :
    oInfinityTensorApproximation n (a ⊗ₜ[ℂ] b) =
      oInfinityApproximationSequence n a ⊗ₜ[ℂ] b :=
  TensorProduct.map_tmul _ _ _ _

lemma oInfinityTensorApproximation_tmul_error
    (p : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B)) (n : ℕ) (a : OInfinity) (b : B) :
    p.toAlgebraNorm (oInfinityTensorApproximation n (a ⊗ₜ[ℂ] b) - a ⊗ₜ[ℂ] b) =
      ‖oInfinityApproximationSequence n a - a‖ * ‖b‖ := by
  rw [oInfinityTensorApproximation_tmul, ← TensorProduct.sub_tmul,
    NuclearUnitization.cstar_norm_tmul]

theorem oInfinityTensorApproximation_error_tendsto
    (p : Pureness.CStarAlgebraNorm (OInfinity ⊗[ℂ] B)) (x : OInfinity ⊗[ℂ] B) :
    Tendsto (fun n => p.toAlgebraNorm (oInfinityTensorApproximation n x - x)) atTop
      (𝓝 0) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simpa only [oInfinityTensorApproximation_tmul_error, zero_mul] using
      (tendsto_iff_norm_sub_tendsto_zero.mp (oInfinityApproximationSequence_tendsto a)).mul_const ‖b‖
  | add x y hx hy =>
    refine squeeze_zero
      (g := fun n => p.toAlgebraNorm (oInfinityTensorApproximation n x - x) +
        p.toAlgebraNorm (oInfinityTensorApproximation n y - y))
      (fun n => apply_nonneg p.toAlgebraNorm _) ?_ ?_
    · intro n
      have he := linearMap_error_add (oInfinityTensorApproximation n) x y
      exact (congrArg p.toAlgebraNorm he).trans_le (map_add_le_add p.toAlgebraNorm _ _)
    · simpa only [zero_add] using hx.add hy

end WeakPureInfiniteness

end

end OAI
