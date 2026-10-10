import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MemSobolevSum

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def product (n : ℕ) (g : 𝓢(E,ℂ)) : H E F n →L[ℂ] H E F n :=
  liftOperator (smulLeftCLM F g) (fun _ h =>
    EuclideanSobolevOperators.memSobolev_nat_product n g h)

lemma toDistribution_product (n : ℕ) (g : 𝓢(E,ℂ)) (u : H E F n) :
    toDistribution E F n (product n g u) = smulLeftCLM F g (toDistribution E F n u) :=
  toDistribution_liftOperator _ _ _

lemma product_inclusion (n : ℕ) (g : 𝓢(E,ℂ)) (u : H E F (n+1)) :
    inclusion (show (n:ℝ) ≤ n+1 by linarith) (product (n+1) g u) =
      product n g (inclusion (show (n:ℝ) ≤ n+1 by linarith) u) := by
  apply toDistribution_injective (n:ℝ)
  rw [toDistribution_inclusion, toDistribution_product, toDistribution_inclusion]
  simpa only [toDistribution, Nat.cast_add, Nat.cast_one] using toDistribution_product (n+1) g u

lemma product_derivative (n : ℕ) (g : 𝓢(E,ℂ)) (v : E) (u : H E F (n+1)) :
    derivative (n+1) v (product (n+1) g u) =
      product n (∂_{v} g) (inclusion (show (n:ℝ) ≤ n+1 by linarith) u) +
      product n g (derivative (n+1) v u) := by
  apply toDistribution_injective (n:ℝ)
  have he : (n:ℝ)+1-1 = n := by ring
  have hd (w : H E F (n+1)) :
      toDistribution E F n (derivative ((n:ℝ)+1) v w) =
        ∂_{v} (toDistribution E F ((n:ℝ)+1) w) := by
    have h := toDistribution_derivative ((n:ℝ)+1) v w
    rw [he] at h
    exact h
  have hp : toDistribution E F ((n:ℝ)+1) (product (n+1) g u) =
      smulLeftCLM F g (toDistribution E F ((n:ℝ)+1) u) := by
    simpa only [toDistribution, Nat.cast_add, Nat.cast_one] using toDistribution_product (n+1) g u
  rw [hd, hp, EuclideanSobolevOperators.distribution_derivative_product]
  rw [map_add, toDistribution_product, toDistribution_product,
    toDistribution_inclusion, hd]

lemma product_zero_eq (g : 𝓢(E,ℂ)) (u : H E F 0) :
    product 0 g u = (g.toBoundedContinuousFunction.memLp_top (μ := volume)).toLp g.toBoundedContinuousFunction • u := by
  apply toDistribution_injective 0
  have hp : toDistribution E F 0 (product 0 g u) =
      smulLeftCLM F g (toDistribution E F 0 u) := by
    simpa only [toDistribution, Nat.cast_zero] using toDistribution_product 0 g u
  rw [hp]
  simp only [toDistribution, neg_zero, besselPotential_zero,
    ContinuousLinearMap.id_comp]
  exact Lp.toTemperedDistribution_smul_eq g.hasTemperateGrowth
    (g.toBoundedContinuousFunction.memLp_top (μ := volume)) u |>.symm

lemma product_zero_norm_le (g : 𝓢(E,ℂ)) (u : H E F 0) :
    ‖product 0 g u‖ ≤ ‖g.toBoundedContinuousFunction‖ * ‖u‖ := by
  rw [product_zero_eq]
  apply (Lp.norm_smul_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact toLp_top_norm_le (g.toBoundedContinuousFunction.memLp_top (μ := volume))
    (norm_nonneg _) (fun x => g.toBoundedContinuousFunction.norm_coe_le_norm x)

def coefficientSize : ℕ → 𝓢(E,ℂ) → ℝ
  | 0, g => ‖g.toBoundedContinuousFunction‖
  | n+1, g => coefficientSize n g +
      ∑ i : basisIndex E, coefficientSize n (∂_{stdOrthonormalBasis ℝ E i} g)

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_nonneg (n : ℕ) (g : 𝓢(E,ℂ)) : 0 ≤ coefficientSize n g := by
  induction n generalizing g with
  | zero => exact norm_nonneg _
  | succ n ih => exact add_nonneg (ih g) (Finset.sum_nonneg (fun i _ => ih _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_le_succ (n : ℕ) (g : 𝓢(E,ℂ)) :
    coefficientSize n g ≤ coefficientSize (n+1) g := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => coefficientSize_nonneg n _))

omit [MeasurableSpace E] [BorelSpace E] in
lemma coefficientSize_derivative_le (n : ℕ) (g : 𝓢(E,ℂ)) (i : basisIndex E) :
    coefficientSize n (∂_{stdOrthonormalBasis ℝ E i} g) ≤ coefficientSize (n+1) g := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : basisIndex E => coefficientSize n (∂_{stdOrthonormalBasis ℝ E j} g))
    (fun j _ => coefficientSize_nonneg n _) (Finset.mem_univ i)
  exact h.trans (le_add_of_nonneg_left (coefficientSize_nonneg n g))

theorem product_estimate (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (g : 𝓢(E,ℂ)) (u : H E F n),
      ‖product n g u‖ ≤ C * coefficientSize n g * ‖u‖ := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, fun g u => ?_⟩
    simpa only [one_mul, coefficientSize] using product_zero_norm_le g u
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let c : ℝ := |((2*Real.pi)^2)⁻¹|
    let D (i : basisIndex E) : ℝ := ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖
    let D' (i : basisIndex E) : ℝ := ‖derivative (F := F) ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i)‖
    let K : ℝ := 1 + c * ∑ i, D i * (1 + D' i)
    have hc : 0 ≤ c := abs_nonneg _
    have hD (i) : 0 ≤ D i := norm_nonneg _
    have hD' (i) : 0 ≤ D' i := norm_nonneg _
    have hK : 0 < K := by
      dsimp only [K]
      positivity
    refine ⟨C*K, mul_pos hC hK, fun g u => ?_⟩
    let S := coefficientSize (n+1) g
    let A := C * S * ‖u‖
    have hS : 0 ≤ S := coefficientSize_nonneg _ _
    have hB (f : 𝓢(E,ℂ)) (hf : coefficientSize n f ≤ S) (w : H E F n) :
        ‖product n f w‖ ≤ C*S*‖w‖ :=
      (hbound f w).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf hC.le) (norm_nonneg w))
    have hu0 : ‖inclusion (show (n:ℝ) ≤ n+1 by linarith) u‖ ≤ ‖u‖ :=
      inclusion_norm_le (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ))
        (show (n:ℝ) ≤ n+1 by linarith) u
    have hz : ‖inclusion (show (n:ℝ) ≤ n+1 by linarith) (product (n+1) g u)‖ ≤ A := by
      rw [product_inclusion]
      exact (hB g (coefficientSize_le_succ n g) _).trans
        (mul_le_mul_of_nonneg_left hu0 (mul_nonneg hC.le hS))
    have hd (i : basisIndex E) :
        ‖derivative ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i) (product (n+1) g u)‖ ≤
          A * (1 + D' i) := by
      rw [product_derivative]
      have h1 := (hB (∂_{stdOrthonormalBasis ℝ E i} g)
        (coefficientSize_derivative_le n g i) _).trans
        (mul_le_mul_of_nonneg_left hu0 (mul_nonneg hC.le hS))
      have h2 := (hB g (coefficientSize_le_succ n g)
        (derivative ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i) u)).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ u)
          (mul_nonneg hC.le hS))
      apply (norm_add_le _ _).trans
      calc
        _ ≤ A + C*S*(D' i*‖u‖) := add_le_add h1 h2
        _ = A*(1+D' i) := by dsimp only [A]; ring
    have hn := norm_le_gradient (n:ℝ) (product (n+1) g u)
    apply hn.trans
    calc
      _ ≤ A + c * ∑ i, D i * (A * (1+D' i)) :=
        add_le_add hz (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hD i))) hc)
      _ = (C*K)*S*‖u‖ := by
        have he : (∑ i, D i * (A * (1+D' i))) = A * ∑ i, D i * (1+D' i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [he]
        dsimp only [A, K]
        ring

theorem product_operator_estimate (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ g : 𝓢(E,ℂ), ‖product (F := F) n g‖ ≤ C * coefficientSize n g := by
  obtain ⟨C, hC, h⟩ := product_estimate (E := E) (F := F) n
  refine ⟨C, hC, fun g => ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC.le (coefficientSize_nonneg n g)) (h g)

end TamingCompatibility.HilbertSobolev

end

end OAI
