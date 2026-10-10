import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # The logarithm of a bounded probe section times a small generator -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {V E N J : Type*} [LieRing V] [LieAlgebra ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N] [T2Space N] [Fintype J]

/-- A two-factor Dynkin product multiplies the small exponential rate
only by its fixed degree. The remaining radius is subexponential. -/
theorem exists_sequence_small_product_bound
    (e : V ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N) (hExp : IsGroupExponential Exp)
    (dynkin : NilpotentDynkinExpansionInput E N)
    {c : ℕ} (hc : lowerCentralSeries ℝ V V c = ⊥) (b : Basis J ℝ V)
    (scale R₁ R₂ : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR₁0 : ∀ n, 0 ≤ R₁ n) (hR₂0 : ∀ n, 0 ≤ R₂ n)
    (hR₁ : HasSubexponentialUpperBoundSeq scale R₁)
    (hR₂ : HasSubexponentialUpperBoundSeq scale R₂) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n (δ : ℝ), 0 ≤ δ → ∀ x y : V,
        ‖b.equivFun x‖ ≤ R₁ n → ‖b.equivFun y‖ ≤ R₂ n * Real.exp (δ * scale n) →
        ∃ v : V, Exp (e v) = Exp (e x) * Exp (e y) ∧
          ‖b.equivFun v‖ ≤ R n * Real.exp ((c : ℝ) * δ * scale n) := by
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound b
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc 2
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * K) ^ c
  let R := fun n => A * (1 + (R₁ n + R₂ n)) ^ c * (1 + (2 : ℝ)) ^ c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbase0 : ∀ n, 0 ≤ 1 + (R₁ n + R₂ n) := fun n => by linarith [hR₁0 n, hR₂0 n]
  have hbase : HasSubexponentialUpperBoundSeq scale (fun n => 1 + (R₁ n + R₂ n)) :=
    (sequence_subexponential_upper_const hs 1).add (hR₁.add hR₂ hs) hs
  refine ⟨R, fun n => mul_nonneg (mul_nonneg hA (pow_nonneg (hbase0 n) _))
    (by positivity), ?_, ?_⟩
  · exact ((sequence_subexponential_upper_const hs A).mul
      (hbase.pow hs (Eventually.of_forall hbase0) c) (Eventually.of_forall (fun _ => hA))).mul
      (sequence_subexponential_upper_const hs ((1 + (2 : ℝ)) ^ c))
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (hbase0 n) _)))
  intro n δ hδ x y hx hy
  let t := Real.exp (δ * scale n)
  have ht : 1 ≤ t := Real.one_le_exp_iff.mpr (mul_nonneg hδ (hscale0 n))
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have hm0 : 0 ≤ (R₁ n + R₂ n) * t := mul_nonneg (add_nonneg (hR₁0 n) (hR₂0 n)) ht0
  have hxy : ∀ i : Fin 2, ‖b.equivFun (![x, y] i)‖ ≤ (R₁ n + R₂ n) * t := by
    intro i
    fin_cases i
    · apply hx.trans
      have h₁ : R₁ n ≤ R₁ n * t := le_mul_of_one_le_right (hR₁0 n) ht
      have h₂ : 0 ≤ R₂ n * t := mul_nonneg (hR₂0 n) ht0
      nlinarith
    · apply hy.trans
      have h₁ : 0 ≤ R₁ n * t := mul_nonneg (hR₁0 n) ht0
      change R₂ n * t ≤ _
      nlinarith
  refine ⟨finiteDynkinPolynomial coeff ![x, y], ?_, ?_⟩
  · simpa using (hprod ![x, y]).symm
  have hn := norm_finiteDynkinPolynomial_le b coeff hcoeff ![x, y] hK hm0 hbracket hxy
  have hp : (1 + (R₁ n + R₂ n) * t) ^ c ≤ ((1 + (R₁ n + R₂ n)) * t) ^ c := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ A * (1 + (R₁ n + R₂ n) * t) ^ c * (1 + (2 : ℝ)) ^ c := by simpa [A] using hn
    _ ≤ A * ((1 + (R₁ n + R₂ n)) * t) ^ c * (1 + (2 : ℝ)) ^ c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (by positivity)
    _ = _ := by
      dsimp [R, t]
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (c : ℝ) * (δ * scale n) = (c : ℝ) * δ * scale n by ring]
      ring

end PolycyclicRecognition

end

end OAI
