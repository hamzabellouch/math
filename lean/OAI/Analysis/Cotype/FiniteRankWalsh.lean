import OAI.Analysis.Cotype.VectorWalsh
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem cubeL2_smul_const {n : ℕ} (g : Cube n → ℝ) (y : Y) :
    cubeL2 Y (fun ε => g ε • y) = cubeL2 ℝ g * ‖y‖ := by
  apply (sq_eq_sq₀ (cubeL2_nonneg _) (mul_nonneg (cubeL2_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cubeL2_sq, cubeL2_sq]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, average, smul_eq_mul,
    ← Finset.sum_mul, mul_assoc]

theorem vectorWalsh_smul_const {n : ℕ} (g : Cube n → ℝ) (y : Y) :
    vectorWalsh (fun ε => g ε • y) = fun v => scalarWalsh g v • y := by
  funext v
  simp only [vectorWalsh, smul_smul, average_smul_const]
  congr 1
  simp only [scalarWalsh, fourier, mul_comm]

theorem vectorWalsh_finset_sum {n : ℕ} {α : Type*} (s : Finset α) (f : α → Cube n → Y) :
    vectorWalsh (fun ε => ∑ i ∈ s, f i ε) = fun v => ∑ i ∈ s, vectorWalsh (f i) v := by
  funext v
  simp only [vectorWalsh, average, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem finiteRank_expansion (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ (r : ℕ) (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y),
      ∀ x, T x = ∑ i, φ i x • y i := by
  let := hT
  let b := Module.finBasis ℝ (LinearMap.range T.toLinearMap)
  let R : X →L[ℝ] LinearMap.range T.toLinearMap :=
    T.codRestrict _ (fun x => ⟨x, rfl⟩)
  let φ := fun i => ((b.coord i).toContinuousLinearMap).comp R
  refine ⟨Module.finrank ℝ (LinearMap.range T.toLinearMap), φ, fun i => (b i : Y), ?_⟩
  intro x
  have he := congrArg (fun z : LinearMap.range T.toLinearMap => (z : Y)) (b.sum_repr (R x))
  change T x = ∑ i, b.repr (R x) i • (b i : Y)
  simpa [R] using he.symm

theorem operatorWalsh_expansion {r n : ℕ} (T : X →L[ℝ] Y)
    (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y)
    (hT : ∀ x, T x = ∑ i, φ i x • y i) (f : Cube n → X) :
    operatorWalsh T f = fun v => ∑ i, scalarWalsh (fun u => φ i (f u)) v • y i := by
  unfold operatorWalsh
  simp_rw [hT]
  rw [vectorWalsh_finset_sum]
  simp_rw [vectorWalsh_smul_const]

theorem finite_expansion_Walsh_bound {r n : ℕ} (T : X →L[ℝ] Y)
    (φ : Fin r → X →L[ℝ] ℝ) (y : Fin r → Y)
    (hT : ∀ x, T x = ∑ i, φ i x • y i) (f : Cube n → X) :
    cubeL2 Y (operatorWalsh T f) ≤
      (∑ i, ‖φ i‖ * ‖y i‖) * Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 X f := by
  rw [operatorWalsh_expansion T φ y hT f]
  apply (cubeL2_sum_le _ _).trans
  calc
    _ = ∑ i, (Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 ℝ (fun u => φ i (f u))) * ‖y i‖ := by
      simp_rw [cubeL2_smul_const, scalarWalsh_L2]
    _ ≤ ∑ i, (Real.sqrt ((2 : ℝ)⁻¹ ^ n) * (‖φ i‖ * cubeL2 X f)) * ‖y i‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cubeL2_clm (φ i) f) (Real.sqrt_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem finiteRank_Walsh_decay (T : X →L[ℝ] Y)
    (hT : FiniteDimensional ℝ (LinearMap.range T.toLinearMap)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (f : Cube n → X),
      cubeL2 Y (operatorWalsh T f) ≤ D * Real.sqrt ((2 : ℝ)⁻¹ ^ n) * cubeL2 X f := by
  obtain ⟨r, φ, y, he⟩ := finiteRank_expansion T hT
  exact ⟨∑ i, ‖φ i‖ * ‖y i‖, Finset.sum_nonneg (fun i _ => by positivity),
    fun _ f => finite_expansion_Walsh_bound T φ y he f⟩

end Cotype

end

end OAI
