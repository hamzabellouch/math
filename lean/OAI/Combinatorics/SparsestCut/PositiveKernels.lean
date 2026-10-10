import OAI.Combinatorics.SparsestCut.RoundedCharts

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut
namespace TriangleRepair

variable {ι : Type u1} [Fintype ι]

lemma gram_posSemidef {H : Type u2} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ι → H) : (Matrix.of (fun i j => ⟪x i, x j⟫_ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [real_inner_comm]
  · intro c
    have h := real_inner_self_nonneg (x := ∑ i, c i • x i)
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right] at h
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Finset.mul_sum, Pi.star_apply,
      star_trivial]
    convert h using 1
    try rfl
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (x j) (x i)]
    ring

lemma ones_posSemidef : (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)) using 1
  ext i j
  change (1 : ℝ) = 1 * 1
  ring

lemma entrywise_pow_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => (A i j) ^ k) := by
  induction k with
  | zero => convert (ones_posSemidef (ι := ι)) using 1; rfl
  | succ k hk => convert hk.hadamard hA using 1; rfl

omit [Fintype ι] in
lemma sum_posSemidef {κ : Type u3} (s : Finset κ) (A : κ → Matrix ι ι ℝ)
    (hA : ∀ k ∈ s, (A k).PosSemidef) : (∑ k ∈ s, A k).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | @insert a s ha hs =>
    rw [Finset.sum_insert ha]
    exact (hA a (Finset.mem_insert_self a s)).add
      (hs (fun k hk => hA k (Finset.mem_insert_of_mem hk)))

lemma posSemidef_of_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (ha : ∀ k, (A k).PosSemidef)
    (hab : ∀ i j, Tendsto (fun k => A k i j) atTop (nhds (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply tendsto_nhds_unique (hab j i)
    have heq : (fun k => A k j i) = (fun k => A k i j) := by
      funext k
      simpa using (ha k).isHermitian.apply i j
    simpa [heq] using hab i j
  · intro c
    have ht : Tendsto (fun k => star c ⬝ᵥ (A k *ᵥ c)) atTop
        (nhds (star c ⬝ᵥ (B *ᵥ c))) := by
      simp only [dotProduct, Matrix.mulVec]
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hab i j).mul tendsto_const_nhds)
    exact ge_of_tendsto' ht (fun k => (ha k).dotProduct_mulVec_nonneg c)

lemma entrywise_exp_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => Real.exp (A i j)) := by
  let P (k : ℕ) : Matrix ι ι ℝ := fun i j => A i j ^ k / (k.factorial : ℝ)
  have hp (k : ℕ) : (P k).PosSemidef := by
    have h := (entrywise_pow_posSemidef hA k).smul
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) k.factorial))
    convert h using 1
    ext i j
    change A i j ^ k / (k.factorial : ℝ) = (k.factorial : ℝ)⁻¹ * A i j ^ k
    exact div_eq_inv_mul _ _
  apply posSemidef_of_tendsto (A := fun k => ∑ l ∈ Finset.range k, P l)
    (fun k => sum_posSemidef _ _ (fun l _ => hp l))
  intro i j
  have h := (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  convert h using 1
  · funext k
    exact Matrix.sum_apply i j (Finset.range k) P
  · rw [Real.exp_eq_exp_ℝ]

lemma gaussian_posSemidef {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : ι → H) {l : ℝ} (hl : 0 < l) :
    Matrix.PosSemidef (fun i j => Real.exp (-‖x i - x j‖ ^ 2 / l)) := by
  let a : ι → ℝ := fun i => Real.exp (-‖x i‖ ^ 2 / l)
  have hgram := (gram_posSemidef x).smul (show 0 ≤ 2 / l by positivity)
  have hexp := entrywise_exp_posSemidef hgram
  have hrank := Matrix.posSemidef_vecMulVec_self_star a
  have heq : (fun i j => Real.exp (-‖x i - x j‖ ^ 2 / l) : Matrix ι ι ℝ) =
      Matrix.vecMulVec a (star a) ⊙ (fun i j => Real.exp ((2 / l) * ⟪x i, x j⟫_ℝ)) := by
    ext i j
    change Real.exp (-‖x i - x j‖ ^ 2 / l) =
      (a i * a j) * Real.exp ((2 / l) * ⟪x i, x j⟫_ℝ)
    simp only [a, ← Real.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    ring
  rw [heq]
  convert hrank.hadamard hexp using 1
  rfl

open MeasureTheory

lemma integral_posSemidef (K : ℝ → Matrix ι ι ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hK : ∀ l ∈ Set.Icc 0 r, (K l).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun l => K l i j) volume 0 r) :
    Matrix.PosSemidef (fun i j => ∫ l in (0 : ℝ)..r, K l i j) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply intervalIntegral.integral_congr
    intro l hl
    simpa using (hK l (by simpa [Set.uIcc_of_le hr] using hl)).isHermitian.apply i j
  · intro c
    have h : 0 ≤ ∫ l in (0 : ℝ)..r, star c ⬝ᵥ (K l *ᵥ c) :=
      intervalIntegral.integral_nonneg hr (fun l hl => (hK l hl).dotProduct_mulVec_nonneg c)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial] at h ⊢
    have hrow (i : ι) : IntervalIntegrable
        (fun l => ∑ j, K l i j * c j) volume 0 r := by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => (hi i j).mul_const (c j)) using 1
      try rfl
      funext l
      simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hrow i).const_mul (c i))] at h
    simp_rw [intervalIntegral.integral_const_mul] at h
    simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (hi _ j).mul_const (c j)),
      intervalIntegral.integral_mul_const] at h
    exact h

open scoped MatrixOrder in

lemma exists_gram {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ q : ι → EuclideanSpace ℝ ι, ∀ i j, ⟪q i, q j⟫_ℝ = A i j := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun i => WithLp.toLp 2 (fun k => B k i), ?_⟩
  intro i j
  rw [hB]
  simp [PiLp.inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose, mul_comm]

end TriangleRepair
end UniformSparsestCut

end

end OAI
