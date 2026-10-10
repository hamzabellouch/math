import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallPairTransform

namespace OAI

/-! # The actual small-kernel moment after the first finite rearrangement -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_principal_pair_reduction {n₁ n₂ D : ℕ}
    (hg : n₁.gcd n₂ = D) (c : ℕ) :
    (1 : DirichletCharacter ℂ (2 * (n₁ * n₂))) (c : ZMod (2 * (n₁ * n₂))) =
      (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel n₁ n₂ * D)))
        (c : ZMod (2 * (quadraticPairKernel n₁ n₂ * D))) := by
  rw [quadratic_principal_nat, quadratic_principal_nat,
    ← quadraticPairKernel_factor n₁ n₂, hg]
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  congr 1
  exact propext (by tauto)

theorem quadratic_pair_sum_gcd {R : Type*} [AddCommMonoid R] (N : ℕ) (F : ℕ × ℕ → R) :
    (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N), F z) =
      ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D, F z := by
  have hmaps (z : ℕ × ℕ)
      (hz : z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N)) :
      z.1.gcd z.2 ∈ Finset.Icc 1 N := by
    have hz₁ := (Finset.mem_product.mp hz).1
    have hr := Finset.mem_Icc.mp (Finset.mem_filter.mp hz₁).1
    exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ hr.1,
      (Nat.gcd_le_left _ hr.1).trans hr.2⟩
  exact (Finset.sum_fiberwise_of_maps_to hmaps F).symm

theorem quadratic_small_energy_pairs (M N K : ℕ) (v : ℕ → ℂ) :
    (quadraticSmallEnergy M N K v : ℂ) =
      ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        v z.1 * conj (v z.2) *
        ∑ m ∈ quadraticSmallKernelRange (3 * M) K,
          quadraticSieveWeight ((m : ℝ) / M) *
            (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
  unfold quadraticSmallEnergy
  push_cast
  simp_rw [quadraticTranspose_norm_sq_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro m _
  rw [quadraticSieveWeight_apply]
  ring

theorem quadratic_small_moment_transform {M : ℕ} (hM : 0 < M)
    (N K : ℕ) (v : ℕ → ℂ) :
    (quadraticSmallEnergy M N K v : ℂ) =
      ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
        v z.1 * conj (v z.2) *
        ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
          (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
            (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
              quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
  rw [quadratic_small_energy_pairs, quadratic_pair_sum_gcd]
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  obtain ⟨hz₁, hz₂⟩ := Finset.mem_product.mp hz
  rw [quadratic_small_pair_transform hM K (Finset.mem_filter.mp hz₁).2.2
    (Finset.mem_filter.mp hz₂).2.2, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [hg]
  have hs : (∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (z.1 * z.2)))
      (c : ZMod (2 * (z.1 * z.2))) * quadraticSieveWeight ((c : ℝ) ^ 2 * b / M)) =
      ∑' c : ℕ+, (1 : DirichletCharacter ℂ (2 * (quadraticPairKernel z.1 z.2 * D)))
        (c : ZMod (2 * (quadraticPairKernel z.1 z.2 * D))) *
          quadraticSieveWeight ((c : ℝ) ^ 2 * b / M) := by
    apply tsum_congr
    intro c
    rw [quadratic_principal_pair_reduction hg]
  rw [hs]
  by_cases hb : D.Coprime b
  · rw [ite_eq_left hb.symm, ite_eq_left hb, one_mul]
  · rw [ite_eq_right (fun h => hb h.symm), ite_eq_right hb, zero_mul, zero_mul]

end Ostmann

end OAI
