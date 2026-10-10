import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Descent.IdealMasks
import OAI.NumberTheory.DirichletL.Descent.SieveComposition

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_family_quadratic_hybrid_orientation :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal Eis) (cols : n → Ideal Eis),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (rows i) (primaryGenerator (cols j)) * a j‖ ^ 2) ≤
        C * (M * N) ^ ε * (M + N) * ∑ j, ‖a j‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  let B : Matrix n m ℂ := fun j i => quadraticRow (rows i) (primaryGenerator (cols j))
  have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm N M :=
    family_squared_norm_le cols rows hc hr N M hcols hrows
  have hBT : B.conjTranspose =
      (fun i j => quadraticRow (rows i) (primaryGenerator (cols j))) := by
    ext i j
    exact canonical_quadraticRow_star (rows i) (hrows i).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose a
  rw [FiniteSieveOperator.operator_conjTranspose_norm, hBT] at he
  have henergy : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply he.trans
  calc
    _ ≤ sieveNorm N M * ∑ j, ‖a j‖ ^ 2 := mul_le_mul_of_nonneg_right hB henergy
    _ ≤ (C * (N * M) ^ ε * (N + M)) * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hsharp N M hN hM) henergy
    _ = _ := by rw [mul_comm N M, add_comm N M]

theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows cols : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
        C * (K * X) ^ ε * (K + X) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro K X hK hX rows cols hrows hcols a
  have hf := squarefree_all_column_energy (fun J : cols => J.val) Subtype.val_injective X K
    (fun J => hcols J.val J.property) (fun J => a J.val)
  have hi (k : idealRange K) :
      (∑ J : cols, quadraticRow k.val (primaryGenerator J.val) * a J.val) =
        ∑ J ∈ cols, quadraticRow k.val (primaryGenerator J) * a J :=
    Finset.sum_coe_sort cols (fun J => quadraticRow k.val (primaryGenerator J) * a J)
  simp_rw [hi] at hf
  rw [Finset.sum_coe_sort (idealRange K)
    (fun k => ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hf
  have hr : rows ⊆ idealRange K := fun k hk => mem_idealRange.mpr (hrows k hk)
  have he : (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
      ∑ k ∈ idealRange K, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hr (by intro k _ _; exact sq_nonneg _)
  apply (he.trans hf).trans
  calc
    _ ≤ 4 * (C * (X * K) ^ ε * (X + K)) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsharp X K hX hK) (by norm_num)
    _ = _ := by rw [mul_comm X K, add_comm X K]; ring

theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquadratic⟩ := finite_family_quadratic_hybrid_orientation (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hquad (f : Ideal Eis → ℂ) :
      (∑ k ∈ rows, ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2) ≤
        (Cq * (K * X) ^ (ε / 2) * (K + X)) * ∑ J ∈ target, ‖f J‖ ^ 2 := by
    have he := hquadratic K X hK hX
      (fun k : rows => k.val) (fun J : target => J.val)
      Subtype.val_injective Subtype.val_injective
      (fun k => hrows k.val k.property) (fun J => ht J.val J.property)
      (fun J => f J.val)
    have hi (k : rows) :
        (∑ J : target, quadraticRow k.val (primaryGenerator J.val) * f J.val) =
        ∑ J ∈ target, quadraticRow k.val (primaryGenerator J) * f J :=
      Finset.sum_coe_sort target (fun J => quadraticRow k.val (primaryGenerator J) * f J)
    simp_rw [hi] at he
    rw [Finset.sum_coe_sort rows
      (fun k => ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2),
      Finset.sum_coe_sort target (fun J => ‖f J‖ ^ 2)] at he
    exact he
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (CanonicalQuadraticSieve.product_fiber_card pairs J (ht J hJ).1.1)).trans
    exact (hdiv J (ht J hJ).1.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber hquad
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
    (hrows : ∀ k ∈ rows, Admissible k) (B : Ideal Eis)
    (a : Ideal Eis × Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p) =
      quadraticRow k (primaryGenerator B) * ∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p := by
    simp only [primaryGenerator_mul,
      canonical_quadraticRow_argument_mul k (hrows k hk), Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one k _)

theorem quadratic_product_column_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end
end SevenEighths.InverseMoment

end OAI
