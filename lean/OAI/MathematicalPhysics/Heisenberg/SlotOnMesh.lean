import OAI.MathematicalPhysics.Heisenberg.MeshCompletion

namespace OAI

noncomputable section

open scoped Classical
namespace Heisenberg.SpinSlots
abbrev Config (ℓ : ℕ) := Finset (Fin ℓ)
abbrev Level (ℓ : ℕ) := Fin (ℓ+1)

def basis (ℓ : ℕ) : Matrix (Config ℓ) (Level ℓ) ℝ :=
  fun A k => if A.card = k.val then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0

lemma config_card_le (ℓ : ℕ) (A : Config ℓ) : A.card ≤ ℓ := by
  simpa using Finset.card_le_univ A

lemma multiplicity_pos (ℓ : ℕ) (k : Level ℓ) : 0 < (ℓ.choose k.val : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : k.val ≤ ℓ)

lemma sqrt_multiplicity_pos (ℓ : ℕ) (k : Level ℓ) : 0 < Real.sqrt (ℓ.choose k.val) :=
  Real.sqrt_pos.mpr (multiplicity_pos ℓ k)

lemma basis_nonneg (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) : 0 ≤ basis ℓ A k := by
  unfold basis
  split_ifs <;> positivity

lemma card_layer (ℓ k : ℕ) :
    (Finset.univ.filter (fun A : Config ℓ => A.card = k)).card = ℓ.choose k := by
  have he : Finset.univ.filter (fun A : Config ℓ => A.card = k) =
      (Finset.univ : Finset (Fin ℓ)).powersetCard k := by
    ext A
    simp
  rw [he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem basis_orthonormal (ℓ : ℕ) : (basis ℓ).transpose * basis ℓ = 1 := by
  ext k m
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  by_cases hkm : k = m
  · subst m
    have he : ∑ A : Config ℓ, basis ℓ A k * basis ℓ A k =
      ((ℓ.choose k.val : ℝ)) / (Real.sqrt (ℓ.choose k.val))^2 := by
      calc
        _ = ∑ A ∈ (Finset.univ.filter (fun A : Config ℓ => A.card = k.val)),
            (Real.sqrt (ℓ.choose k.val))⁻¹ * (Real.sqrt (ℓ.choose k.val))⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro A _
          by_cases hk : A.card = k.val <;> simp [basis,hk]
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul,card_layer]
          ring
    rw [he,Real.sq_sqrt (multiplicity_pos ℓ k).le]
    simp [ne_of_gt (multiplicity_pos ℓ k)]
  · rw [Matrix.one_apply_ne hkm]
    apply Finset.sum_eq_zero
    intro A _
    by_cases hk : A.card = k.val
    · have hm : A.card ≠ m.val := fun hm => hkm (Fin.ext (hk.symm.trans hm))
      simp [basis,hm]
    · simp [basis,hk]

def raising (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  fun A B => ∑ j ∈ A, if B = A.erase j then 1 else 0

def diagonalZ (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  Matrix.diagonal (fun A => (A.card : ℝ) - (ℓ : ℝ)/2)

def physicalZ (ℓ : ℕ) : Matrix (Level ℓ) (Level ℓ) ℝ :=
  Matrix.diagonal (fun k => (k.val : ℝ) - (ℓ : ℝ)/2)

def physicalPlus (ℓ : ℕ) : Matrix (Level ℓ) (Level ℓ) ℝ :=
  fun m k => if m.val = k.val+1 then Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) else 0

lemma raising_mul_basis (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    (raising ℓ * basis ℓ) A k = ∑ j ∈ A, basis ℓ (A.erase j) k := by
  simp only [Matrix.mul_apply,raising,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

lemma binomial_raising_coefficient (ℓ : ℕ) (k : Fin ℓ) :
    ((k.val+1 : ℕ) : ℝ) * (Real.sqrt (ℓ.choose k.val))⁻¹ =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * (Real.sqrt (ℓ.choose (k.val+1)))⁻¹ := by
  have hA := multiplicity_pos ℓ k.castSucc
  have hB := multiplicity_pos ℓ k.succ
  have ha := sqrt_multiplicity_pos ℓ k.castSucc
  have hb := sqrt_multiplicity_pos ℓ k.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hA hB ha hb
  have he : ((ℓ.choose (k.val+1) : ℝ)) * (k.val+1) =
      (ℓ.choose k.val : ℝ) * (ℓ-k.val : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq ℓ k.val
  have hc : 0 ≤ (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by positivity
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsqC := Real.sq_sqrt hc
  have he' : ((k.val+1 : ℕ) : ℝ) * Real.sqrt (ℓ.choose (k.val+1)) =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * Real.sqrt (ℓ.choose k.val) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hsqB,hsqC,hsqA]
    push_cast
    nlinarith [he]
  simpa only [div_eq_mul_inv] using (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)).mpr he'

lemma raising_coefficient_source (ℓ : ℕ) (k : Fin ℓ) :
    ((ℓ-k.val : ℕ) : ℝ)*(k.val+1) =
      (ℓ/2 : ℝ)*(ℓ/2+1) - ((k.val : ℝ)-ℓ/2)*((k.val : ℝ)-ℓ/2+1) := by
  rw [Nat.cast_sub (Nat.le_of_lt k.isLt)]
  ring

lemma raising_basis_entry (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    (raising ℓ * basis ℓ) A k =
      if A.card = k.val+1 then (A.card : ℝ) * (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
  rw [raising_mul_basis]
  have he : ∀ j ∈ A, basis ℓ (A.erase j) k =
      if A.card = k.val+1 then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
    intro j hj
    have hcard := Finset.card_pos.mpr ⟨j,hj⟩
    simp only [basis,Finset.card_erase_of_mem hj]
    have hi : (A.card-1=k.val) ↔ (A.card=k.val+1) := by omega
    simp only [hi]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul]
  split_ifs <;> simp

theorem diagonal_intertwines (ℓ : ℕ) : diagonalZ ℓ * basis ℓ = basis ℓ * physicalZ ℓ := by
  ext A k
  simp only [diagonalZ,physicalZ,Matrix.diagonal_mul,Matrix.mul_diagonal]
  by_cases h : A.card = k.val <;> simp [basis,h,mul_comm]

theorem raising_intertwines (ℓ : ℕ) : raising ℓ * basis ℓ = basis ℓ * physicalPlus ℓ := by
  ext A k
  rw [raising_basis_entry]
  by_cases hk : k.val < ℓ
  · let j : Fin ℓ := ⟨k.val,hk⟩
    have he : (basis ℓ * physicalPlus ℓ) A k =
        basis ℓ A j.succ * Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j.succ]
      · simp [physicalPlus,j]
      · intro m hm hmj
        have hne : m.val ≠ k.val+1 := fun h => hmj (Fin.ext h)
        simp [physicalPlus,hne]
      · simp
    rw [he]
    by_cases hA : A.card = k.val+1
    · simpa [basis,hA,j,mul_comm] using binomial_raising_coefficient ℓ j
    · simp [basis,hA,j]
  · have htop : k.val = ℓ := by omega
    have hA : A.card ≠ k.val+1 := by have := config_card_le ℓ A; omega
    rw [ite_eq_right hA,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro m _
    have hm : m.val ≠ k.val+1 := by omega
    simp [physicalPlus,hm]

def average (ℓ : ℕ) : Matrix (Config ℓ) (Config ℓ) ℝ :=
  fun A B => (Fintype.card (Equiv.Perm (Fin ℓ)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin ℓ), if A = B.map σ.toEmbedding then 1 else 0

lemma map_mul (ℓ : ℕ) (A : Config ℓ) (σ τ : Equiv.Perm (Fin ℓ)) :
    A.map (σ*τ).toEmbedding = (A.map τ.toEmbedding).map σ.toEmbedding := by
  rw [Finset.map_map]
  rfl

lemma average_map_left (ℓ : ℕ) (A B : Config ℓ) (τ : Equiv.Perm (Fin ℓ)) :
    average ℓ (A.map τ.toEmbedding) B = average ℓ A B := by
  unfold average
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
  apply Finset.sum_congr rfl
  intro σ _
  change (if A.map τ.toEmbedding = B.map (τ*σ).toEmbedding then (1 : ℝ) else 0) = _
  rw [map_mul]
  simp only [(Finset.map_injective τ.toEmbedding).eq_iff]

lemma average_column_sum (ℓ : ℕ) (B : Config ℓ) : ∑ A, average ℓ A B = 1 := by
  have hp : (Fintype.card (Equiv.Perm (Fin ℓ)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp [hp]

lemma average_eq_zero (ℓ : ℕ) (A B : Config ℓ) (h : A.card ≠ B.card) :
    average ℓ A B = 0 := by
  unfold average
  have hn : ∀ σ : Equiv.Perm (Fin ℓ), A ≠ B.map σ.toEmbedding := by
    intro σ he
    exact h (by rw [he,Finset.card_map])
  simp [hn]

lemma average_eq_diagonal (ℓ : ℕ) (A B : Config ℓ) (h : A.card = B.card) :
    average ℓ A B = average ℓ B B := by
  obtain ⟨τ,hτ⟩ := Equiv.Perm.exists_map_finset_eq B A h.symm
  rw [← hτ,average_map_left]

lemma average_diagonal (ℓ : ℕ) (B : Config ℓ) :
    average ℓ B B = (ℓ.choose B.card : ℝ)⁻¹ := by
  have hp : (ℓ.choose B.card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Nat.choose_pos (config_card_le ℓ B))
  have he := average_column_sum ℓ B
  have hf : ∑ A, average ℓ A B =
      (ℓ.choose B.card : ℝ) * average ℓ B B := by
    calc
      _ = ∑ A : Config ℓ, if A.card = B.card then average ℓ B B else 0 := by
        apply Finset.sum_congr rfl
        intro A _
        by_cases h : A.card = B.card
        · rw [ite_eq_left h,average_eq_diagonal ℓ A B h]
        · rw [ite_eq_right h,average_eq_zero ℓ A B h]
      _ = _ := by rw [← Finset.sum_filter]; simp
  rw [hf] at he
  simpa only [one_div] using (eq_div_iff hp).mpr (show average ℓ B B * (ℓ.choose B.card : ℝ) = 1 by simpa [mul_comm] using he)

theorem average_entry (ℓ : ℕ) (A B : Config ℓ) :
    average ℓ A B = if A.card = B.card then (ℓ.choose B.card : ℝ)⁻¹ else 0 := by
  split_ifs with h
  · rw [average_eq_diagonal ℓ A B h,average_diagonal]
  · exact average_eq_zero ℓ A B h

lemma basis_projection_entry (ℓ : ℕ) (A B : Config ℓ) :
    (basis ℓ * (basis ℓ).transpose) A B =
      if A.card = B.card then (ℓ.choose B.card : ℝ)⁻¹ else 0 := by
  let k : Level ℓ := ⟨B.card,by have := config_card_le ℓ B; omega⟩
  have he : (basis ℓ * (basis ℓ).transpose) A B = basis ℓ A k * basis ℓ B k := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    apply Finset.sum_eq_single k
    · intro m hm hmk
      have hne : B.card ≠ m.val := fun h => hmk (Fin.ext h.symm)
      simp [basis,hne]
    · simp
  rw [he]
  have hp : 0 ≤ (ℓ.choose B.card : ℝ) := by positivity
  by_cases h : A.card = B.card
  · simp only [basis,k,h,ite_true]
    rw [← mul_inv_rev,← sq,Real.sq_sqrt hp]
  · simp [basis,k,h]

theorem symmetrizer (ℓ : ℕ) : average ℓ = basis ℓ * (basis ℓ).transpose := by
  ext A B
  rw [average_entry,basis_projection_entry]

lemma erase_relation (ℓ : ℕ) (A B : Config ℓ) (j : Fin ℓ) :
    (j ∈ B ∧ A = B.erase j) ↔ (j ∉ A ∧ B = insert j A) := by
  constructor
  · rintro ⟨hj,rfl⟩
    exact ⟨by simp,(Finset.insert_erase hj).symm⟩
  · rintro ⟨hj,rfl⟩
    exact ⟨Finset.mem_insert_self _ _,(Finset.erase_insert hj).symm⟩

lemma lowering_entry (ℓ : ℕ) (A B : Config ℓ) :
    (raising ℓ).transpose A B = ∑ j ∈ (Finset.univ \ A), if B = insert j A then 1 else 0 := by
  simp only [Matrix.transpose_apply,raising]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact erase_relation ℓ A B j
  · intro j hj
    rfl

lemma lowering_mul_basis (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    ((raising ℓ).transpose * basis ℓ) A k =
      ∑ j ∈ (Finset.univ \ A), basis ℓ (insert j A) k := by
  simp only [Matrix.mul_apply,lowering_entry,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma lowering_basis_entry (ℓ : ℕ) (A : Config ℓ) (k : Level ℓ) :
    ((raising ℓ).transpose * basis ℓ) A k =
      if A.card+1 = k.val then ((ℓ-A.card : ℕ) : ℝ) *
        (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
  rw [lowering_mul_basis]
  have he : ∀ j ∈ (Finset.univ \ A), basis ℓ (insert j A) k =
      if A.card+1 = k.val then (Real.sqrt (ℓ.choose k.val))⁻¹ else 0 := by
    intro j hj
    simp only [basis,Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hj).2]
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_sdiff,Finset.inter_univ,
    Finset.card_univ,Fintype.card_fin]
  split_ifs <;> simp

lemma binomial_lowering_coefficient (ℓ : ℕ) (k : Fin ℓ) :
    ((ℓ-k.val : ℕ) : ℝ) * (Real.sqrt (ℓ.choose (k.val+1)))⁻¹ =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * (Real.sqrt (ℓ.choose k.val))⁻¹ := by
  have hA := multiplicity_pos ℓ k.castSucc
  have hB := multiplicity_pos ℓ k.succ
  have ha := sqrt_multiplicity_pos ℓ k.castSucc
  have hb := sqrt_multiplicity_pos ℓ k.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hA hB ha hb
  have he : ((ℓ.choose (k.val+1) : ℝ)) * (k.val+1) =
      (ℓ.choose k.val : ℝ) * (ℓ-k.val : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq ℓ k.val
  have hc : 0 ≤ (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) := by positivity
  have hsqA := Real.sq_sqrt hA.le
  have hsqB := Real.sq_sqrt hB.le
  have hsqC := Real.sq_sqrt hc
  have he' : ((ℓ-k.val : ℕ) : ℝ) * Real.sqrt (ℓ.choose k.val) =
      Real.sqrt (((ℓ-k.val : ℕ) : ℝ)*(k.val+1)) * Real.sqrt (ℓ.choose (k.val+1)) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,hsqA,hsqC,hsqB]
    nlinarith [he]
  simpa only [div_eq_mul_inv] using (div_eq_div_iff (ne_of_gt hb) (ne_of_gt ha)).mpr he'

theorem lowering_intertwines (ℓ : ℕ) :
    (raising ℓ).transpose * basis ℓ = basis ℓ * (physicalPlus ℓ).transpose := by
  ext A k
  rw [lowering_basis_entry]
  by_cases hk : 0 < k.val
  · let j : Fin ℓ := ⟨k.val-1,by omega⟩
    have hjs : j.val+1 = k.val := by dsimp [j]; omega
    have he : (basis ℓ * (physicalPlus ℓ).transpose) A k =
        basis ℓ A j.castSucc * Real.sqrt (((ℓ-j.val : ℕ) : ℝ)*(j.val+1)) := by
      rw [Matrix.mul_apply,Finset.sum_eq_single j.castSucc]
      · simp [physicalPlus,hjs]
      · intro m hm hmj
        have hne : k.val ≠ m.val+1 := by
          intro h
          apply hmj
          apply Fin.ext
          dsimp [j]
          omega
        simp [physicalPlus,hne]
      · simp
    rw [he]
    by_cases hA : A.card+1 = k.val
    · have hAj : A.card = j.val := by omega
      simpa [basis,hAj,← hjs,mul_comm] using binomial_lowering_coefficient ℓ j
    · have hAj : A.card ≠ j.val := by omega
      simp [basis,hA,hAj]
  · have hzero : k.val = 0 := by omega
    have hA : A.card+1 ≠ k.val := by omega
    rw [ite_eq_right hA,Matrix.mul_apply]
    symm
    apply Finset.sum_eq_zero
    intro m _
    have hm : k.val ≠ m.val+1 := by omega
    simp [physicalPlus,hm]

end Heisenberg.SpinSlots

open scoped Classical BigOperators
namespace Heisenberg.TensorMatrix
variable {X α β γ R : Type*} [Fintype X] [DecidableEq X] [CommSemiring R]

def tensor (M : X → Matrix α β R) : Matrix (X → α) (X → β) R :=
  fun a b => ∏ x, M x (a x) (b x)

lemma tensor_mul [Fintype β] (M : X → Matrix α β R) (N : X → Matrix β γ R) :
    tensor M * tensor N = tensor (fun x => M x * N x) := by
  ext a b
  simp only [Matrix.mul_apply,tensor,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun x y => M x (a x) y * N x y (b x)).symm

omit [DecidableEq X] in
lemma tensor_one [DecidableEq α] : tensor (fun _ : X => (1 : Matrix α α R)) = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [tensor]
  · obtain ⟨x,hx⟩ := Function.ne_iff.mp h
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    exact Matrix.one_apply_ne hx

omit [DecidableEq X] in
lemma tensor_transpose (M : X → Matrix α β R) :
    (tensor M).transpose = tensor (fun x => (M x).transpose) := rfl

lemma tensor_trace [Fintype α] (M : X → Matrix α α R) :
    Matrix.trace (tensor M) = ∏ x, Matrix.trace (M x) := by
  simp only [Matrix.trace,Matrix.diag,tensor]
  exact (Fintype.prod_sum fun x a => M x a a).symm

def onsite [DecidableEq α] (x : X) (M : Matrix α α R) :
    Matrix (X → α) (X → α) R :=
  tensor (Function.update (fun _ => 1) x M)

lemma local_one [DecidableEq α] (x : X) :
    onsite x (1 : Matrix α α R) = 1 := by
  rw [onsite,Function.update_eq_self,tensor_one]

lemma local_mul [DecidableEq α] [Fintype α]
    (x : X) (M N : Matrix α α R) : onsite x M * onsite x N = onsite x (M*N) := by
  simp only [onsite]
  rw [tensor_mul (X := X) (α := α) (β := α) (γ := α)]
  congr 1
  funext y
  by_cases h : y = x <;> simp [h]

lemma local_entry [DecidableEq α] (x : X) (M : Matrix α α R)
    (a b : X → α) : onsite x M a b =
      M (a x) (b x) * ∏ y ∈ (Finset.univ.erase x), (1 : Matrix α α R) (a y) (b y) := by
  unfold onsite tensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  simp only [Function.update_of_ne (Finset.mem_erase.mp hy).1]

lemma local_add [DecidableEq α] (x : X) (M N : Matrix α α R) :
    onsite x (M+N) = onsite x M + onsite x N := by
  ext a b
  simp only [local_entry,Matrix.add_apply,add_mul]

lemma local_zero [DecidableEq α] (x : X) :
    onsite x (0 : Matrix α α R) = 0 := by
  ext a b
  simp [local_entry]

lemma local_smul [DecidableEq α] (x : X) (r : R) (M : Matrix α α R) :
    onsite x (r • M) = r • onsite x M := by
  ext a b
  simp [local_entry,mul_assoc]

lemma local_commute [DecidableEq α] [Fintype α]
    {x y : X} (hxy : x ≠ y) (M N : Matrix α α R) : Commute (onsite x M) (onsite y N) := by
  change onsite x M * onsite y N = onsite y N * onsite x M
  simp only [onsite]
  rw [tensor_mul (X := X) (α := α) (β := α) (γ := α),tensor_mul (X := X) (α := α) (β := α) (γ := α)]
  congr 1
  funext z
  by_cases hx : z = x
  · subst z; simp [hxy]
  · by_cases hy : z = y
    · subst z; simp [hxy.symm]
    · simp [hx,hy]

lemma local_intertwines [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (x : X) (V : Matrix α β R)
    (A : Matrix α α R) (B : Matrix β β R) (h : A * V = V * B) :
    onsite x A * tensor (fun _ : X => V) = tensor (fun _ : X => V) * onsite x B := by
  simp only [onsite]
  rw [tensor_mul (X := X) (α := α) (β := α) (γ := β),tensor_mul (X := X) (α := α) (β := β) (γ := β)]
  congr 1
  funext y
  by_cases hy : y = x
  · simp [hy,h]
  · simp [hy]

lemma tensor_orthonormal [Fintype α] [DecidableEq β] (V : Matrix α β R)
    (h : V.transpose * V = 1) :
    (tensor (fun _ : X => V)).transpose * tensor (fun _ : X => V) = 1 := by
  rw [tensor_transpose,tensor_mul]
  simpa only [h] using (tensor_one (X := X) (α := β) (R := R))

end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open SpinSlots TensorMatrix
variable {X : Type*} [Fintype X] [DecidableEq X]

def configEquiv (ℓ : ℕ) : SlotColor.Color (V:=X × Fin ℓ) ≃ (X → Config ℓ) where
  toFun c x := Finset.univ.filter (fun a => c (x,a) = true)
  invFun A p := decide (p.2 ∈ A p.1)
  left_inv c := by
    funext ⟨x,a⟩
    cases h : c (x,a) <;> simp [h]
  right_inv A := by ext x a; simp

omit [Fintype X] [DecidableEq X] in
@[simp] lemma mem_configEquiv (ℓ : ℕ) (c : SlotColor.Color (V:=X × Fin ℓ))
    (x : X) (a : Fin ℓ) : a ∈ configEquiv ℓ c x ↔ c (x,a) = true := by
  simp [configEquiv]

def fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ)) : Equiv.Perm (X × Fin ℓ) where
  toFun p := (p.1,κ p.1 p.2)
  invFun p := (p.1,(κ p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

omit [Fintype X] [DecidableEq X] in
lemma configEquiv_fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ))
    (c : SlotColor.Color (V:=X × Fin ℓ)) :
    configEquiv ℓ (SlotColor.permute (fiberPerm κ) c) =
      fun x => (configEquiv ℓ c x).map (κ x).toEmbedding := by
  ext x a
  simp [Finset.mem_map_equiv,SlotColor.permute,fiberPerm]

def matrix {ℓ : ℕ} (π : Equiv.Perm (X × Fin ℓ)) :
    Matrix (X → Config ℓ) (X → Config ℓ) ℝ :=
  Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (SlotColor.matrix π)

omit [DecidableEq X] in
lemma matrix_fiberPerm {ℓ : ℕ} (κ : X → Equiv.Perm (Fin ℓ)) :
    matrix (fiberPerm κ) = tensor (fun x => fun A B : Config ℓ =>
      if A = B.map (κ x).toEmbedding then (1:ℝ) else 0) := by
  ext A B
  have he : SlotColor.permute (fiberPerm κ) ((configEquiv ℓ).symm B) =
      (configEquiv ℓ).symm A ↔ A = fun x => (B x).map (κ x).toEmbedding := by
    rw [← (configEquiv ℓ).injective.eq_iff,configEquiv_fiberPerm]
    simp [eq_comm]
  change (if SlotColor.permute (fiberPerm κ) ((configEquiv ℓ).symm B) =
      (configEquiv ℓ).symm A then (1:ℝ) else 0) = _
  simp only [he]
  by_cases h : A = fun x => (B x).map (κ x).toEmbedding
  · subst A
    simp [tensor]
  · rw [ite_eq_right h]
    symm
    obtain ⟨x,hx⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (ite_eq_right hx)

theorem symmetrizer (ℓ : ℕ) :
    (Fintype.card (X → Equiv.Perm (Fin ℓ)) : ℝ)⁻¹ •
      (∑ κ : X → Equiv.Perm (Fin ℓ), matrix (fiberPerm κ)) =
    tensor (fun _ : X => basis ℓ) * (tensor (fun _ : X => basis ℓ)).transpose := by
  rw [tensor_transpose,tensor_mul]
  simp_rw [← SpinSlots.symmetrizer,matrix_fiberPerm]
  ext A B
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,tensor,average,
    Fintype.card_fun,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Nat.cast_pow,inv_pow]
  rw [Fintype.prod_sum]

lemma basis_orthonormal (ℓ : ℕ) :
    (tensor (fun _ : X => basis ℓ)).transpose * tensor (fun _ : X => basis ℓ) = 1 :=
  tensor_orthonormal _ (SpinSlots.basis_orthonormal ℓ)

lemma raising_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.raising ℓ) * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalPlus ℓ) :=
  local_intertwines x _ _ _ (SpinSlots.raising_intertwines ℓ)

lemma lowering_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.raising ℓ).transpose * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalPlus ℓ).transpose :=
  local_intertwines x _ _ _ (SpinSlots.lowering_intertwines ℓ)

lemma diagonal_intertwines (ℓ : ℕ) (x : X) :
    onsite x (SpinSlots.diagonalZ ℓ) * tensor (fun _ : X => basis ℓ) =
      tensor (fun _ : X => basis ℓ) * onsite x (physicalZ ℓ) :=
  local_intertwines x _ _ _ (SpinSlots.diagonal_intertwines ℓ)

end Heisenberg.SlotTensor
namespace Heisenberg.SlotHalf
open SlotColor
variable {V : Type*} [Fintype V] [DecidableEq V]

def change (i : V) (s : Bool) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  fun a b => if b i ≠ s ∧ a = Function.update b i s then 1 else 0

def z (i : V) : Matrix (Color (V:=V)) (Color (V:=V)) ℝ :=
  Matrix.diagonal (fun a => if a i then (1:ℝ)/2 else -1/2)

lemma change_entry (i : V) (s : Bool) (a b : Color (V:=V)) :
    change i s a b = if b i ≠ s then if a = Function.update b i s then 1 else 0 else 0 := by
  simp only [change,ite_and]

lemma change_mul {i j : V} (hij : i ≠ j) (s t : Bool) (a b : Color (V:=V)) :
    (change i s * change j t) a b = if b j ≠ t ∧ b i ≠ s ∧
      a = Function.update (Function.update b j t) i s then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : b j = t
  · simp [change,hj]
  · rw [Finset.sum_eq_single (Function.update b j t)]
    · simp [change,hj,Function.update_of_ne hij]
    · intro c _ hc
      have he : c ≠ Function.update b j t := hc
      simp [change,he]
    · simp

omit [Fintype V] in
lemma swapped_same {i j : V} (b : Color (V:=V)) (h : b i = b j) :
    SlotColor.permute (Equiv.swap i j) b = b := by
  ext k
  by_cases hi : k = i
  · subst k; simp [permute,h]
  · by_cases hj : k = j
    · subst k; simp [permute,h]
    · simp [permute,Equiv.swap_apply_of_ne_of_ne hi hj]

omit [Fintype V] in
lemma swapped_different {i j : V} (hij : i ≠ j) (b : Color (V:=V)) :
    SlotColor.permute (Equiv.swap i j) b =
      Function.update (Function.update b j (b i)) i (b j) := by
  ext k
  by_cases hi : k = i
  · subst k; simp [permute]
  · by_cases hj : k = j
    · subst k; simp [permute,hij.symm]
    · simp [permute,hi,hj,Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swap_spin {i j : V} (hij : i ≠ j) :
    SlotColor.matrix (Equiv.swap i j) =
      change i true * change j false + change i false * change j true +
      (2:ℝ) • (z i * z j) + (1/2:ℝ) • (1:Matrix (Color (V:=V)) (Color (V:=V)) ℝ) := by
  ext a b
  rw [Matrix.add_apply,Matrix.add_apply,Matrix.add_apply,change_mul hij,change_mul hij]
  simp only [z,Matrix.diagonal_mul_diagonal,Matrix.smul_apply,smul_eq_mul,
    Matrix.diagonal_apply,Matrix.one_apply]
  cases hi : b i <;> cases hj : b j
  · have he := swapped_same b (hi.trans hj.symm)
    by_cases hab : a = b
    · subst a; norm_num [SlotColor.matrix,he,hi,hj]
    · simp [SlotColor.matrix,he,hab,Ne.symm hab]
  · have he := swapped_different hij b
    rw [hi,hj] at he
    by_cases hab : a = b
    · subst a
      have hn : b ≠ Function.update (Function.update b j false) i true := by
        intro hh
        have hh' := congrFun hh i
        simp [hi] at hh'
      norm_num [SlotColor.matrix,he,hi,hj,hn,Ne.symm hn]
    · simp [SlotColor.matrix,he,hab,eq_comm]
  · have he := swapped_different hij b
    rw [hi,hj] at he
    by_cases hab : a = b
    · subst a
      have hn : b ≠ Function.update (Function.update b j true) i false := by
        intro hh
        have hh' := congrFun hh i
        simp [hi] at hh'
      norm_num [SlotColor.matrix,he,hi,hj,hn,Ne.symm hn]
    · simp [SlotColor.matrix,he,hab,eq_comm]
  · have he := swapped_same b (hi.trans hj.symm)
    by_cases hab : a = b
    · subst a; norm_num [SlotColor.matrix,he,hi,hj]
    · simp [SlotColor.matrix,he,hab,Ne.symm hab]

end Heisenberg.SlotHalf
namespace Heisenberg.TensorMatrix
variable {X α R : Type*} [Fintype X] [DecidableEq X] [DecidableEq α] [CommSemiring R]
lemma local_entry_ite (x : X) (M : Matrix α α R) (A B : X → α) :
    onsite x M A B = if ∀ y, y ≠ x → A y = B y then M (A x) (B x) else 0 := by
  rw [local_entry]
  by_cases h : ∀ y, y ≠ x → A y = B y
  · rw [ite_eq_left h]
    have he : ∏ y ∈ Finset.univ.erase x, (1:Matrix α α R) (A y) (B y) = 1 := by
      apply Finset.prod_eq_one
      intro y hy
      rw [h y (Finset.mem_erase.mp hy).1]
      exact Matrix.one_apply_eq _
    rw [he,mul_one]
  · rw [ite_eq_right h]
    obtain ⟨y,hy,hab⟩ := not_forall.mp h |>.imp (fun _ => Classical.not_imp.mp)
    have he : ∏ y ∈ Finset.univ.erase x, (1:Matrix α α R) (A y) (B y) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hy,Finset.mem_univ _⟩) (Matrix.one_apply_ne hab)
    rw [he,mul_zero]
end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
lemma config_update_true (ℓ : ℕ) (b : SlotColor.Color (V:=X × Fin ℓ)) (x : X) (a : Fin ℓ) :
    configEquiv ℓ (Function.update b (x,a) true) =
      Function.update (configEquiv ℓ b) x (insert a (configEquiv ℓ b x)) := by
  ext y k
  by_cases hy : y = x
  · subst y
    by_cases hk : k = a
    · subst k; simp
    · simp [hk]
  · simp [Function.update_of_ne hy,Function.update_of_ne (show (y,k) ≠ (x,a) by simp [hy])]

lemma reindex_change_true_entry (ℓ : ℕ) (x : X) (a : Fin ℓ) (A B : X → Config ℓ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (SlotHalf.change (x,a) true) A B =
      if a ∉ B x ∧ A = Function.update B x (insert a (B x)) then (1:ℝ) else 0 := by
  have he : (configEquiv ℓ).symm A = Function.update ((configEquiv ℓ).symm B) (x,a) true ↔
      A = Function.update B x (insert a (B x)) := by
    rw [← (configEquiv ℓ).injective.eq_iff,config_update_true]
    simp
  change (if ((configEquiv ℓ).symm B) (x,a) ≠ true ∧
      (configEquiv ℓ).symm A = Function.update ((configEquiv ℓ).symm B) (x,a) true then (1:ℝ) else 0) = _
  simp only [he]
  simp [configEquiv]

lemma erase_insert_condition {ℓ : ℕ} (a : Fin ℓ) (A B : Config ℓ) :
    (a ∉ B ∧ A = insert a B) ↔ (a ∈ A ∧ B = A.erase a) := by
  constructor
  · rintro ⟨ha,rfl⟩
    simp [ha]
  · rintro ⟨ha,rfl⟩
    simp [Finset.insert_erase ha]

theorem slot_raising (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.change (x,a) true) = onsite x (SpinSlots.raising ℓ) := by
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply]
  change (∑ a : Fin ℓ, Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
    (SlotHalf.change (x,a) true) A B) = _
  simp_rw [reindex_change_true_entry,Function.eq_update_iff]
  rw [local_entry_ite]
  by_cases h : ∀ y, y ≠ x → A y = B y
  · simp only [iff_true_intro h,and_true,ite_true]
    simp_rw [erase_insert_condition]
    unfold SpinSlots.raising
    have he : Finset.univ.filter (fun a : Fin ℓ => a ∈ A x) = A x := by ext a; simp
    simp only [ite_and]
    rw [← Finset.sum_filter,he]
  · simp only [iff_false_intro h,and_false,ite_false,Finset.sum_const_zero]

end Heisenberg.SlotTensor

namespace Heisenberg.SlotHalf
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma change_transpose (i : V) : (change i true).transpose = change i false := by
  ext a b
  have he : (b i ≠ false ∧ a = Function.update b i false) ↔
      (a i ≠ true ∧ b = Function.update a i true) := by
    constructor
    · rintro ⟨hb,rfl⟩
      have hb' : b i = true := by cases h : b i <;> simp_all
      simp [Function.update_idem,hb']
    · rintro ⟨ha,rfl⟩
      have ha' : a i = false := by cases h : a i <;> simp_all
      simp [Function.update_idem,ha']
  simp only [Matrix.transpose_apply,change,he]
end Heisenberg.SlotHalf

namespace Heisenberg.TensorMatrix
variable {X α R : Type*} [Fintype X] [DecidableEq X] [DecidableEq α] [CommSemiring R]
lemma local_transpose (x : X) (M : Matrix α α R) :
    (onsite x M).transpose = onsite x M.transpose := by
  rw [onsite,tensor_transpose]
  congr 1
  funext y
  by_cases h : y=x <;> simp [h]
lemma local_diagonal (x : X) (f : α → R) :
    onsite x (Matrix.diagonal f) = Matrix.diagonal (fun A => f (A x)) := by
  ext A B
  rw [local_entry_ite]
  by_cases h : A = B
  · subst B
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    split_ifs with ho
    · apply Matrix.diagonal_apply_ne
      intro hx
      apply h
      funext y
      by_cases hy : y=x
      · simpa [hy] using hx
      · exact ho y hy
    · rfl
end Heisenberg.TensorMatrix

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]
theorem slot_lowering (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.change (x,a) false) = onsite x (SpinSlots.raising ℓ).transpose := by
  rw [← local_transpose,← slot_raising]
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact congrFun (congrFun (SlotHalf.change_transpose (x,a)).symm ((configEquiv ℓ).symm A))
    ((configEquiv ℓ).symm B)

theorem slot_z (ℓ : ℕ) (x : X) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ)
      (∑ a : Fin ℓ, SlotHalf.z (x,a)) = onsite x (SpinSlots.diagonalZ ℓ) := by
  rw [diagonalZ,local_diagonal]
  ext A B
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply,SlotHalf.z]
  by_cases h : A = B
  · subst B
    simp only [Matrix.diagonal_apply_eq]
    have he : ∀ a : Fin ℓ, (if ((configEquiv ℓ).symm A) (x,a) then (1:ℝ)/2 else -1/2) =
        (if a ∈ A x then (1:ℝ) else 0) - 1/2 := by
      intro a
      change (if decide (a ∈ A x) then (1:ℝ)/2 else -1/2) = _
      by_cases ha : a ∈ A x <;> simp [ha] <;> norm_num
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    simp [div_eq_mul_inv]
  · have hn : (configEquiv ℓ).symm A ≠ (configEquiv ℓ).symm B :=
      (configEquiv ℓ).symm.injective.ne h
    simp [Matrix.diagonal_apply_ne _ h,Matrix.diagonal_apply_ne _ hn]

end Heisenberg.SlotTensor

namespace Heisenberg.SlotHalf
variable {X : Type*} [Fintype X] [DecidableEq X]

def totalPlus (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, change (x,a) true
def totalMinus (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, change (x,a) false
def totalZ (ℓ : ℕ) (x : X) := ∑ a : Fin ℓ, z (x,a)

theorem cross_site_swaps (ℓ : ℕ) {x y : X} (hxy : x ≠ y) :
    (∑ a : Fin ℓ, ∑ b : Fin ℓ, SlotColor.matrix (Equiv.swap (x,a) (y,b))) =
      totalPlus ℓ x * totalMinus ℓ y + totalMinus ℓ x * totalPlus ℓ y +
      (2:ℝ) • (totalZ ℓ x * totalZ ℓ y) +
      ((ℓ:ℝ)^2/2) • (1:Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) := by
  have hh : ∀ a b : Fin ℓ, (x,a) ≠ (y,b) := fun _ _ => fun h => hxy (congrArg Prod.fst h)
  simp_rw [swap_spin (hh _ _),Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul,← Finset.smul_sum]
  simp only [totalPlus,totalMinus,totalZ]
  have hz : (∑ a : Fin ℓ, ∑ b : Fin ℓ, z (x,a)*z (y,b)) =
      (∑ a : Fin ℓ, z (x,a))*(∑ b : Fin ℓ, z (y,b)) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hz]
  congr 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_smul]
  congr 1
  ring
end Heisenberg.SlotHalf

namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type*} [Fintype X] [DecidableEq X]

def spinBond (ℓ : ℕ) (x y : X) : Matrix (X → Level ℓ) (X → Level ℓ) ℝ :=
    (1/2:ℝ) • (onsite x (physicalPlus ℓ)*onsite y (physicalPlus ℓ).transpose +
      onsite x (physicalPlus ℓ).transpose*onsite y (physicalPlus ℓ)) +
      onsite x (physicalZ ℓ)*onsite y (physicalZ ℓ)

def slotBond (ℓ : ℕ) (x y : X) : Matrix (SlotColor.Color (V:=X × Fin ℓ))
    (SlotColor.Color (V:=X × Fin ℓ)) ℝ :=
    (1/2:ℝ) • (∑ a : Fin ℓ, ∑ b : Fin ℓ, SlotColor.matrix (Equiv.swap (x,a) (y,b))) -
      ((ℓ:ℝ)^2/4) • 1

theorem bond_intertwines (ℓ : ℕ) {x y : X} (hxy : x ≠ y) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (slotBond ℓ x y) *
      tensor (fun _ : X => basis ℓ) =
        tensor (fun _ : X => basis ℓ) * spinBond ℓ x y := by
  let R := Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ)
  have hR (M : Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) :
      R M = Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) M := rfl
  have hmul (M N : Matrix (SlotColor.Color (V:=X × Fin ℓ)) (SlotColor.Color (V:=X × Fin ℓ)) ℝ) : R (M*N)=R M*R N := by
    exact map_mul R M N
  rw [← hR]
  rw [slotBond,SlotHalf.cross_site_swaps ℓ hxy]
  simp only [map_sub,map_smul,map_add,map_one,hmul]
  simp only [hR,SlotHalf.totalPlus,SlotHalf.totalMinus,SlotHalf.totalZ,slot_raising,slot_lowering,slot_z]
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,
    Matrix.mul_assoc,raising_intertwines,lowering_intertwines,diagonal_intertwines]
  simp only [← Matrix.mul_assoc,raising_intertwines,lowering_intertwines,diagonal_intertwines]
  simp only [spinBond,Matrix.mul_add,Matrix.mul_smul]
  simp only [Matrix.mul_assoc]
  module

end Heisenberg.SlotTensor

end

end OAI
