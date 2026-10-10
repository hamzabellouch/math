import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHamiltonian
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.Singlet

namespace OAI

/-! Actual one-site Pauli matrices on the complete source spin basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def sourceTensor (n : ℕ) (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t => ∏ i, M i (s i) (t i)

theorem sourceTensor_one (n : ℕ) : sourceTensor n (fun _ => 1) = 1 := by
  classical
  ext s t
  by_cases hst : s = t
  · subst t
    simp [sourceTensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
    simp only [Matrix.one_apply, ite_eq_right hst, sourceTensor]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sourceTensor_mul (n : ℕ) (M N : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    sourceTensor n M * sourceTensor n N = sourceTensor n (fun i => M i * N i) := by
  ext s t
  simp only [Matrix.mul_apply, sourceTensor, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => M i (s i) a * N i a (t i))).symm

def sourceLocalPauli (n : ℕ) (i : Fin n) (μ : Fin 3) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceTensor n (fun k => if k = i then pauli μ else 1)

theorem pauli_sq (μ : Fin 3) : pauli μ * pauli μ = 1 := by
  fin_cases μ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem sourceLocalPauli_sq (n : ℕ) (i : Fin n) (μ : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n i μ = 1 := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul]
  have h (k : Fin n) :
      (if k = i then pauli μ else 1) * (if k = i then pauli μ else 1) = 1 := by
    by_cases hki : k = i <;> simp [hki, pauli_sq]
  simp_rw [h]
  exact sourceTensor_one n

theorem sourceLocalPauli_commute (n : ℕ) (i j : Fin n) (hij : i ≠ j) (μ ν : Fin 3) :
    sourceLocalPauli n i μ * sourceLocalPauli n j ν =
      sourceLocalPauli n j ν * sourceLocalPauli n i μ := by
  unfold sourceLocalPauli
  rw [sourceTensor_mul, sourceTensor_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij.symm]
    · simp [hki, hkj]

/-- The Pauli contraction on two actual two-state spins. -/
theorem pauli_entry_sum (a b c d : Fin 2) :
    (∑ μ : Fin 3, pauli μ a c * pauli μ b d) =
      2 * (if a = d ∧ b = c then (1 : ℂ) else 0) -
        (if a = c ∧ b = d then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauli, pauliX, pauliY, pauliZ, Fin.sum_univ_succ]

def sourceSpectatorDelta (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, if s k = t k then (1 : ℂ) else 0

theorem sourceSpectatorDelta_eq_one (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n)
    (hst : ∀ k, k ≠ i → k ≠ j → s k = t k) : sourceSpectatorDelta n i j s t = 1 := by
  classical
  apply Finset.prod_eq_one
  intro k hk
  exact ite_eq_left (hst k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    (Finset.mem_erase.mp hk).1)

theorem sourceSpectatorDelta_eq_zero (n : ℕ) (i j : Fin n) (s t : SourceSpinBasis n)
    (hst : ¬∀ k, k ≠ i → k ≠ j → s k = t k) : sourceSpectatorDelta n i j s t = 0 := by
  classical
  push Not at hst
  obtain ⟨k, hki, hkj, hne⟩ := hst
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,
    Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩)
  simp [hne]

theorem sourceLocalPauli_product_entry (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (μ ν : Fin 3) (s t : SourceSpinBasis n) :
    (sourceLocalPauli n i μ * sourceLocalPauli n j ν) s t =
      pauli μ (s i) (t i) * pauli ν (s j) (t j) * sourceSpectatorDelta n i j s t := by
  classical
  unfold sourceLocalPauli
  rw [sourceTensor_mul]
  unfold sourceTensor
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  simp only [ite_true, ite_eq_right hij, ite_eq_right hij.symm, mul_one, one_mul]
  rw [← mul_assoc]
  congr 1
  unfold sourceSpectatorDelta
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  simp only [ite_eq_right hki, ite_eq_right hkj, one_mul, Matrix.one_apply]

theorem sourceSpinSwap_eq_iff {n : ℕ} (i j : Fin n) (_hij : i ≠ j)
    (s t : SourceSpinBasis n) :
    sourceSpinSwap i j s = t ↔ s j = t i ∧ s i = t j ∧
      ∀ k, k ≠ i → k ≠ j → s k = t k := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceSpinSwap_apply] using congrFun h i
    · simpa [sourceSpinSwap_apply] using congrFun h j
    · intro k hki hkj
      simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using congrFun h k
  · rintro ⟨hi, hj, hrest⟩
    funext k
    by_cases hki : k = i
    · subst k
      simpa [sourceSpinSwap_apply] using hi
    · by_cases hkj : k = j
      · subst k
        simpa [sourceSpinSwap_apply] using hj
      · simpa [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj] using hrest k hki hkj

def sourceHeisenbergMatrix (n : ℕ) (i j : Fin n) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ := fun s t =>
  2 * (if sourceSpinSwap i j s = t then 1 else 0) - (if s = t then 1 else 0)

/-- The Pauli sum on distinct sites equals the complete source Hamiltonian
matrix, with every other spin acting as an untouched spectator. -/
theorem sourceLocalPauli_sum (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (∑ μ : Fin 3, sourceLocalPauli n i μ * sourceLocalPauli n j μ) =
      sourceHeisenbergMatrix n i j := by
  classical
  ext s t
  rw [Matrix.sum_apply]
  simp_rw [sourceLocalPauli_product_entry n i j hij]
  rw [← Finset.sum_mul, pauli_entry_sum]
  by_cases hrest : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [sourceSpectatorDelta_eq_one n i j s t hrest, mul_one]
    have hsame : s = t ↔ s i = t i ∧ s j = t j := by
      constructor
      · intro h
        exact ⟨congrFun h i, congrFun h j⟩
      · rintro ⟨hi, hj⟩
        funext k
        by_cases hki : k = i
        · simpa [hki] using hi
        · by_cases hkj : k = j
          · simpa [hkj] using hj
          · exact hrest k hki hkj
    have hswap : sourceSpinSwap i j s = t ↔ s i = t j ∧ s j = t i := by
      rw [sourceSpinSwap_eq_iff i j hij]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hrest⟩⟩
    change _ = 2 * (if sourceSpinSwap i j s = t then (1 : ℂ) else 0) -
      (if s = t then 1 else 0)
    simp only [hswap, hsame]
  · rw [sourceSpectatorDelta_eq_zero n i j s t hrest, mul_zero]
    have hswap : sourceSpinSwap i j s ≠ t := by
      intro h
      exact hrest ((sourceSpinSwap_eq_iff i j hij s t).mp h).2.2
    have hsame : s ≠ t := by
      intro h
      apply hrest
      intro k _ _
      exact congrFun h k
    simp [sourceHeisenbergMatrix, hswap, hsame]

/-- Matrix multiplication agrees with the swap-based Heisenberg action. -/
theorem sourceHeisenbergMatrix_mulVec (n : ℕ) (i j : Fin n) (u : SourceSpinVector n) :
    sourceHeisenbergMatrix n i j *ᵥ u = sourceHeisenbergAction i j u := by
  classical
  funext s
  simp only [sourceHeisenbergMatrix, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  simp [sourceHeisenbergAction]

end ContinuumCoulomb

end

end OAI
