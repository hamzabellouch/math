import OAI.Analysis.MarkovType.CoefficientBasic
import Mathlib.Order.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {n m k : ℕ}

omit sectionNormedSpaceℝE in
theorem sum_univ_eq_sum_embedding [NormedSpace ℝ E] {A B : Type*} [Fintype A] [Fintype B]
    (e : A ↪ B) (f : B → E)
    (hf : ∀ b, (¬ ∃ a, e a = b) → f b = 0) :
    (∑ b, f b) = ∑ a, f (e a) := by
  classical
  calc
    (∑ b, f b) = ∑ b ∈ Finset.univ.map e, f b := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _hb hnot
      apply hf b
      rintro ⟨a, rfl⟩
      exact hnot (Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    _ = ∑ a, f (e a) := Finset.sum_map _ _ _

theorem sum_extend_smul (e : Fin m ↪ Fin n) (a : Fin m → ℝ) (x : Fin n → E) :
    (∑ i, Function.extend e a (fun _ => 0) i • x i) = ∑ j, a j • x (e j) := by
  classical
  calc
    _ = ∑ j, Function.extend e a (fun _ => 0) (e j) • x (e j) := by
      apply sum_univ_eq_sum_embedding e
      intro i hi
      rw [Function.extend_apply' a (fun _ => 0) i hi, zero_smul]
    _ = _ := by simp only [e.injective.extend_apply]

theorem CoefficientBasic.comp_orderEmbedding {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) :
    CoefficientBasic K (fun i => x (e i)) := by
  classical
  intro a r hr
  let s : ℕ := if h : r < m then (e ⟨r, h⟩).val else n
  have hs : s ≤ n := by
    dsimp [s]
    split
    · exact (e _).is_lt.le
    · exact le_rfl
  have hcut (j : Fin m) : (e j).val < s ↔ j.val < r := by
    by_cases h : r < m
    · dsimp [s]
      rw [dite_eq_left h]
      change e j < e ⟨r, h⟩ ↔ j < ⟨r, h⟩
      exact e.lt_iff_lt
    · dsimp [s]
      rw [dite_eq_right h]
      exact iff_of_true (e j).is_lt (lt_of_lt_of_le j.is_lt (Nat.le_of_not_gt h))
  have hfull := sum_extend_smul e.toEmbedding a x
  have hpref := sum_extend_smul e.toEmbedding a (fun i => if i.val < s then x i else 0)
  simp only [smul_ite, smul_zero] at hpref
  change (∑ i : Fin n, if i.val < s then
    Function.extend e.toEmbedding a (fun _ => 0) i • x i else 0) =
      ∑ j : Fin m, if (e j).val < s then a j • x (e j) else 0 at hpref
  simp only [hcut] at hpref
  have hh := hx (Function.extend e.toEmbedding a (fun _ => 0)) s hs
  rw [hpref, hfull] at hh
  exact hh

def coefficientZeroPad (x : Fin n → E) (_hnm : n ≤ m) : Fin m → E :=
  fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0

omit sectionNormedSpaceℝE in
@[simp] theorem coefficientZeroPad_castLE [NormedSpace ℝ E] (x : Fin n → E) (hnm : n ≤ m) (i : Fin n) :
    coefficientZeroPad x hnm (Fin.castLE hnm i) = x i := by
  simp [coefficientZeroPad, i.is_lt]

omit sectionNormedSpaceℝE in
theorem coefficientZeroPad_eq_zero [NormedSpace ℝ E] (x : Fin n → E) (hnm : n ≤ m) (i : Fin m)
    (hi : n ≤ i.val) : coefficientZeroPad x hnm i = 0 := by
  simp [coefficientZeroPad, Nat.not_lt.mpr hi]

theorem coefficientZeroPad_eq_zero_of_not_range (x : Fin n → E) (hnm : n ≤ m)
    (i : Fin m) (hi : ¬ ∃ j : Fin n, Fin.castLE hnm j = i) :
    coefficientZeroPad x hnm i = 0 := by
  apply coefficientZeroPad_eq_zero
  by_contra h
  apply hi
  exact ⟨⟨i.val, Nat.lt_of_not_ge h⟩, Fin.ext rfl⟩

theorem sum_coefficientZeroPad (x : Fin n → E) (hnm : n ≤ m) :
    (∑ i, coefficientZeroPad x hnm i) = ∑ i, x i := by
  rw [sum_univ_eq_sum_embedding (Fin.castLEEmb hnm) _
    (coefficientZeroPad_eq_zero_of_not_range x hnm)]
  simp only [Fin.castLEEmb_apply, coefficientZeroPad_castLE]

omit sectionNormedSpaceℝE in
theorem norm_coefficientZeroPad_le [NormedSpace ℝ E] (x : Fin n → E) (hnm : n ≤ m)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ i, ‖x i‖ ≤ R) (i : Fin m) :
    ‖coefficientZeroPad x hnm i‖ ≤ R := by
  by_cases hi : i.val < n
  · simpa only [coefficientZeroPad, dite_eq_left hi] using hx ⟨i.val, hi⟩
  · simpa only [coefficientZeroPad, dite_eq_right hi, norm_zero] using hR

theorem CoefficientBasic.zeroPad {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (hnm : n ≤ m) :
    CoefficientBasic K (coefficientZeroPad x hnm) := by
  classical
  intro a r hr
  have hfull : (∑ i : Fin m, a i • coefficientZeroPad x hnm i) =
      ∑ j : Fin n, a (Fin.castLE hnm j) • x j := by
    rw [sum_univ_eq_sum_embedding (Fin.castLEEmb hnm) _ ?_]
    · simp only [Fin.castLEEmb_apply, coefficientZeroPad_castLE]
    · intro i hi
      rw [coefficientZeroPad_eq_zero_of_not_range x hnm i hi, smul_zero]
  have hpref : (∑ i : Fin m, if i.val < r then a i • coefficientZeroPad x hnm i else 0) =
      ∑ j : Fin n, if j.val < min r n then a (Fin.castLE hnm j) • x j else 0 := by
    rw [sum_univ_eq_sum_embedding (Fin.castLEEmb hnm) _ ?_]
    · apply Finset.sum_congr rfl
      intro j _hj
      simp [Fin.castLEEmb_apply, coefficientZeroPad_castLE, lt_min_iff, j.is_lt]
    · intro i hi
      rw [coefficientZeroPad_eq_zero_of_not_range x hnm i hi]
      simp only [smul_zero, ite_self]
  rw [hpref, hfull]
  exact hx (fun j => a (Fin.castLE hnm j)) (min r n) (Nat.min_le_right _ _)

def equalBlock (x : Fin (m * k) → E) (j : Fin m) (i : Fin k) : E :=
  x (finProdFinEquiv (j, i))

def equalBlocks (x : Fin (m * k) → E) (j : Fin m) : E :=
  ∑ i : Fin k, equalBlock x j i

def equalBlockOrderEmbedding (j : Fin m) : Fin k ↪o Fin (m * k) :=
  OrderEmbedding.ofStrictMono (fun i => finProdFinEquiv (j, i)) (by
    intro i l hil
    change i.val + k * j.val < l.val + k * j.val
    exact Nat.add_lt_add_right hil _)

theorem CoefficientBasic.equalBlock {K : ℝ} {x : Fin (m * k) → E}
    (hx : CoefficientBasic K x) (j : Fin m) :
    CoefficientBasic K (equalBlock x j) :=
  hx.comp_orderEmbedding (equalBlockOrderEmbedding j)

omit sectionNormedSpaceℝE in
theorem sum_equalBlocks [NormedSpace ℝ E] (x : Fin (m * k) → E) :
    (∑ j : Fin m, equalBlocks x j) = ∑ i : Fin (m * k), x i := by
  change (∑ j : Fin m, ∑ i : Fin k, x (finProdFinEquiv (j, i))) = _
  rw [← Fintype.sum_prod_type']
  exact finProdFinEquiv.sum_comp x

theorem sum_smul_equalBlocks (x : Fin (m * k) → E) (a : Fin m → ℝ) :
    (∑ j : Fin m, a j • equalBlocks x j) =
      ∑ i : Fin (m * k), a (finProdFinEquiv.symm i).1 • x i := by
  simp only [equalBlocks, equalBlock, Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  simpa only [Equiv.symm_apply_apply] using
    finProdFinEquiv.sum_comp (fun i : Fin (m * k) => a (finProdFinEquiv.symm i).1 • x i)

theorem finProdFinEquiv_prefix_iff (i : Fin (m * k)) (r : ℕ) :
    i.val < r * k ↔ (finProdFinEquiv.symm i).1.val < r := by
  obtain ⟨⟨j, l⟩, rfl⟩ := finProdFinEquiv.surjective i
  simp only [Equiv.symm_apply_apply]
  change l.val + k * j.val < r * k ↔ j.val < r
  constructor
  · intro h
    by_contra hn
    have hmul : r * k ≤ k * j.val := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right k (Nat.le_of_not_gt hn)
    omega
  · intro h
    have hmul : k * j.val + k ≤ r * k := by
      simpa only [Nat.succ_mul, Nat.mul_comm] using
        Nat.mul_le_mul_right k (Nat.succ_le_of_lt h)
    have hl := l.is_lt
    omega

theorem sum_prefix_smul_equalBlocks (x : Fin (m * k) → E) (a : Fin m → ℝ) (r : ℕ) :
    (∑ j : Fin m, if j.val < r then a j • equalBlocks x j else 0) =
      ∑ i : Fin (m * k), if i.val < r * k then
        a (finProdFinEquiv.symm i).1 • x i else 0 := by
  classical
  have h := sum_smul_equalBlocks x (fun j => if j.val < r then a j else 0)
  simp only [ite_smul, zero_smul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [finProdFinEquiv_prefix_iff]

theorem CoefficientBasic.equalBlocks {K : ℝ} {x : Fin (m * k) → E}
    (hx : CoefficientBasic K x) : CoefficientBasic K (equalBlocks x) := by
  intro a r hr
  rw [sum_prefix_smul_equalBlocks, sum_smul_equalBlocks]
  exact hx (fun i => a (finProdFinEquiv.symm i).1) (r * k) (Nat.mul_le_mul_right k hr)

end MarkovSuperreflexivity

end

end OAI
