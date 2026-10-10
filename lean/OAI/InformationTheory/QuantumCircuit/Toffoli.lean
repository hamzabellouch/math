import OAI.InformationTheory.QuantumCircuit.Reflection

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- Computational basis vectors and the normalized minus vector. -/
def basisVector (b : Bit) : Bit → ℂ := fun x => if x=b then 1 else 0

def halfScale : ℝ := (Real.sqrt 2)⁻¹

lemma halfScale_sq : halfScale^2 = 1/2 := by
  rw [halfScale,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

lemma halfScale_nonneg : 0 ≤ halfScale := by unfold halfScale; positivity

lemma basisVector_normalized (b : Bit) : ∑ x, Complex.normSq (basisVector b x) = 1 := by
  classical
  simp [basisVector]

lemma rankOne_basis (b : Bit) (x y : Bit) :
    rankOne (basisVector b) x y = if x=b ∧ y=b then 1 else 0 := by
  classical
  simp only [rankOne,basisVector]
  split_ifs <;> simp_all

def minusVector (b : Bit) : ℂ := if b=0 then (halfScale:ℂ) else -(halfScale:ℂ)

lemma minusVector_normalized : ∑ b, Complex.normSq (minusVector b) = 1 := by
  norm_num [Fin.sum_univ_two,minusVector,Complex.normSq_ofReal]
  nlinarith only [halfScale_sq]

lemma rankOne_minus (x y : Bit) :
    rankOne minusVector x y = if x=y then (1/2:ℂ) else -(1/2:ℂ) := by
  have hh : (halfScale:ℂ)^2 = 1/2 := by rw [← Complex.ofReal_pow,halfScale_sq]; norm_num
  fin_cases x <;> fin_cases y <;> simp [rankOne,minusVector,← pow_two,hh]

/-- The product projection in the exact Toffoli identity I-2 C⊗|-><-|. -/
def toffoliCount {N : ℕ} (c : Finset (Fin N)) (t : Fin N) : Count N where
  support := insert t c
  vector i := if i=t then minusVector else basisVector 1
  normalized i _ := by
    split_ifs
    · exact minusVector_normalized
    · exact basisVector_normalized 1

lemma toffoliCount_entry {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c)
    (x y : Word N) :
    (toffoliCount c t).zero x y =
      if (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) then
        rankOne minusVector (x t) (y t) else 0 := by
  classical
  let a : Fin N → QubitOperator := fun i =>
    if i ∈ insert t c then rankOne (if i=t then minusVector else basisVector 1) else 1
  change (∏ i, a i (x i) (y i)) = _
  have hat : a t (x t) (y t) = rankOne minusVector (x t) (y t) := by simp [a]
  have hf : ∀ i, i ≠ t → a i (x i) (y i) =
      if x i=y i ∧ (i ∈ c → y i=1) then 1 else 0 := by
    intro i hi
    by_cases hic : i ∈ c
    · simp only [a,Finset.mem_insert,hic,or_true,ite_true,ite_eq_right hi,rankOne_basis,true_implies]
      congr 1
      apply propext
      constructor
      · rintro ⟨hx,hy⟩; exact ⟨hx.trans hy.symm,hy⟩
      · rintro ⟨hxy,hy⟩; exact ⟨hxy.trans hy,hy⟩
    · simp [a,hi,hic,Matrix.one_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single t]
    · exact hat
    · intro i _ hit
      rw [hf i hit,ite_eq_left ⟨h.1 i hit,h.2 i⟩]
    · simp
  · obtain h | h := not_and_or.mp h
    · push Not at h
      obtain ⟨i,hit,hxy⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hxy])
    · push Not at h
      obtain ⟨i,hic,hy⟩ := h
      have hit : i ≠ t := fun h => ht (h ▸ hic)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hf i hit]; simp [hic,hy])

lemma toffoli_reflection {N : ℕ} (c : Finset (Fin N)) (t : Fin N) (ht : t ∉ c) :
    Gate.matrix (.toffoli c t ht) = reflect (toffoliCount c t) := by
  classical
  ext x y
  change (if x=Gate.toffoliWord c t y then (1:ℂ) else 0) =
    (if x=y then 1 else 0) - 2*(toffoliCount c t).zero x y
  rw [toffoliCount_entry c t ht]
  by_cases hctrl : ∀ i ∈ c, y i=1
  · have hw : Gate.toffoliWord c t y = Function.update y t (1-y t) := by
      exact ite_eq_left hctrl
    rw [hw]
    by_cases hrest : ∀ i, i ≠ t → x i=y i
    · have hxy : x=y ↔ x t=y t := by
        constructor
        · intro h; exact congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · exact hrest i hi
      have hxu : x=Function.update y t (1-y t) ↔ x t=1-y t := by
        constructor
        · intro h; simpa using congrFun h t
        · intro h; funext i; by_cases hi : i=t
          · simpa [hi] using h
          · simpa [Function.update_of_ne hi] using hrest i hi
      have hboth : (∀ i, i ≠ t → x i=y i) ∧ (∀ i ∈ c, y i=1) := ⟨hrest,hctrl⟩
      rw [ite_eq_left hboth,rankOne_minus]
      simp only [hxy,hxu]
      generalize x t = a, y t = b
      fin_cases a <;> fin_cases b <;> norm_num
    · have hxy : x ≠ y := by intro h; apply hrest; intro i _; exact congrFun h i
      have hxu : x ≠ Function.update y t (1-y t) := by
        intro h; apply hrest; intro i hi
        simpa [Function.update_of_ne hi] using congrFun h i
      simp [hrest,hxy,hxu]
  · have hw : Gate.toffoliWord c t y = y := by exact ite_eq_right hctrl
    rw [hw]
    simp [hctrl]

end QAC

end

end OAI
