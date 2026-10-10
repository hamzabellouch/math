import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.InitialLeafRates

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCCapacity

open AllFieldHistory AllFieldParameters MatrixMultiplication.Foundation
open scoped BigOperators

def stageCMarginal (t u : Shape) (i : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : Fin 4, if stageCAtom u b i = k.val then (stageCWeight t u b : ℝ) else 0

theorem stageCMarginal_eq_shapeLaw (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 3) (k : Fin 17) :
    stageCMarginal t u i k =
      ∑ b : Fin 4, if stageCAtom u b i = k.val then
        (stageCLaw t u (stageCAtom u b) : ℝ) else 0 := by
  simp only [stageCMarginal, stageCLaw_atom t u hu hpos]

private def symbolicMarginal (u : Shape) (d : ℝ) (i : Fin 3) (k : Fin 17) : ℝ :=
  ∑ b : Fin 4, if stageCAtom u b i = k.val then
    (if b.val < 2 then d / 2 else (1 - d) / 2) else 0

private theorem stageCMarginal_symbolic (t u : Shape) (i : Fin 3) (k : Fin 17) :
    stageCMarginal t u i k = symbolicMarginal u (binaryParameter t u) i k := by
  unfold stageCMarginal symbolicMarginal
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.val < 2 <;> simp [stageCWeight, hb]

private theorem symbolicMarginal_eq_2_1_1_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff]

private theorem symbolicMarginal_eq_2_1_1_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_2_1_1_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_2_1_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_2_1_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff]

private theorem symbolicMarginal_eq_1_2_1_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff]

private theorem symbolicMarginal_eq (u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (d : ℝ) (i : Fin 3) (k : Fin 17) :
    symbolicMarginal u d i k =
      if i = stageCDistinguished u then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0)  := by
  rcases positive_four_shapes u hu hpos with rfl | rfl | rfl <;> fin_cases i
  · exact symbolicMarginal_eq_1_1_2_0 d k
  · exact symbolicMarginal_eq_1_1_2_1 d k
  · exact symbolicMarginal_eq_1_1_2_2 d k
  · exact symbolicMarginal_eq_1_2_1_0 d k
  · exact symbolicMarginal_eq_1_2_1_1 d k
  · exact symbolicMarginal_eq_1_2_1_2 d k
  · exact symbolicMarginal_eq_2_1_1_0 d k
  · exact symbolicMarginal_eq_2_1_1_1 d k
  · exact symbolicMarginal_eq_2_1_1_2 d k

theorem stageCMarginal_eq (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 3) (k : Fin 17) :
    stageCMarginal t u i k =
      if i = stageCDistinguished u then
        (if k = 0 then (binaryParameter t u : ℝ) / 2
         else if k = 1 then 1 - (binaryParameter t u : ℝ)
         else if k = 2 then (binaryParameter t u : ℝ) / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  rw [stageCMarginal_symbolic]
  exact symbolicMarginal_eq u hu hpos _ i k

private theorem entropy_three_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p q r : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q
      else if i = c then r else 0) = entropyTerm p + entropyTerm q + entropyTerm r := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0) + (if i = c then entropyTerm r else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases ha : i = a
      · subst i
        simp [hab, hac]
      · by_cases hb : i = b
        · subst i
          simp [ha, hbc]
        · by_cases hc : i = c <;> simp [ha, hb, hc, Ne.symm hac, Ne.symm hbc]
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem entropy_distinguished (d : ℚ) :
    finiteEntropy (fun k : Fin 17 =>
      if k = 0 then (d : ℝ) / 2 else if k = 1 then 1 - (d : ℝ)
      else if k = 2 then (d : ℝ) / 2 else 0) = binaryEntropyRate d := by
  rw [entropy_three_points (0 : Fin 17) 1 2 (by decide) (by decide) (by decide)]
  simp only [entropyTerm_divide]
  unfold binaryEntropyRate
  ring

private theorem entropy_other :
    finiteEntropy (fun k : Fin 17 =>
      if k = 0 then (1 / 2 : ℝ) else if k = 1 then 1 / 2 else 0) = Real.log 2 := by
  rw [entropy_two_points (0 : Fin 17) 1 (by decide)]
  simp only [entropyTerm_divide]
  norm_num [entropyTerm]
  ring

theorem stageCMarginal_entropy (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 3) :
    finiteEntropy (stageCMarginal t u i) =
      if i = stageCDistinguished u then binaryEntropyRate (binaryParameter t u)
      else Real.log 2 := by
  change finiteEntropy (fun k => stageCMarginal t u i k) = _
  simp_rw [stageCMarginal_eq t u hu hpos]
  by_cases hi : i = stageCDistinguished u
  · simp only [hi, ite_true]
    exact entropy_distinguished _
  · simp only [hi, ite_false]
    exact entropy_other

theorem stageCMarginal_priority_entropy {K : ℕ} (h : PartC K) (i : Fin 3) :
    finiteEntropy (stageCMarginal (cParameterParent h) (cShapeParent h) (cPriority h i)) =
      if i = h.2 then binaryEntropyRate (binaryParameter (cParameterParent h) (cShapeParent h))
      else Real.log 2 := by
  rw [stageCMarginal_entropy (cParameterParent h) (cShapeParent h)
    (bShape_size h.1.val) h.1.property (cPriority h i)]
  have hi : cPriority h i = stageCDistinguished (cShapeParent h) ↔ i = h.2 := by
    rw [← cPriority_at_part h, Equiv.apply_eq_iff_eq]
  simp only [hi]

theorem allocation_capacity (allocation : Allocation) (d : ℚ) (i : Fin 3) :
    (∑ part : Fin 3, (allocation.mass part : ℝ) *
      (if i = part then binaryEntropyRate d else Real.log 2)) =
      (1 - (allocation.mass i : ℝ)) * Real.log 2 +
        (allocation.mass i : ℝ) * binaryEntropyRate d := by
  have hsum : (∑ part : Fin 3, (allocation.mass part : ℝ)) = 1 := by
    exact_mod_cast allocation.total
  calc
    _ = ∑ part : Fin 3, ((allocation.mass part : ℝ) * Real.log 2 +
        if part = i then (allocation.mass i : ℝ) * (binaryEntropyRate d - Real.log 2) else 0) := by
      apply Finset.sum_congr rfl
      intro part _
      by_cases hp : part = i
      · subst part
        simp only [ite_true]
        ring
      · simp [hp, Ne.symm hp]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [hsum, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring

end MatrixMultiplication.AllFieldStageCCapacity

end

end MatrixAllFields

end OAI
