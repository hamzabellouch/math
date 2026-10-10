import Mathlib
import OAI.Algebra.FrobeniusObstruction.FormTensor

namespace OAI

noncomputable section
open scoped BigOperators TensorProduct

namespace BoundaryOnly.FormalObstruction
namespace SignedTensor

variable {k ι : Type*} [Field k] [Fintype ι] [LinearOrder ι]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

abbrev EndFamily := ∀ i, Module.End k (V i)
abbrev TensorEnd := Module.End k (⨂[k] i, V i)

def dSlot (P D : EndFamily (k := k) V) (i : ι) : EndFamily (k := k) V :=
  fun j => if j < i then P j else if j = i then D j else 1

def hSlot (P r h : EndFamily (k := k) V) (i : ι) : EndFamily (k := k) V :=
  fun j => if j < i then r j * P j else if j = i then h j else 1

def diagSlot (r : EndFamily (k := k) V) (i : ι) : EndFamily (k := k) V :=
  fun j => if j < i then r j else if j = i then 1 - r j else 1

def differential (P D : EndFamily (k := k) V) : TensorEnd (k := k) V :=
  ∑ i, PiTensorProduct.map (dSlot V P D i)

def homotopy (P r h : EndFamily (k := k) V) : TensorEnd (k := k) V :=
  ∑ i, PiTensorProduct.map (hSlot V P r h i)

omit [Fintype ι] in
private theorem tensor_neg_at (f g : EndFamily (k := k) V) (i : ι)
    (hii : f i = -g i) (hij : ∀ j, j ≠ i → f j = g j) :
    PiTensorProduct.map f = -PiTensorProduct.map g := by
  have heq : f = Function.update g i (-g i) := by
    funext j
    by_cases h : j = i
    · subst j; simpa using hii
    · simp only [Function.update_of_ne h, hij j h]
  rw [heq]
  exact (PiTensorProduct.mapMultilinear k V V).map_update_neg g i (g i) |>.trans
    (by rw [Function.update_eq_self]; rfl)

omit [Fintype ι] in
private theorem tensor_add_at (f g b : EndFamily (k := k) V) (i : ι)
    (hf : ∀ j, j ≠ i → f j = b j) (hg : ∀ j, j ≠ i → g j = b j) :
    PiTensorProduct.map f + PiTensorProduct.map g =
      PiTensorProduct.map (Function.update b i (f i + g i)) := by
  have hh (a : EndFamily (k := k) V) (ha : ∀ j, j ≠ i → a j = b j) :
      a = Function.update b i (a i) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp only [Function.update_of_ne h, ha j h]
  conv_lhs => rw [hh f hf, hh g hg]
  exact ((PiTensorProduct.mapMultilinear k V V).map_update_add b i (f i) (g i)).symm

variable {V}

                                                    
omit [Fintype ι] in
theorem mixed_cancel (P D r h : EndFamily (k := k) V)
    (hDP : ∀ i, D i * P i = -(P i * D i))
    (hDr : ∀ i, D i * r i = r i * D i)
    (hPr : ∀ i, P i * r i = r i * P i)
    (hPh : ∀ i, P i * h i = -(h i * P i))
    (i j : ι) (hij : i ≠ j) :
    PiTensorProduct.map (dSlot V P D i) * PiTensorProduct.map (hSlot V P r h j) +
      PiTensorProduct.map (hSlot V P r h j) * PiTensorProduct.map (dSlot V P D i) = 0 := by
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  suffices hh : PiTensorProduct.map (dSlot V P D i * hSlot V P r h j) =
      -PiTensorProduct.map (hSlot V P r h j * dSlot V P D i) by exact add_eq_zero_iff_eq_neg.mpr hh
  rcases lt_or_gt_of_ne hij with hij | hji
  · apply tensor_neg_at V _ _ i
    · simp only [Pi.mul_apply, dSlot, hSlot, lt_irrefl, ite_false, ite_true, hij]
      rw [← mul_assoc, hDr, mul_assoc, hDP, mul_neg, ← mul_assoc]
    · intro a hai
      by_cases haj : a = j
      · subst a
        simp [dSlot, hSlot, hai, not_lt_of_gt hij]
      · by_cases hal : a < i
        · have hajl : a < j := hal.trans hij
          simp only [Pi.mul_apply, dSlot, hSlot, hal, hajl, ite_true]
          rw [← mul_assoc, hPr, mul_assoc]
        · by_cases hajl : a < j
          · simp [dSlot, hSlot, hal, hajl, hai]
          · simp [dSlot, hSlot, hal, hajl, hai, haj]
  · apply tensor_neg_at V _ _ j
    · simp only [Pi.mul_apply, dSlot, hSlot, lt_irrefl, ite_false, ite_true, hji]
      exact hPh j
    · intro a haj
      by_cases hai : a = i
      · subst a
        simp [dSlot, hSlot, haj, not_lt_of_gt hji]
      · by_cases hal : a < j
        · have hail : a < i := hal.trans hji
          simp only [Pi.mul_apply, dSlot, hSlot, hal, hail, ite_true]
          rw [← mul_assoc, hPr, mul_assoc]
        · by_cases hail : a < i
          · simp [dSlot, hSlot, hal, hail, haj]
          · simp [dSlot, hSlot, hal, hail, hai, haj]

                                                                
omit [Fintype ι] in
theorem diagonal_term (P D r h : EndFamily (k := k) V)
    (hP2 : ∀ i, P i * P i = 1)
    (hPr : ∀ i, P i * r i = r i * P i)
    (hDh : ∀ i, D i * h i + h i * D i = 1 - r i)
    (i : ι) :
    PiTensorProduct.map (dSlot V P D i) * PiTensorProduct.map (hSlot V P r h i) +
      PiTensorProduct.map (hSlot V P r h i) * PiTensorProduct.map (dSlot V P D i) =
        PiTensorProduct.map (diagSlot V r i) := by
  rw [← PiTensorProduct.map_mul, ← PiTensorProduct.map_mul]
  have hbefore (a : ι) : P a * (r a * P a) = r a := by
    rw [← mul_assoc, hPr, mul_assoc, hP2, mul_one]
  rw [tensor_add_at V _ _ (diagSlot V r i) i]
  · congr 1
    funext a
    by_cases hai : a = i
    · subst a
      simp only [Function.update_self, dSlot, hSlot, diagSlot,
        lt_irrefl, ite_false, ite_true, hDh]
    · rw [Function.update_of_ne hai]
  · intro a hai
    by_cases hal : a < i
    · simp [dSlot, hSlot, diagSlot, hal, hbefore]
    · simp [dSlot, hSlot, diagSlot, hal, hai]
  · intro a hai
    by_cases hal : a < i
    · simp only [dSlot, hSlot, diagSlot, hal, ite_true]
      rw [mul_assoc, hP2, mul_one]
    · simp [dSlot, hSlot, diagSlot, hal, hai]

                                                                      
theorem diagonal_sum (r : EndFamily (k := k) V) :
    ∑ i, PiTensorProduct.map (diagSlot V r i) = 1 - PiTensorProduct.map r := by
  let m := PiTensorProduct.mapMultilinear k V V
  have H := m.map_piecewise_sub_map_piecewise r (1 : EndFamily (k := k) V) (1 : EndFamily (k := k) V) Finset.univ
  simp only [Finset.piecewise_univ, Finset.mem_univ, ↓reduceIte] at H
  have hn (i : ι) : m (fun j => if j < i then r j else if j = i then r j - 1 else 1) =
      -PiTensorProduct.map (diagSlot V r i) := by
    apply tensor_neg_at V _ _ i
    · simp [diagSlot]
    · intro j hji
      simp [diagSlot, hji]
  change m r - m (1 : EndFamily (k := k) V) =
    ∑ i, m (fun j => if j < i then r j else if j = i then r j - 1 else 1) at H
  simp_rw [hn] at H
  change PiTensorProduct.map r - PiTensorProduct.map (1 : EndFamily (k := k) V) = _ at H
  have hone : PiTensorProduct.map (1 : EndFamily (k := k) V) = 1 := PiTensorProduct.map_one
  rw [hone, Finset.sum_neg_distrib] at H
  apply neg_injective
  rw [← H]
  abel

                                                                                       
theorem tensor_homotopy (P D r h : EndFamily (k := k) V)
    (hP2 : ∀ i, P i * P i = 1)
    (hDP : ∀ i, D i * P i = -(P i * D i))
    (hDr : ∀ i, D i * r i = r i * D i)
    (hPr : ∀ i, P i * r i = r i * P i)
    (hPh : ∀ i, P i * h i = -(h i * P i))
    (hDh : ∀ i, D i * h i + h i * D i = 1 - r i) :
    differential V P D * homotopy V P r h + homotopy V P r h * differential V P D =
      1 - PiTensorProduct.map r := by
  simp only [differential, homotopy, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j =>
    PiTensorProduct.map (dSlot V P D j) * PiTensorProduct.map (hSlot V P r h i)),
    ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  have hsum (i : ι) : ∑ j,
      (PiTensorProduct.map (dSlot V P D i) * PiTensorProduct.map (hSlot V P r h j) +
        PiTensorProduct.map (hSlot V P r h j) * PiTensorProduct.map (dSlot V P D i)) =
      PiTensorProduct.map (diagSlot V r i) := by
    rw [Finset.sum_eq_single i]
    · exact diagonal_term P D r h hP2 hPr hDh i
    · intro j _ hji
      exact mixed_cancel P D r h hDP hDr hPr hPh i j hji.symm
    · simp
  simp_rw [hsum]
  exact diagonal_sum r

end SignedTensor
end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.SignedTensor
open GlobalForms
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] {n : ℕ}
variable (V : Fin (n + 1) → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

                                                                          
                                              
theorem differential_cons_tprod (P D : EndFamily (k := k) V) (v : ∀ i, V i) :
    tensorCons V (differential V P D (PiTensorProduct.tprod k v)) =
      D 0 (v 0) ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin n => v i.succ) +
        P 0 (v 0) ⊗ₜ[k] differential (fun i : Fin n => V i.succ)
          (fun i => P i.succ) (fun i => D i.succ)
          (PiTensorProduct.tprod k (fun i : Fin n => v i.succ)) := by
  simp only [differential, LinearMap.sum_apply, PiTensorProduct.map_tprod, map_sum,
    tensorCons_tprod]
  rw [Fin.sum_univ_succ, TensorProduct.tmul_sum]
  simp only [dSlot, Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_succ,
    Nat.not_lt_zero, Nat.succ_ne_zero, Nat.zero_lt_succ, Nat.add_lt_add_iff_right,
    Nat.add_right_cancel_iff, ite_false, ite_true, Module.End.one_apply]

@[simp] theorem parity_cons_tprod (P : EndFamily (k := k) V) (v : ∀ i, V i) :
    tensorCons V (PiTensorProduct.map P (PiTensorProduct.tprod k v)) =
      P 0 (v 0) ⊗ₜ[k] PiTensorProduct.map (fun i : Fin n => P i.succ)
        (PiTensorProduct.tprod k (fun i : Fin n => v i.succ)) := by
  simp only [PiTensorProduct.map_tprod, tensorCons_tprod]

end BoundaryOnly.FormalObstruction.SignedTensor

end

end OAI
