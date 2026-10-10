import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

section

variable {R ι : Type*} [Semiring R]

variable (C A K : ι → R)

def cutSum : List ι → R
  | [] => 1
  | i :: w => C i * cutSum w + (A i + K i) * (w.map A).prod

def CutCompatible (i j : ι) : Prop :=
  A i * C j = 0 ∧ K i * C j = 0 ∧ A i * K j = 0 ∧ K i * K j = 0

theorem noncreation_cutSum (i j : ι) (w : List ι)
    (h : CutCompatible C A K i j) :
    (A i + K i) * cutSum C A K (j :: w) =
      (A i + K i) * ((j :: w).map A).prod := by
  rcases h with ⟨hAC, hKC, hAK, hKK⟩
  simp only [cutSum, List.map_cons, List.prod_cons, mul_add, add_mul,
    ← mul_assoc, hAC, hKC, hAK, hKK, zero_mul, zero_add, add_zero]

theorem product_eq_cutSum (w : List ι) (hw : w.IsChain (CutCompatible C A K)) :
    (w.map (fun i => C i + A i + K i)).prod = cutSum C A K w := by
  induction w with
  | nil => simp [cutSum]
  | cons i w ih =>
    rw [List.isChain_cons] at hw
    rw [List.map_cons, List.prod_cons, ih hw.2, cutSum, add_assoc, add_mul]
    congr 1
    cases w with
    | nil => simp [cutSum]
    | cons j w => exact noncreation_cutSum C A K i j w (hw.1 j (by simp))

theorem cutSum_map {κ : Type*} (f : κ → ι) (w : List κ) :
    cutSum C A K (w.map f) = cutSum (C ∘ f) (A ∘ f) (K ∘ f) w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [cutSum, List.map_cons, ih, List.map_map]; rfl

def noPresCut {n : ℕ} (C A : Fin n → R) (k : ℕ) : R :=
  ((List.ofFn C).take k).prod * ((List.ofFn A).drop k).prod

def presCut {n : ℕ} (C A K : Fin n → R) (j : Fin n) : R :=
  ((List.ofFn C).take j).prod * K j * ((List.ofFn A).drop (j+1)).prod

theorem cutSum_eq_cuts {n : ℕ} (C A K : Fin n → R) :
    cutSum C A K (List.ofFn id) =
      (∑ p : Fin (n+1), noPresCut C A p) + ∑ j : Fin n, presCut C A K j := by
  induction n with
  | zero => simp [cutSum, noPresCut, presCut]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [id_eq]
    rw [cutSum]
    have htail : cutSum C A K (List.ofFn (fun j : Fin n => j.succ)) =
        cutSum (fun j => C j.succ) (fun j => A j.succ) (fun j => K j.succ)
          (List.ofFn id) := by
      simpa only [List.map_ofFn, Function.comp_def, id_eq] using
        cutSum_map C A K Fin.succ (List.ofFn (id : Fin n → Fin n))
    rw [htail, ih,
      Fin.sum_univ_succ (fun p : Fin (n+2) => noPresCut C A p),
      Fin.sum_univ_succ (fun j : Fin (n+1) => presCut C A K j)]
    simp only [noPresCut, presCut, List.ofFn_succ, List.take_zero, List.prod_nil,
      List.drop_zero, one_mul, List.take_succ_cons, List.drop_succ_cons,
      List.prod_cons, Fin.val_zero, Fin.val_succ,
      List.map_ofFn, Function.comp_def]
    simp only [mul_add, add_mul, Finset.mul_sum, mul_assoc]
    abel

end

end KKFreeWords
end

end OAI
