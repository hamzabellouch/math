import OAI.Probability.SignedSweeps.WordTwirl

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def colorClassCut {C P : Type*} (π : C → P) :
    Matrix C C ℂ →ₗ[ℂ] Matrix C C ℂ where
  toFun A x y := if π x = π y then A x y else 0
  map_add' A B := by
    ext x y
    change (if π x = π y then A x y + B x y else 0) =
      (if π x = π y then A x y else 0) + (if π x = π y then B x y else 0)
    split_ifs <;> simp
  map_smul' c A := by
    ext x y
    change (if π x = π y then c * A x y else 0) =
      c * (if π x = π y then A x y else 0)
    split_ifs <;> simp

@[simp] lemma colorClassCut_apply {C P : Type*} (π : C → P) (A : Matrix C C ℂ) (x y : C) :
    colorClassCut π A x y = if π x = π y then A x y else 0 := by rfl

def wordClassCut {p : ℕ} {C P : Type*} (π : C → P) :
    Matrix (Fin p → C) (Fin p → C) ℂ →ₗ[ℂ]
      Matrix (Fin p → C) (Fin p → C) ℂ :=
  colorClassCut (fun w : Fin p → C => π ∘ w)

lemma wordClassCut_tensor {p : ℕ} {C P : Type*} (π : C → P)
    (A : Matrix C C ℂ) :
    wordClassCut π (wordTensorMatrix p A) = wordTensorMatrix p (colorClassCut π A) := by
  ext x y
  simp only [wordClassCut, colorClassCut_apply, wordTensorMatrix]
  by_cases h : π ∘ x = π ∘ y
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    exact (ite_eq_left (show π (x i) = π (y i) from congrFun h i)).symm
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

lemma colorClassCut_idempotent {C P : Type*} (π : C → P) (A : Matrix C C ℂ) :
    colorClassCut π (colorClassCut π A) = colorClassCut π A := by
  ext x y
  simp only [colorClassCut_apply]; split_ifs <;> rfl

lemma wordClassCut_commutant {p : ℕ} {C P : Type*} [Fintype C] (π : C → P)
    (A : Matrix (Fin p → C) (Fin p → C) ℂ) (hA : A ∈ wordCommutant p C) :
    wordClassCut π A ∈ wordCommutant p C := by
  rw [mem_wordCommutant_iff] at hA ⊢
  intro g x y
  have he : π ∘ (x ∘ g) = π ∘ (y ∘ g) ↔ π ∘ x = π ∘ y := by
    constructor
    · intro h
      funext i
      simpa using congrFun h (g⁻¹ i)
    · intro h
      funext i
      exact congrFun h (g i)
  simp only [wordClassCut, colorClassCut_apply]
  rw [he, hA]

theorem even_wordCommutant_span {p : ℕ} {C P : Type*} [Fintype C]
    (π : C → P) (A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hA : A ∈ wordCommutant p C) (hcut : wordClassCut π A = A) :
    A ∈ Submodule.span ℂ (Set.range (fun B : Matrix C C ℂ =>
      wordTensorMatrix p (colorClassCut π B))) := by
  rw [← hcut]
  rw [← span_wordTensorMatrix] at hA
  clear hcut
  induction hA using Submodule.span_induction with
  | mem B h =>
    obtain ⟨B, rfl⟩ := h
    rw [wordClassCut_tensor]
    exact Submodule.subset_span (Set.mem_range_self B)
  | zero => simp
  | add B D _ _ hB hD =>
    rw [map_add]
    exact Submodule.add_mem _ hB hD
  | smul c B _ hB =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hB

theorem commute_even_wordCommutant {p : ℕ} {C P : Type*} [Fintype C]
    (π : C → P) (K A : Matrix (Fin p → C) (Fin p → C) ℂ)
    (hK : ∀ B : Matrix C C ℂ, K * wordTensorMatrix p (colorClassCut π B) =
      wordTensorMatrix p (colorClassCut π B) * K)
    (hA : A ∈ wordCommutant p C) (hcut : wordClassCut π A = A) : K * A = A * K := by
  have h := even_wordCommutant_span π A hA hcut
  clear hA hcut
  induction h using Submodule.span_induction with
  | mem B h => obtain ⟨B, rfl⟩ := h; exact hK B
  | zero => simp
  | add B D _ _ hB hD => simp only [Matrix.mul_add, Matrix.add_mul, hB, hD]
  | smul c B _ hB => simp only [Matrix.mul_smul, Matrix.smul_mul, hB]

end SignedSweeps
end

end OAI
