import OAI.Analysis.FreeEntropy.MatrixBlocks

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries FreeTensor
 def tensorMatrixTuple {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) : Option (Fin p) → Matrix (Fin (d*p)) (Fin (d*p)) ℂ :=
  fun a => matrixBlocks (fun l : Fin p => optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) a)
 theorem tensorMatrixTuple_some {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (i : Fin p) :
    tensorMatrixTuple A (some i)=matrixBlocks (fun _ => A i) := rfl
 theorem tensorMatrixTuple_none {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrixTuple A none=matrixBlocks (fun l : Fin p => (equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := rfl
 theorem tensorMatrixTuple_norm_le {p d : ℕ} (hp : 2≤p) (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,matrixOpNorm (A i)≤64) (a : Option (Fin p)) : matrixOpNorm (tensorMatrixTuple A a)≤64 := by
  apply matrixBlocks_norm_le _ (by norm_num)
  intro l
  cases a with
  | some i => exact hA i
  | none =>
    change matrixOpNorm ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))≤64
    rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs]
    have h := mul_le_mul (equidiscreteAtom_abs_le hp l) (matrixOpNorm_one (d:=d)) (matrixOpNorm_nonneg _) (by norm_num : (0:ℝ)≤1)
    norm_num at h ⊢
    linarith
 theorem tensorMatrixTuple_isHermitian {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i,(A i).IsHermitian) (a : Option (Fin p)) : (tensorMatrixTuple A a).IsHermitian := by
  apply matrixBlocks_isHermitian
  intro l
  cases a with
  | some i => exact hA i
  | none =>
    change (((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))).IsHermitian
    simp [Matrix.IsHermitian,Matrix.conjTranspose_smul]
 theorem tensorMatrixTuple_word {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (w : List (Option (Fin p))) :
    matrixWord (tensorMatrixTuple A) w = matrixBlocks (fun l : Fin p => (equidiscreteAtom p l:ℂ)^(w.count none) • matrixWord A (w.filterMap id)) := by
  let F : Option (Fin p) → (Fin p → Matrix (Fin d) (Fin d) ℂ) :=
    fun a l => optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) a
  have hmap : matrixWord (tensorMatrixTuple A) w = matrixBlocks (w.map F).prod := by
    change (w.map (fun a => matrixBlocks (F a))).prod = matrixBlocks (w.map F).prod
    rw [map_list_prod,List.map_map]
    rfl
  rw [hmap]
  clear hmap
  congr 1
  funext l
  have he : (w.map F).prod l = (w.map (optionTuple A ((equidiscreteAtom p l:ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)))).prod := by
    induction w with
    | nil => rfl
    | cons a w ih => simp only [List.map_cons,List.prod_cons,Pi.mul_apply,ih]; rfl
  rw [he,option_word_product _ _ (fun i => (Commute.one_left (A i)).smul_left _)]
  rw [smul_pow,one_pow,mul_smul_comm,mul_one]
  rfl
 theorem tensorMatrixTuple_moment {p d : ℕ} (A : Fin p → Matrix (Fin d) (Fin d) ℂ) (w : List (Option (Fin p))) :
    matrixTraceWord (tensorMatrixTuple A) w = matrixTraceWord A (w.filterMap id) *
      ((p:ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l:ℂ)^(w.count none)) := by
  simp only [matrixTraceWord,tensorMatrixTuple_word,trace_matrixBlocks,Matrix.trace_smul,smul_eq_mul,Nat.cast_mul,mul_inv_rev]
  rw [← Finset.sum_mul]
  ring
end FiniteEntropySeparation

end

end OAI
