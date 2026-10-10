import OAI.Probability.SignedSweeps.PairDensityLower
import OAI.Probability.SignedSweeps.NormalizedColors

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
local instance (priority := 2000) pairEntropyDensitySumDecidableEq {C D : Type*} :
    DecidableEq (C ⊕ D) := Classical.decEq _

lemma positive_unscale_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T P : E →ₗ[ℂ] E) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (h : (T - ((w / c : ℝ) : ℂ) • P).IsPositive) :
    (((c / w : ℝ) : ℂ) • T - P).IsPositive := by
  have hh := h.smul_of_nonneg (Complex.zero_le_real.mpr (div_pos hc hw).le)
  have he : (c / w : ℝ) * (w / c) = 1 := by field_simp
  simpa only [smul_sub, smul_smul, ← Complex.ofReal_mul, he,
    Complex.ofReal_one, one_smul] using hh

lemma exists_pair_entropy_colors {u v p q : ℕ} (h : u+v=p) (hq : 1 ≤ q)
    (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q) :
    ∃ x y : Fin q → ℝ,
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      (∏ i, x (Fin.castLE hα (α.rowIndex i))) *
        (∏ i, y (Fin.castLE hβ (β.rowIndex i))) = Real.exp (-signedEntropy α β) := by
  by_cases hp : p = 0
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    subst u
    subst v
    let i₀ : Fin q := ⟨0, by omega⟩
    refine ⟨(fun i => if i=i₀ then 1 else 0), (fun _ => 0), ?_, ?_, ?_, ?_⟩
    · intro i; dsimp; split_ifs <;> norm_num
    · intro i; rfl
    · simp
    · rw [signedEntropy_empty]
      simp
  · exact ⟨normalizedRowColors α q p, normalizedRowColors β q p,
      normalizedRowColors_nonneg α q p, normalizedRowColors_nonneg β q p,
      normalizedPairColors_sum h (Nat.pos_of_ne_zero hp) α β hα hβ,
      normalizedPairColors_monomial h (Nat.pos_of_ne_zero hp) α β hα hβ⟩

lemma exists_pair_entropy_color_embeddings {u v p : ℕ} {C : Type*}
    [Fintype C] [Nonempty C] (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ (e : Fin (α.1.colLen 0) ↪ C) (f : Fin (β.1.colLen 0) ↪ C) (x y : C → ℝ),
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      (∏ i, x (rowColorWord α e i)) * (∏ i, y (rowColorWord β f i)) =
        Real.exp (-signedEntropy α β) := by
  obtain ⟨x,y,hx,hy,hxy,he⟩ := exists_pair_entropy_colors h (Fintype.card_pos) α β hα hβ
  let e : Fin (α.1.colLen 0) ↪ C :=
    ⟨fun i => (Fintype.equivFin C).symm (Fin.castLE hα i),
      (Fintype.equivFin C).symm.injective.comp (Fin.castLE_injective _)⟩
  let f : Fin (β.1.colLen 0) ↪ C :=
    ⟨fun i => (Fintype.equivFin C).symm (Fin.castLE hβ i),
      (Fintype.equivFin C).symm.injective.comp (Fin.castLE_injective _)⟩
  refine ⟨e,f,(fun i => x (Fintype.equivFin C i)), (fun i => y (Fintype.equivFin C i)),
    (fun i => hx _), (fun i => hy _), ?_, ?_⟩
  · simpa only [Equiv.sum_comp] using hxy
  · simpa only [rowColorWord, Partition.rowIndex, e, f, Function.Embedding.coeFn_mk,
      Equiv.apply_symm_apply] using he

theorem exists_pair_entropy_density {u v p : ℕ} {C : Type*}
    [Fintype C] [Nonempty C] (h : u+v=p) (α : Partition u) (β : Partition v)
    (hα : α.1.colLen 0 ≤ Fintype.card C) (hβ : β.1.colLen 0 ≤ Fintype.card C) :
    ∃ (x y : C → ℝ) (M : Matrix (Fin p → C ⊕ C) (Fin p → C ⊕ C) ℂ),
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ (∑ i, x i) + (∑ i, y i) = 1 ∧
      matrixHilbertEquiv M ∈ pairTensorOrbitHull p
        (Matrix.diagonal (fun i => (x i : ℂ))) (Matrix.diagonal (fun i => (y i : ℂ))) ∧
      M.PosSemidef ∧
      ((((Real.exp (signedEntropy α β) *
          ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
            (v+1 : ℝ)^(Fintype.card C * Fintype.card C))) : ℝ) : ℂ) •
          (wordMatrixEquiv p (C ⊕ C)).symm M -
        pairTypeProjection h α β C).IsPositive := by
  obtain ⟨e,f,x,y,hx,hy,hxy,he⟩ := exists_pair_entropy_color_embeddings h α β hα hβ
  obtain ⟨M,hM,hMpos,hMlow⟩ := exists_pair_density_lower h α β e f x y hx hy
  rw [div_mul_div_comm, he] at hMlow
  refine ⟨x,y,M,hx,hy,hxy,hM,hMpos,?_⟩
  have hl := positive_unscale_lower _ _ (Real.exp_pos (-signedEntropy α β))
    (by positivity : (0:ℝ) < (u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) hMlow
  have hd : ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
      (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) / Real.exp (-signedEntropy α β) =
      Real.exp (signedEntropy α β) * ((u+1 : ℝ)^(Fintype.card C * Fintype.card C) *
        (v+1 : ℝ)^(Fintype.card C * Fintype.card C)) := by
    rw [Real.exp_neg, div_inv_eq_mul, mul_comm]
  rwa [hd] at hl

end SignedSweeps
end

end OAI
