import OAI.Analysis.KadisonKastler.AmplifiedAlgebra

namespace OAI

/-! # Finite blocks of a countable amplification

Finite operator matrices act on the first finitely many matrix summands.
Their extension is an isometric nonunital star homomorphism. These are the
bounded approximants used for the infinite-amplification gap estimate.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

def blockElement (i j : ℕ) (T : E →L[ℂ] E) : H →L[ℂ] H :=
  F.entry i 0 * cornerExtension E T * F.entry 0 j

theorem blockElement_mul (i j k l : ℕ) (T U : E →L[ℂ] E) :
    F.blockElement i j T * F.blockElement k l U =
      if j = k then F.blockElement i l (T * U) else 0 := by
  have hc : cornerExtension E T * (F.entry 0 j * F.entry k 0) * cornerExtension E U =
      if j = k then cornerExtension E (T * U) else 0 := by
    rw [F.mul_entry]
    split_ifs
    · rw [F.zero_zero, cornerExtension_mul_starProjection, ← cornerExtension_mul]
    · simp
  calc
    _ = F.entry i 0 *
        (cornerExtension E T * (F.entry 0 j * F.entry k 0) * cornerExtension E U) *
          F.entry 0 l := by unfold blockElement; noncomm_ring
    _ = _ := by rw [hc]; split_ifs <;> simp [blockElement]

theorem blockElement_star (i j : ℕ) (T : E →L[ℂ] E) :
    star (F.blockElement i j T) = F.blockElement j i (star T) := by
  simp only [blockElement, star_mul, F.star_entry, ← cornerExtension_star, mul_assoc]

theorem matrixEntry_blockElement (i j k l : ℕ) (T : E →L[ℂ] E) :
    F.matrixEntry (F.blockElement k l T) i j = if i = k ∧ l = j then T else 0 := by
  have hinj : Function.Injective (cornerExtension E) :=
    Function.LeftInverse.injective (cornerCompression_extension E)
  apply hinj
  rw [F.extension_matrixEntry]
  have he : F.entry 0 i * F.blockElement k l T * F.entry j 0 =
      (F.entry 0 i * F.entry k 0) * cornerExtension E T * (F.entry 0 l * F.entry j 0) := by
    unfold blockElement
    noncomm_ring
  rw [he, F.mul_entry, F.mul_entry]
  by_cases hik : i = k <;> by_cases hlj : l = j
  · simp only [hik, hlj, ite_true, F.zero_zero, true_and]
    rw [starProjection_mul_cornerExtension, cornerExtension_mul_starProjection]
  · simp [hik, hlj]
  · simp [hik, hlj]
  · simp [hik, hlj]

theorem matrixEntry_sum {ι : Type*} (s : Finset ι) (T : ι → H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (∑ a ∈ s, T a) i j = ∑ a ∈ s, F.matrixEntry (T a) i j := by
  apply ContinuousLinearMap.ext
  intro x
  simp [matrixEntry, sum_apply, map_sum]

def finiteBlock {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) : H →L[ℂ] H :=
  ∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (X i j)

theorem matrixEntry_finiteBlock {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) (i j : Fin n) :
    F.matrixEntry (F.finiteBlock X) i j = X i j := by
  simp only [finiteBlock, F.matrixEntry_sum, F.matrixEntry_blockElement]
  have hsum (f : Fin n → Fin n → (E →L[ℂ] E)) :
      (∑ k : Fin n, ∑ l : Fin n,
        if (i : ℕ) = k ∧ (l : ℕ) = j then f k l else 0) = f i j := by
    rw [Finset.sum_eq_single i]
    · simp [Fin.val_inj]
    · intro k _ hki
      have hi : (i : ℕ) ≠ k := fun h => hki (Fin.ext h.symm)
      simp [hi]
    · simp
  exact hsum (fun k l => X k l)

theorem finiteBlock_mul {n : ℕ}
    (X Y : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    F.finiteBlock (X * Y) = F.finiteBlock X * F.finiteBlock Y := by
  let f : Fin n → Fin n → (E →L[ℂ] E) := fun i j => X i j
  let g : Fin n → Fin n → (E →L[ℂ] E) := fun i j => Y i j
  change (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (∑ k : Fin n, f i k * g k j)) =
    (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (f i j)) *
      (∑ i : Fin n, ∑ j : Fin n, F.blockElement i j (g i j))
  simp only [Finset.sum_mul, Finset.mul_sum, F.blockElement_mul]
  have he (j k : Fin n) : ((j : ℕ) = k) ↔ j = k := Fin.val_inj
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hs (i j : Fin n) : F.blockElement i j (∑ k : Fin n, f i k * g k j) =
      ∑ k : Fin n, F.blockElement i j (f i k * g k j) := by
    simp only [blockElement, map_sum, Finset.mul_sum, Finset.sum_mul]
  simp_rw [hs]
  calc
    _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
        F.blockElement i j (f i k * g k j) := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
        F.blockElement i j (f i k * g k j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def finiteBlockHom (n : ℕ) : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E) →⋆ₙₐ[ℂ]
    (H →L[ℂ] H) where
  toFun := F.finiteBlock
  map_zero' := by simp [finiteBlock, blockElement]
  map_add' X Y := by simp [finiteBlock, blockElement, mul_add, add_mul, Finset.sum_add_distrib]
  map_mul' := F.finiteBlock_mul
  map_smul' c X := by simp [finiteBlock, blockElement, Finset.smul_sum]
  map_star' X := by
    simp only [finiteBlock, star_sum, F.blockElement_star, CStarMatrix.star_apply]
    rw [Finset.sum_comm]

theorem finiteBlockHom_injective (n : ℕ) : Function.Injective (F.finiteBlockHom n) := by
  intro X Y h
  apply Matrix.ext
  intro i j
  have hh := congrArg (fun T => F.matrixEntry T i j) h
  change F.matrixEntry (F.finiteBlock X) i j = F.matrixEntry (F.finiteBlock Y) i j at hh
  simpa only [F.matrixEntry_finiteBlock] using hh

local instance finiteBlockOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance finiteBlockOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

theorem norm_finiteBlock {n : ℕ} (X : CStarMatrix (Fin n) (Fin n) (E →L[ℂ] E)) :
    ‖F.finiteBlock X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (F.finiteBlockHom n) (F.finiteBlockHom_injective n) X

end FullMatrixCorner

end

end KadisonKastler

end OAI
