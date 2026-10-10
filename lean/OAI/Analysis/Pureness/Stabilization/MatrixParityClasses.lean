import OAI.Analysis.Pureness.Stabilization.MatrixEmbedding
import OAI.Analysis.Pureness.Stabilization.MatrixCuntzAddition
import OAI.Analysis.Pureness.Stabilization.CuntzDenseMaps

namespace OAI
noncomputable section
open scoped CStarAlgebra NNReal
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixParityEmbedding (n : ℕ) (r : Fin 2) : Fin n ↪ Fin (n*2) where
  toFun i := finProdFinEquiv (i,r)
  inj' := by intro i j h; exact (Prod.mk.inj (finProdFinEquiv.injective h)).1

def matrixParity (r : Fin 2) : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A :=
  if r = 0 then matrixEven else matrixOdd

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixParity_embedding (n : ℕ) (r : Fin 2) (M : FinMatrix A n) :
    matrixEmbedding (matrixParityEmbedding n r) M =
      matrixInterleave n (if r = 0 then (M,0) else (0,M)) := by
  apply matrixEmbedding_ext
  · intro i j
    change matrixInterleave n _ (finProdFinEquiv (i,r)) (finProdFinEquiv (j,r)) = _
    rw [matrixInterleave_entry]
    fin_cases r <;> simp
  · intro i j h
    obtain ⟨⟨p,s⟩,rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨q,t⟩,rfl⟩ := finProdFinEquiv.surjective j
    have hs : s ≠ r ∨ t ≠ r := by
      rcases h with h | h
      · exact Or.inl (fun he => h ⟨p, by change finProdFinEquiv (p,r) = finProdFinEquiv (p,s); rw [he]⟩)
      · exact Or.inr (fun he => h ⟨q, by change finProdFinEquiv (q,r) = finProdFinEquiv (q,t); rw [he]⟩)
    rw [matrixInterleave_entry]
    fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all

lemma matrixParity_stage (n : ℕ) (r : Fin 2) (M : FinMatrix A n) :
    matrixParity r (matrixLimitStage n M) =
      matrixLimitStage (n*2) (matrixEmbedding (matrixParityEmbedding n r) M) := by
  rw [matrixParity_embedding]
  fin_cases r <;> simp [matrixParity,matrixLimitBlock]

theorem matrixLimit_maps_eq (f g : MatrixLimit A →⋆ₙₐ[ℂ] MatrixLimit A)
    (hfg : ∀ n (M : Positive (FinMatrix A n)),
      CuntzClass.mk (Positive.map f (Positive.map (matrixLimitStage n) M)) =
      CuntzClass.mk (Positive.map g (Positive.map (matrixLimitStage n) M)))
    (a : Positive (MatrixLimit A)) :
    CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) := by
  let S : Set (Positive (MatrixLimit A)) :=
    {a | ∃ (n : ℕ) (M : Positive (FinMatrix A n)), Positive.map (matrixLimitStage n) M = a}
  apply cuntzClass_maps_eq_of_dense f g S ?_ ?_ ?_ a
  · intro b ε hε
    obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation b hε
    exact ⟨_,⟨n,M,rfl⟩,hM⟩
  · rintro _ ⟨n,M,rfl⟩ ε
    exact ⟨n,Positive.cut ε M,Positive.map_cut _ _ _⟩
  · rintro _ ⟨n,M,rfl⟩
    exact hfg n M

theorem matrixParity_cuntzClass (r : Fin 2) (a : Positive (MatrixLimit A)) :
    CuntzClass.mk (Positive.map (matrixParity r) a) = CuntzClass.mk a := by
  apply matrixLimit_maps_eq (matrixParity r) (NonUnitalStarAlgHom.id ℂ (MatrixLimit A)) ?_ a
  intro n M
  have he : Positive.map (matrixParity r) (Positive.map (matrixLimitStage n) M) =
      Positive.map (matrixLimitStage (n*2)) (Positive.map (matrixEmbedding (matrixParityEmbedding n r)) M) :=
    Subtype.ext (matrixParity_stage n r M.1)
  rw [he]
  exact matrixEmbedding_cuntzClass _ M

namespace CuntzClass
instance : Zero (CuntzClass A) := ⟨mk Positive.zero⟩
@[simp] lemma zero_mk : mk (Positive.zero (A := A)) = (0 : CuntzClass A) := rfl

theorem matrixAdd_zero (x : CuntzClass (MatrixLimit A)) : matrixAdd x 0 = x := by
  induction x using Quotient.inductionOn with | h a =>
  change mk (matrixBlockPositive a Positive.zero) = mk a
  have he : matrixBlockPositive a Positive.zero = Positive.map (matrixParity 0) a := by
    apply Subtype.ext
    simp [matrixBlockPositive,Positive.map,positiveProduct,Positive.zero,matrixBlockHom,matrixParity]
  rw [he]
  exact matrixParity_cuntzClass 0 a

theorem zero_matrixAdd (x : CuntzClass (MatrixLimit A)) : matrixAdd 0 x = x := by
  induction x using Quotient.inductionOn with | h a =>
  change mk (matrixBlockPositive Positive.zero a) = mk a
  have he : matrixBlockPositive Positive.zero a = Positive.map (matrixParity 1) a := by
    apply Subtype.ext
    simp [matrixBlockPositive,Positive.map,positiveProduct,Positive.zero,matrixBlockHom,matrixParity]
  rw [he]
  exact matrixParity_cuntzClass 1 a
end CuntzClass
end CuntzTrace

end

end OAI
