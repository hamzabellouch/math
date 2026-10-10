import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorAncilla

namespace OAI

/-! Exact vacuum-to-one-excitation columns and their compressions.
All matrices retain every original system coordinate. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ α κ : Type*} [Fintype σ]
  [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

def qmaSliceColumn (a : α) (A : Matrix σ σ ℂ) : Matrix (σ × α) σ ℂ :=
  fun p t => if p.2 = a then A p.1 t else 0

theorem qmaSliceColumn_gram (a b : α) (A B : Matrix σ σ ℂ) :
    (qmaSliceColumn a A).conjTranspose*qmaSliceColumn b B =
      if a = b then A.conjTranspose*B else 0 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,qmaSliceColumn,
    Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply]
  · simp [hab,Ne.symm hab]

theorem qmaSliceColumn_kronecker_apply (b : α) (D B : Matrix σ σ ℂ)
    (P : Matrix α α ℂ) (s : σ) (a : α) (t : σ) :
    ((D ⊗ₖ P)*qmaSliceColumn b B) (s,a) t = P a b*(D*B) s t := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,
    qmaSliceColumn,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem qmaSliceColumn_sandwich (a b : α) (A B D : Matrix σ σ ℂ)
    (P : Matrix α α ℂ) :
    (qmaSliceColumn a A).conjTranspose*(D ⊗ₖ P)*qmaSliceColumn b B =
      P a b • (A.conjTranspose*D*B) := by
  rw [Matrix.mul_assoc]
  ext s t
  change (∑ p : σ × α, star (qmaSliceColumn a A p s)*
    ((D ⊗ₖ P)*qmaSliceColumn b B) p t) = P a b*((A.conjTranspose*D*B) s t)
  rw [Fintype.sum_prod_type]
  simp only [qmaSliceColumn_kronecker_apply,qmaSliceColumn]
  simp only [apply_ite,star_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Matrix.mul_assoc,Matrix.mul_apply,Finset.mul_sum]
  simp only [Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro u _
  ring

def qmaAncillaColumn (V : κ → Matrix σ σ ℂ) : Matrix (σ × (κ → Fin 2)) σ ℂ :=
  ∑ e, qmaSliceColumn (qmaAncillaSingle e) (V e)

theorem qmaAncillaColumn_gram (V W : κ → Matrix σ σ ℂ) :
    (qmaAncillaColumn V).conjTranspose*qmaAncillaColumn W = ∑ e, (V e).conjTranspose*W e := by
  simp only [qmaAncillaColumn,Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum,
    qmaSliceColumn_gram,qmaAncillaSingle_injective.eq_iff]
  simp

theorem qmaAncillaColumn_sandwich (V W : κ → Matrix σ σ ℂ) (D : Matrix σ σ ℂ)
    (P : Matrix (κ → Fin 2) (κ → Fin 2) ℂ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ P)*qmaAncillaColumn W =
      ∑ e, ∑ f, P (qmaAncillaSingle e) (qmaAncillaSingle f) •
        ((V e).conjTranspose*D*W f) := by
  unfold qmaAncillaColumn
  rw [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact qmaSliceColumn_sandwich (qmaAncillaSingle e) (qmaAncillaSingle f) (V e) (W f) D P

theorem qmaAncillaColumn_occupation (V W : κ → Matrix σ σ ℂ)
    (D : Matrix σ σ ℂ) (e : κ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ qmaAncillaOccupation e)*qmaAncillaColumn W =
      (V e).conjTranspose*D*W e := by
  rw [qmaAncillaColumn_sandwich]
  simp only [qmaAncillaOccupation_single,ite_smul,one_smul,zero_smul]
  simp only [ite_and]
  simp

theorem qmaAncillaColumn_flip (V W : κ → Matrix σ σ ℂ) (D : Matrix σ σ ℂ) (e : κ) :
    (qmaAncillaColumn V).conjTranspose*(D ⊗ₖ qmaBitFlipMatrix e)*qmaAncillaColumn W = 0 := by
  rw [qmaAncillaColumn_sandwich]
  simp only [qmaBitFlipMatrix_single,zero_smul,Finset.sum_const_zero]

end ContinuumCoulomb

end

end OAI
