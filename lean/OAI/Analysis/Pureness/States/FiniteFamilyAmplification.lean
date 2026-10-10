import OAI.Analysis.Pureness.Cuntz.FiniteMatrixFlattenNaturality
import OAI.Analysis.Pureness.States.FiniteFamilyNuclearTrace

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped NNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (F : CompatibleFiniteQuasitrace A)

def matrixAmplificationRaw (n : ℕ) : CompatibleFiniteQuasitrace (FinMatrix A n) where
  level k := (F.level (k*n)).comap (finiteMatrixFlatten k n).toNonUnitalStarAlgHom
  inclusion := by
    intro k l h X
    change F.level (l*n) (finiteMatrixFlatten l n (matrixInclusion h X))=
      F.level (k*n) (finiteMatrixFlatten k n X)
    rw [finiteMatrixFlatten_inclusion,F.inclusion]

lemma matrixAmplificationRaw_base (n : ℕ) (M : FinMatrix A n) :
    (F.matrixAmplificationRaw n).toTwoQuasitrace.base M=F.level n M := by
  change F.level (1*n) (finiteMatrixFlatten 1 n (scalarMatrixHom (ι := Fin 1) M))=F.level n M
  rw [finiteMatrixFlatten_scalar_one,F.inclusion]

lemma matrixAmplificationRaw_monotone
    (hmono : ∀ k, Monotone (fun a : Positive (FinMatrix A k) => (F.level k a.1).re))
    (n k : ℕ) :
    Monotone (fun a : Positive (FinMatrix (FinMatrix A n) k) =>
      ((F.matrixAmplificationRaw n).level k a.1).re) := by
  intro a b hab
  exact ((F.positiveLevel hmono (k*n)).comap (finiteMatrixFlatten k n).toNonUnitalStarAlgHom).monotone hab

def matrixAmplification (n : ℕ) : CompatibleFiniteQuasitrace (FinMatrix A n) :=
  (F.matrixAmplificationRaw n).scale ⟨(n : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg n)⟩

lemma matrixAmplification_level (n k : ℕ) (X : FinMatrix (FinMatrix A n) k) :
    (F.matrixAmplification n).level k X=
      (((n : ℝ)⁻¹ : ℝ) : ℂ)*F.level (k*n) (finiteMatrixFlatten k n X) := rfl

lemma matrixAmplification_base (n : ℕ) (M : FinMatrix A n) :
    (F.matrixAmplification n).toTwoQuasitrace.base M=
      (((n : ℝ)⁻¹ : ℝ) : ℂ)*F.level n M := by
  change (((n : ℝ)⁻¹ : ℝ) : ℂ)*(F.matrixAmplificationRaw n).toTwoQuasitrace.base M=_
  rw [F.matrixAmplificationRaw_base]

lemma matrixAmplification_monotone
    (hmono : ∀ k, Monotone (fun a : Positive (FinMatrix A k) => (F.level k a.1).re))
    (n k : ℕ) :
    Monotone (fun a : Positive (FinMatrix (FinMatrix A n) k) =>
      ((F.matrixAmplification n).level k a.1).re) :=
  scale_monotone _ (F.matrixAmplificationRaw_monotone hmono n) _ k

include F in
lemma matrixAmplification_unit
    (hmono : ∀ k, Monotone (fun a : Positive (FinMatrix A k) => (F.level k a.1).re))
    (hF : F.level 1 1=1) (n : ℕ) (hn : 1 ≤ n) :
    (F.matrixAmplification n).level 1 1=1 := by
  have h := F.matrixAmplification_base n 1
  have hv : F.level n 1=((n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using F.unit hmono hF n
  rw [hv,← Complex.ofReal_mul,inv_mul_cancel₀ (by exact_mod_cast (by omega : n ≠ 0)),
    Complex.ofReal_one] at h
  change (F.matrixAmplification n).level 1 (scalarMatrixHom 1)=1 at h
  rwa [map_one] at h

variable [Nontrivial A]

theorem level_additive_of_matrix_nuclear
    (hsimple : TopologicallySimple A)
    (hmono : ∀ k, Monotone (fun a : Positive (FinMatrix A k) => (F.level k a.1).re))
    (hF : F.level 1 1=1) (n : ℕ) (hn : 1 ≤ n)
    (hAn : IsNuclear.{u,0} (FinMatrix A n)) :
    ∀ M N : FinMatrix A n, F.level n (M+N)=F.level n M+F.level n N := by
  let : NeZero n := ⟨by omega⟩
  have h := nuclear_finiteFamily_original_additive (matrix_topologicallySimple hsimple) hAn
    (F.matrixAmplification n) (F.matrixAmplification_monotone hmono n)
    (F.matrixAmplification_unit hmono hF n hn)
  intro M N
  have he := h M N
  rw [F.matrixAmplification_base,F.matrixAmplification_base,F.matrixAmplification_base,← mul_add] at he
  exact mul_left_cancel₀ (by
    apply Complex.ofReal_ne_zero.mpr
    exact inv_ne_zero (by exact_mod_cast (by omega : n ≠ 0))) he
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
