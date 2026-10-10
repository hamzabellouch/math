import OAI.Analysis.Pureness.GroupAlgebra.ResidualFiniteQuotientSequence
import OAI.Analysis.Pureness.States.ScalarMatrixTrace
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace OAI
noncomputable section
namespace CuntzPureness
local instance finiteRegularMatrixModelDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α
open CuntzTrace
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι]

def permutationCStarUnitary : Equiv.Perm ι →* unitary (CStarMatrix ι ι ℂ) where
  toFun p := ⟨CStarMatrix.ofMatrix ((p⁻¹).permMatrix ℂ), by
    constructor
    · change CStarMatrix.ofMatrix
        (((p⁻¹).permMatrix ℂ).conjTranspose * (p⁻¹).permMatrix ℂ) = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
    · change CStarMatrix.ofMatrix
        ((p⁻¹).permMatrix ℂ * ((p⁻¹).permMatrix ℂ).conjTranspose) = 1
      rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
      simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]⟩
  map_one' := by apply Subtype.ext; simp [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
  map_mul' p q := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (((p*q)⁻¹).permMatrix ℂ) =
      CStarMatrix.ofMatrix ((p⁻¹).permMatrix ℂ * (q⁻¹).permMatrix ℂ)
    rw [mul_inv_rev, Matrix.permMatrix_mul]

variable (F : Type*) [Group F] [Fintype F]

def finiteRegularMatrix : F →* unitary (CStarMatrix F F ℂ) :=
  permutationCStarUnitary.comp
    { toFun := Equiv.mulLeft, map_one' := Equiv.mulLeft_one, map_mul' := Equiv.mulLeft_mul }

lemma finiteRegularMatrix_norm (g : F) : ‖(finiteRegularMatrix F g : CStarMatrix F F ℂ)‖ = 1 :=
  CStarRing.norm_coe_unitary _

lemma finiteRegularMatrix_entry (g i j : F) :
    (finiteRegularMatrix F g : CStarMatrix F F ℂ) i j = if g⁻¹*i=j then 1 else 0 := by
  simp [finiteRegularMatrix, permutationCStarUnitary, Equiv.Perm.permMatrix, PEquiv.toMatrix]

theorem finiteRegularMatrix_trace (g : F) :
    (matrixTracialState (ι := F) complexScalarTracialState).functional (finiteRegularMatrix F g) =
      if g=1 then 1 else 0 := by
  by_cases hg : g=1
  · subst g
    simp [TracialState.normalized]
  · rw [ite_eq_right hg]
    have hd (i : F) : (finiteRegularMatrix F g : CStarMatrix F F ℂ) i i = 0 := by
      rw [finiteRegularMatrix_entry, ite_eq_right]
      intro he
      apply hg
      have h : g⁻¹=1 := mul_right_cancel (show g⁻¹*i = 1*i by simpa using he)
      exact inv_eq_one.mp h
    change (Fintype.card F : ℂ)⁻¹ * ∑ i, complexScalarTracialState.functional
      ((finiteRegularMatrix F g : CStarMatrix F F ℂ) i i) = 0
    simp [hd]

variable (G : Type*) [Group G] [Countable G] [Group.ResiduallyFinite G]

instance separatingQuotient_fintype (n : ℕ) : Fintype (SeparatingFiniteQuotient G n) :=
  Fintype.ofFinite _

def separatingMatrixModel (n : ℕ) : G →* unitary
    (CStarMatrix (SeparatingFiniteQuotient G n) (SeparatingFiniteQuotient G n) ℂ) :=
  (finiteRegularMatrix (SeparatingFiniteQuotient G n)).comp (separatingQuotientMap G n)

lemma separatingMatrixModel_norm (n : ℕ) (g : G) : ‖(separatingMatrixModel G n g :
    CStarMatrix (SeparatingFiniteQuotient G n) (SeparatingFiniteQuotient G n) ℂ)‖ = 1 :=
  CStarRing.norm_coe_unitary _

theorem separatingMatrixModel_trace_eventually (g : G) :
    ∀ᶠ n in Filter.atTop,
      (matrixTracialState (ι := SeparatingFiniteQuotient G n) complexScalarTracialState).functional
        (separatingMatrixModel G n g) = if g=1 then 1 else 0 := by
  by_cases hg : g=1
  · subst g
    exact Filter.Eventually.of_forall (fun n => by simp [TracialState.normalized])
  · filter_upwards [separatingQuotientMap_eventually_ne G g 1 hg] with n hn
    change (matrixTracialState (ι := SeparatingFiniteQuotient G n) complexScalarTracialState).functional
      (finiteRegularMatrix _ (separatingQuotientMap G n g)) = _
    rw [finiteRegularMatrix_trace, ite_eq_right hg, ite_eq_right]
    simpa using hn
end CuntzPureness

end

end OAI
