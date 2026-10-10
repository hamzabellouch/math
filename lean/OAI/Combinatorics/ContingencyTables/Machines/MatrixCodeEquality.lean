import OAI.Combinatorics.ContingencyTables.Sampling.ProfileCodeEquality
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram

namespace OAI

/-! # Polynomial equality of explicitly stored rectangular arrays -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

def matrixSignature (X : MatrixCode) : List ℕ×List ℕ := (X.map List.length,X.flatten)

def matrixSignatureRealizer : Realizer matrixSignature := pair (map listLength) flatten

lemma polynomial_matrixSignature : PolynomialTime matrixSignatureRealizer :=
  polynomial_pair (polynomial_map polynomial_listLength) polynomial_flatten

lemma matrixSignature_injective : Function.Injective matrixSignature := by
  intro X Y h
  exact List.eq_iff_flatten_eq.mpr ⟨congrArg Prod.snd h,congrArg Prod.fst h⟩

def matrixEqual : Realizer (fun z : MatrixCode×MatrixCode => decide (z.1=z.2)) :=
  (composition (pair (composition first matrixSignatureRealizer)
    (composition second matrixSignatureRealizer)) ProfilePrograms.profileCodeEqual).congr (by
      intro z
      simp only [Function.comp_apply,matrixSignature_injective.eq_iff])

lemma polynomial_matrixEqual : PolynomialTime matrixEqual := by
  unfold matrixEqual
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_matrixSignature)
    (polynomial_composition polynomial_second polynomial_matrixSignature))
    ProfilePrograms.polynomial_profileCodeEqual

lemma matrixCode_injective {m n : ℕ} :
    Function.Injective (matrixCode (m := m) (n := n)) := by
  intro X Y h
  have hi := List.ofFn_injective h
  funext i
  exact List.ofFn_injective (congrFun hi i)

end ContingencyTables.DensePrograms

end OAI
