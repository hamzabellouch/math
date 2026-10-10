import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentListSemantics

namespace OAI

/-! # A polynomial exact acceptance test for a free integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

def completionNonnegative (z : CompletionCell) : Bool :=
  decide ((completionParts z).2≤(completionParts z).1)

def completionNonnegativeRealizer : Realizer completionNonnegative :=
  composition (composition completionPartsRealizer (pair second first)) leNat

theorem polynomial_completionNonnegative : PolynomialTime completionNonnegativeRealizer :=
  polynomial_composition (polynomial_composition polynomial_completionParts
    (polynomial_pair polynomial_second polynomial_first)) polynomial_leNat

def completionValid (z : CompletionData) : Bool :=
  (cellPairs z.1).all (fun ij => completionNonnegative (z,ij))

def completionValidRealizer : Realizer completionValid :=
  (composition (composition (pair identity (composition first cellPairsRealizer))
    (mapWith completionNonnegativeRealizer)) all).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,completionValid])

theorem polynomial_completionValid : PolynomialTime completionValidRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_cellPairs))
    (polynomial_mapWith polynomial_completionNonnegative)) polynomial_all)

theorem completionNonnegative_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    completionNonnegative (((marginCode R,marginCode P),matrixCode z),
      (optionIndex i,optionIndex j))=true ↔
      0≤DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  have h := completionParts_signed R P z i j
  simp only [completionNonnegative,decide_eq_true_eq]
  dsimp only at h
  omega

theorem completionValid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (z : Fin m → Fin n → ℕ) :
    completionValid ((marginCode R,marginCode P),matrixCode z)=true ↔
      ∀ i j,0≤DenseAffine.integerTable R P (fun ij => z ij.1 ij.2) i j := by
  simp only [completionValid,List.all_eq_true]
  constructor
  · intro h i j
    apply (completionNonnegative_code R P z i j).mp
    apply h
    apply (mem_cellPairs _ _ _ _).mpr
    simpa only [marginCode,List.length_cons,List.length_ofFn] using
      And.intro (optionIndex_lt i) (optionIndex_lt j)
  · intro h ij hij
    obtain ⟨i,j⟩ := ij
    have hh := (mem_cellPairs _ _ i j).mp hij
    simp only [marginCode,List.length_cons,List.length_ofFn] at hh
    obtain ⟨a,ha⟩ := exists_optionIndex i hh.1
    obtain ⟨b,hb⟩ := exists_optionIndex j hh.2
    subst i
    subst j
    exact (completionNonnegative_code R P z a b).mpr (h a b)

end ContingencyTables.DensePrograms

end OAI
