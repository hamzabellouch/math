import OAI.Combinatorics.ContingencyTables.Rooted.ComputedForestCode
import OAI.Combinatorics.ContingencyTables.Transport.ComputedCompanionInstance
import OAI.Combinatorics.ContingencyTables.Rooted.RootedDemandProgram

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

abbrev Input := NetworkVertexCode.Input×ℕ

def forestFrame (z : Input) : LargeEdgeCatalogProgram.Input :=
  (TightenedInputProgram.compute z.1,z.2)
def forestFrameRealizer : Realizer forestFrame :=
  pair (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
    first TightenedInputProgram.computeRealizer) second
lemma polynomial_forestFrame : PolynomialTime forestFrameRealizer :=
  polynomial_pair (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
    polynomial_second

def catalogData (z : Input) : RootedForestCatalog.Data :=
  (((ForestGreedyProgram.forest (forestFrame z),z.2),(TightenedInputProgram.compute z.1).1),
    (TightenedInputProgram.compute z.1).2)
def catalogDataRealizer : Realizer catalogData :=
  pair (pair (pair
    (composition (f := forestFrame) (g := ForestGreedyProgram.forest)
      forestFrameRealizer ForestGreedyProgram.forestRealizer) second)
    (composition (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
      first TightenedInputProgram.computeRealizer) first))
    (composition (composition (f := fun z : Input => z.1) (g := TightenedInputProgram.compute)
      first TightenedInputProgram.computeRealizer) second)
lemma polynomial_catalogData : PolynomialTime catalogDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_forestFrame ForestGreedyProgram.polynomial_forest) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
      polynomial_first))
    (polynomial_composition (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
      polynomial_second)

def prepared (z : Input) : RootedForestCatalog.Data×MatrixCode :=
  (catalogData z,TightenedInputProgram.baseline z.1)
def preparedRealizer : Realizer prepared :=
  pair catalogDataRealizer (composition (f := fun z : Input => z.1)
    (g := TightenedInputProgram.baseline) first TightenedInputProgram.baselineRealizer)
lemma polynomial_prepared : PolynomialTime preparedRealizer :=
  polynomial_pair polynomial_catalogData
    (polynomial_composition polynomial_first TightenedInputProgram.polynomial_baseline)

open scoped Classical
variable {m n : ℕ}

lemma catalogData_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    catalogData (data r c b,W)=RootedForestCatalog.data
      (ComputedCompanionInstance.instanceData hEK r c b hne W hW) := by
  unfold catalogData forestFrame
  rw [TightenedInputProgram.compute_code]
  unfold RootedForestCatalog.data ComputedCompanionInstance.instanceData
  rw [ComputedLargeForest.computed_code _ _ _ W (by omega)]
  simp only [data,Int.toNat_natCast,ResidualGraphProgram.natCode,matrixCode]

lemma baseline_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    TightenedInputProgram.baseline (data r c b)=matrixCode
      (fun i j => ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat) := by
  obtain ⟨Y,hY,_,_⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  rw [hY]
  unfold matrixCode
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [ComputedCompanionInstance.instanceData,ComputedCompanionInstance.baseline,
    hY,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Int.toNat_natCast]

lemma prepared_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    prepared (data r c b,W)=
      (RootedForestCatalog.data (ComputedCompanionInstance.instanceData hEK r c b hne W hW),
        matrixCode (fun i j =>
          ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat)) := by
  exact Prod.ext (catalogData_instance hEK r c b hne W hW)
    (baseline_instance hEK r c b hne W hW)

end ContingencyTables.ComputedRootedInput

end OAI
