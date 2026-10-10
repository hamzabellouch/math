import OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternProgram

namespace OAI

/-! # A binary program checking every stored coordinate bound -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def boundedValues (z : ℕ×List ℕ) : Bool := z.2.all (fun a => decide (a≤z.1))

def boundedValuesRealizer : Realizer boundedValues :=
  (composition (mapWith (composition (pair second first) leNat)) all).congr (by
    intro z
    simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,boundedValues])

theorem polynomial_boundedValues : PolynomialTime boundedValuesRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first) polynomial_leNat)) polynomial_all)

lemma boundedValues_ofFn {n : ℕ} (U : ℕ) (v : Fin n → ℕ) :
    boundedValues (U,List.ofFn v)=true ↔ ∀ i,v i≤U := by
  simp only [boundedValues,List.all_eq_true,List.mem_ofFn,decide_eq_true_eq]
  constructor
  · intro h i
    exact h (v i) ⟨i,rfl⟩
  · intro h a ha
    obtain ⟨i,rfl⟩ := ha
    exact h i

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem boundedValues_views (z : SmallProfile small) (U : ℕ) :
    (boundedValues (U,viewList small e z false) &&
      boundedValues (U,viewList small e z true))=true ↔ ∀ a,z a≤U := by
  simp only [Bool.and_eq_true,viewList,boundedValues_ofFn]
  constructor
  · rintro ⟨hx,hy⟩ ⟨a,b⟩
    cases b
    · simpa only [e.apply_symm_apply] using hx (e.symm a)
    · simpa only [e.apply_symm_apply] using hy (e.symm a)
  · intro h
    exact ⟨fun i => h (e i,false),fun i => h (e i,true)⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
