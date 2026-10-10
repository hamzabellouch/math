import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileValidator

namespace OAI

/-! # Literal lists encode exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

def profileCode (z : SmallProfile small) : List ℕ×List ℕ :=
  (viewList small e z false,viewList small e z true)

def profileOfCode (v : List ℕ×List ℕ) : SmallProfile small :=
  fun a => (if a.2 then v.2 else v.1).getD (e.symm a.1).val 0

lemma profileOfCode_code (z : SmallProfile small) :
    profileOfCode small e (profileCode small e z)=z := by
  funext a
  rcases a with ⟨a,b⟩
  cases b <;>
    simp only [profileOfCode,profileCode,viewList,Bool.false_eq_true,ite_false,ite_true,
      List.getD_eq_getElem?_getD,List.getElem?_ofFn,(e.symm a).isLt,dite_true,
      Option.getD_some,Fin.eta,Equiv.apply_symm_apply]

theorem profileCode_injective : Function.Injective (profileCode small e) := by
  intro z w h
  have hh := congrArg (profileOfCode small e) h
  simpa only [profileOfCode_code] using hh

private lemma ofFn_getD (xs : List ℕ) (h : xs.length=q) :
    List.ofFn (fun i : Fin q => xs.getD i.val 0)=xs := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.symm
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      Option.getD_some]

lemma profileCode_ofCode (v : List ℕ×List ℕ) (hx : v.1.length=q) (hy : v.2.length=q) :
    profileCode small e (profileOfCode small e v)=v := by
  apply Prod.ext
  · simpa only [profileCode,viewList,profileOfCode,Bool.false_eq_true,ite_false,
      Equiv.symm_apply_apply] using ofFn_getD v.1 hx
  · simpa only [profileCode,viewList,profileOfCode,ite_true,
      Equiv.symm_apply_apply] using ofFn_getD v.2 hy

def codeCheckData (catalog : List (ℕ×ℕ)) (r c : List ℕ) (U : ℕ)
    (v : List ℕ×List ℕ) : ProfileCheckData := (((catalog,v),(r,c)),U)

/-- For arbitrary input lists, the Boolean program succeeds exactly
when those lists encode an actual positive-completion state. -/
theorem profileTest_code_iff (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c))
    (v : List ℕ×List ℕ) :
    profileTest (codeCheckData (cellCatalog (paperSmall r c) e) (List.ofFn r) (List.ofFn c)
      ((dimensionAllowance (I := Fin m) (J := Fin n))^20) v)=true ↔
      ∃ x : PaperStates r c,profileCode (paperSmall r c) e
        (physicalProfile (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := Fin m) (J := Fin n))^12) x)=v := by
  constructor
  · intro h
    have hx : v.1.length=q := by
      have hh := (Bool.and_eq_true_iff.mp h).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    have hy : v.2.length=q := by
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    let z := profileOfCode (paperSmall r c) e v
    have hz : profileCode (paperSmall r c) e z=v := profileCode_ofCode _ _ v hx hy
    have hp : ProfileFeasible r c z := by
      apply (profileTest_iff r c htotal e z).mp
      change profileTest (codeCheckData (cellCatalog (paperSmall r c) e)
        (List.ofFn r) (List.ofFn c) ((dimensionAllowance (I := Fin m) (J := Fin n))^20)
        (profileCode (paperSmall r c) e z))=true
      rwa [hz]
    exact ⟨stateOfFeasible r c z hp,hz⟩
  · rintro ⟨x,rfl⟩
    exact (profileTest_iff r c htotal e _).mpr (physicalProfile_feasible r c x)

end
end ContingencyTables.SmallGraphProfiles

end OAI
