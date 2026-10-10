import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCodeProposal
import OAI.Combinatorics.ContingencyTables.Machines.BinaryExchangeProgram

namespace OAI

/-! # The small-cell ordering is computed from the encoded margins -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => d^20
local notation "small" => paperSmall r c

def computedCatalog : List (ℕ×ℕ) := smallCellCatalog ((List.ofFn r,List.ofFn c),U)

lemma computedCatalog_nodup : (computedCatalog r c).Nodup :=
  (cellPairs_nodup (List.ofFn r) (List.ofFn c)).filter _

lemma mem_computedCatalog (ij : ℕ×ℕ) :
    ij∈computedCatalog r c ↔ ∃ a : Cells small,((a.val.1.val,a.val.2.val):ℕ×ℕ)=ij := by
  rw [computedCatalog,mem_smallCellCatalog]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨hi,hj,hsmall⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have hs : small i j=true := by
      apply decide_eq_true
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,hj,dite_true,
        Option.getD_some] using hsmall
    exact ⟨⟨(i,j),hs⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a.val.1.isLt,a.val.2.isLt,?_⟩
    have hs : r a.val.1<U ∨ c a.val.2<U := of_decide_eq_true a.property
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,a.val.1.isLt,a.val.2.isLt,
      dite_true,Option.getD_some,Fin.eta] using hs

def catalogCell (i : Fin (computedCatalog r c).length) : Cells small :=
  Classical.choose ((mem_computedCatalog r c ((computedCatalog r c)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_coordinates (i : Fin (computedCatalog r c).length) :
    ((catalogCell r c i).val.1.val,(catalogCell r c i).val.2.val)=
      (computedCatalog r c)[i.val] :=
  Classical.choose_spec ((mem_computedCatalog r c ((computedCatalog r c)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_bijective : Function.Bijective (catalogCell r c) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : Cells small => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((computedCatalog_nodup r c).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈computedCatalog r c :=
      (mem_computedCatalog r c _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates r c ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def computedCellEquiv : Fin (computedCatalog r c).length ≃ Cells small :=
  Equiv.ofBijective (catalogCell r c) (catalogCell_bijective r c)

/-- The proof-level cell equivalence enumerates exactly the list made
by the polynomial catalog program, in the same order. -/
theorem computedCellEquiv_catalog :
    cellCatalog small (computedCellEquiv r c)=computedCatalog r c := by
  apply List.ext_getElem
  · simp only [cellCatalog,List.length_ofFn]
  · intro i hi hj
    simp only [cellCatalog,List.getElem_ofFn]
    exact catalogCell_coordinates r c ⟨i,hj⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
