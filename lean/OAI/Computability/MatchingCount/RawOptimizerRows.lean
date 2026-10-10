import OAI.Computability.MatchingCount.RawOddCompiler

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

def capacities (n : ℕ) (a : Matrix ℤ) : Matrix ℕ :=
  matrix n (fun i j => if i < j then (get a i j).toNat else if j < i then (get a j i).toNat else 0)
lemma capacities_rep {n : ℕ} (a : Table n ℤ) :
    capacities n (tableRep a)=matrixRep (Algorithm.capacities a) := by
  apply matrix_eq_rep
  intro i j
  simp only [get_tableRep,Algorithm.capacities,Fin.lt_def]

def zeroRow (n : ℕ) : Row := (matrix n (fun _ _ => 0),0)
def degreeRow (n v : ℕ) (positive : Bool) : Row :=
  (matrix n (fun i j => if i < j then
    if i=v ∨ j=v then (if positive then 1 else -1) else 0 else 0),if positive then -1 else 1)
def cutRow (n : ℕ) (S : Cut) : Row :=
  (matrix n (fun i j => if i < j then
    if (mem S i && !mem S j) || (mem S j && !mem S i) then -1 else 0 else 0),1)
lemma zeroRow_rep (n : ℕ) : zeroRow n=rowRep (Algorithm.zeroRow (n := n)) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    simp [toTable,tabulate,Algorithm.zeroRow]
  · rfl
lemma degreeRow_rep {n : ℕ} (v : Fin n) (b : Bool) : degreeRow n v.val b=rowRep (Algorithm.degreeRow v b) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.degreeRow,Fin.ext_iff,h]
  · rfl
lemma cutRow_rep {n : ℕ} (S : Finset (Fin n)) : cutRow n (cutRep S)=rowRep (Algorithm.cutRow S) := by
  apply Prod.ext
  · apply matrix_eq_rep
    intro i j
    by_cases h : i < j <;> simp [toTable,tabulate,Algorithm.cutRow,h]
  · rfl

def rows (n : ℕ) (a : Matrix ℤ) : List Row :=
  zeroRow n :: ((List.range n).flatMap (fun v => [degreeRow n v true,degreeRow n v false])) ++
    [cutRow n (oddFlat (n,(capacities n a,full n)))]
lemma rows_rep {n : ℕ} (hn : 2≤n) (he : Even n) (a : Table n ℤ) :
    rows n (tableRep a)=(integralRows a).map rowRep := by
  have hu : (univ : Finset (Fin n)).card=n := Fintype.card_fin n
  unfold rows integralRows
  rw [capacities_rep,full_rep,oddFlat_rep _ _ (by simpa only [hu] using he) (by simpa only [hu] using hn)]
  simp only [zeroRow_rep,cutRow_rep,List.map_append,List.map_cons,List.map_nil,
    DenseOracle.oddCut_eq,DenseOracle.view_make]
  congr 2
  rw [range_eq_fin,List.flatMap_map,List.map_flatMap]
  congr 1
  funext v
  simp only [degreeRow_rep,List.map_cons,List.map_nil]

lemma argmax_map {α β γ : Type} [Preorder γ] [DecidableLT γ] (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmax g=(l.argmax (g ∘ f)).map f :=
  @StackCode.argmin_map_exact α β γᵒᵈ _ _ l f g

def selectedRow (n D : ℕ) (a : Matrix ℤ) : Row :=
  ((rows n a).argmax (rowNumerator D a)).getD (zeroRow n)
lemma selectedRow_rep {n : ℕ} (hn : 2≤n) (he : Even n) (D : ℕ) (a : Table n ℤ) :
    selectedRow n D (tableRep a)=rowRep (integralRow D a) := by
  unfold selectedRow integralRow
  rw [rows_rep hn he,argmax_map]
  have hf : rowNumerator D (tableRep a) ∘ rowRep=Algorithm.rowNumerator D a := by
    funext r
    exact rowNumerator_rep D a r
  rw [hf]
  cases h : (integralRows a).argmax (Algorithm.rowNumerator D a) with
  | none => exact zeroRow_rep n
  | some r => rfl
end BinaryMatching.Raw.Optimize
end

end OAI
