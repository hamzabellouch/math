import OAI.Computability.MatchingCount.CappedPower

namespace OAI

section

namespace BinaryMatching.Raw.Optimize
open Algorithm Finset StackCode
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

abbrev Row := Matrix ℤ × ℤ
abbrev IntState := Matrix ℤ × Option ℤ
structure Params where
  n : ℕ
  q : ℕ
  k : ℕ
  L : ℕ
  D : ℕ
  M : ℕ
  pow : ℕ
  beta : Matrix ℤ
  deriving Inhabited
abbrev ParamData := ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×(ℕ×Matrix ℤ))))))
def Params.repr (p : Params) : ParamData := (p.n,(p.q,(p.k,(p.L,(p.D,(p.M,(p.pow,p.beta)))))))
instance : Coding Params := ⟨fun p => encode p.repr⟩
def Params.ofData (z : ParamData) : Params := ⟨z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩

@[simp] lemma Params.ofData_repr (p : Params) : Params.ofData p.repr=p := rfl

def tableRep {n : ℕ} (a : Table n ℤ) : Matrix ℤ := matrixRep (fun i j => a[i][j])
def rowRep {n : ℕ} (r : Affine n) : Row := (tableRep (toTable r.coeff),r.constant)
def stateRep {n : ℕ} (s : IntegralState n) : IntState := (tableRep s.numerators,s.best)
def params (G : Input) : Params := ⟨G.n,q G.n,K G.n,L G,D₀ G,M₀ G,2^(K G.n),tableRep (toTable (Algorithm.beta G))⟩

def upperSum (n : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  (tab n (fun i => (tab n (fun j => if i<j then f i j else 0)).sum)).sum

lemma upperSum_rep {n : ℕ} (f : Pair n → ℤ) (g : ℕ → ℕ → ℤ)
    (h : ∀ e : Pair n,g e.val.1.val e.val.2.val=f e) : upperSum n g=∑ e,f e := by
  unfold upperSum
  rw [sum_tab]
  simp_rw [sum_tab]
  have hh : ∀ i j : Fin n,(if i.val<j.val then g i.val j.val else 0)=
      if h' : i<j then f ⟨(i,j),h'⟩ else 0 := by
    intro i j
    by_cases hij : i<j
    · simp only [dite_eq_left hij,show i.val<j.val from hij,ite_true]
      exact h ⟨(i,j),hij⟩
    · simp only [dite_eq_right hij,show ¬i.val<j.val from hij,ite_false]
  simp_rw [hh]
  rw [←Fintype.sum_prod_type (f := fun ij : Fin n×Fin n => if h' : ij.1 < ij.2 then f ⟨ij,h'⟩ else 0)]
  symm
  apply Fintype.sum_of_injective (fun e : Pair n => e.val) Subtype.val_injective f _
  · intro ij hij
    by_cases h' : ij.1 < ij.2
    · exact False.elim (hij ⟨⟨ij,h'⟩,rfl⟩)
    · simp only [dite_eq_right h']
  · intro e
    simp only [dite_eq_left e.property]

lemma get_tableRep {n : ℕ} (a : Table n ℤ) (i j : Fin n) : get (tableRep a) i.val j.val=a[i][j] :=
  get_rep _ _ _
lemma get_rowRep {n : ℕ} (r : Affine n) (e : Pair n) : get (rowRep r).1 e.val.1.val e.val.2.val=r.coeff e := by
  rw [rowRep,get_tableRep]
  exact at_toTable _ e
lemma get_beta (G : Input) (e : Pair G.n) : get (params G).beta e.val.1.val e.val.2.val=Algorithm.beta G e := by
  change get (tableRep (toTable (Algorithm.beta G))) e.val.1.val e.val.2.val=_
  rw [get_tableRep]
  exact at_toTable _ e

def rowNumerator (D : ℕ) (a : Matrix ℤ) (r : Row) : ℤ :=
  upperSum a.length (fun i j => get r.1 i j*get a i j)+r.2*D
lemma tableRep_length {n : ℕ} (a : Table n ℤ) : (tableRep a).length=n := by simp [tableRep,matrixRep,vectorRep]
lemma rowNumerator_rep {n : ℕ} (D : ℕ) (a : Table n ℤ) (r : Affine n) :
    rowNumerator D (tableRep a) (rowRep r)=Algorithm.rowNumerator D a r := by
  unfold rowNumerator Algorithm.rowNumerator
  rw [tableRep_length]
  congr 1
  apply upperSum_rep
  intro e
  rw [get_rowRep,get_tableRep]
  rfl

def indexedSlope (k j : ℕ) : ℤ := if j<k then (j:ℤ)-1 else k
def pieceNumerator (k D pow : ℕ) (a : ℤ) (j : ℕ) : ℤ :=
  indexedSlope k j*a*pow+if j<k then (D:ℤ)*(cappedPow2 pow (k-j):ℕ) else 0
lemma pieceNumerator_rep (k D : ℕ) (a : ℤ) (j : ℕ) :
    pieceNumerator k D (2^k) a j=Algorithm.pieceNumerator k D a j := by
  have hp : 2^(k-j)≤2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  simp only [pieceNumerator,cappedPow2_of_le _ _ hp,Algorithm.pieceNumerator,
    indexedSlope,indexedPiece]
  split_ifs <;> push_cast <;> rfl

def selectedIndex (k D pow : ℕ) (a : ℤ) : ℕ :=
  ((List.range (k+1)).argmin (pieceNumerator k D pow a)).getD k
lemma selectedIndex_rep (k D : ℕ) (a : ℤ) : selectedIndex k D (2^k) a=Algorithm.selectedIndex k D a := by
  have hf : pieceNumerator k D (2^k) a=Algorithm.pieceNumerator k D a := funext (pieceNumerator_rep k D a)
  rw [selectedIndex,Algorithm.selectedIndex,hf]
def scaledPsi (p : Params) (a : ℤ) : ℤ := pieceNumerator p.k p.D p.pow a (selectedIndex p.k p.D p.pow a)
def scaledSlope (p : Params) (a : ℤ) : ℤ := indexedSlope p.k (selectedIndex p.k p.D p.pow a)
lemma scaledPsi_rep (G : Input) (a : ℤ) : scaledPsi (params G) a=Algorithm.scaledPsi (K G.n) (D₀ G) a := by
  simp only [scaledPsi,params,selectedIndex_rep,pieceNumerator_rep,Algorithm.scaledPsi]
lemma scaledSlope_rep (G : Input) (a : ℤ) : scaledSlope (params G) a=Algorithm.scaledSlope (K G.n) (D₀ G) a := by
  simp only [scaledSlope,params,selectedIndex_rep,Algorithm.scaledSlope,indexedSlope,indexedPiece]
  split_ifs <;> rfl
end BinaryMatching.Raw.Optimize
end

end OAI
