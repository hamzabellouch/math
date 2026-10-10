import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.BinaryReduction

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

abbrev E := {x : ExplicitInput // 2 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k}
abbrev B := {x : BinaryInput // 2 ≤ x.n ∧ 1 ≤ x.k ∧ x.graph.EdgeConnected x.k}
abbrev eCode (x : E) : Word := x.val.encode
abbrev bCode (x : B) : Word := x.val.encode
abbrev fieldsCode := listCode binaryNatCode

def eFields (x : ExplicitInput) : List ℕ :=
  [x.n,x.m,x.k] ++ (List.ofFn fun i => [(x.graph.left i).val,(x.graph.right i).val]).flatten
def bFields (x : BinaryInput) : List ℕ :=
  [x.n,x.p,x.k] ++ (List.ofFn fun i => [(x.left i).val,(x.right i).val,x.multiplicity i]).flatten

lemma fieldsCode_flatten (rows : List (List ℕ)) :
    fieldsCode rows.flatten = (rows.map fieldsCode).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change listCode binaryNatCode (row ++ rows.flatten) =
      fieldsCode row ++ (rows.map fieldsCode).flatten
    rw [listCode_append]
    exact congrArg (List.append (fieldsCode row)) ih

lemma eFields_code (x : ExplicitInput) : fieldsCode (eFields x) = x.encode := by
  simp only [eFields,listCode_append,listCode_cons,listCode_nil,prodCode,PairRoutine.pair,
    fieldsCode_flatten,List.map_ofFn,Function.comp_def]
  simp [binaryNatCode,ExplicitInput.encode,
    CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat,List.append_assoc]
lemma bFields_code (x : BinaryInput) : fieldsCode (bFields x) = x.encode := by
  simp only [bFields,listCode_append,listCode_cons,listCode_nil,prodCode,PairRoutine.pair,
    fieldsCode_flatten,List.map_ofFn,Function.comp_def]
  simp [binaryNatCode,BinaryInput.encode,
    CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat,List.append_assoc]

abbrev eView : Realizes eCode fieldsCode (fun x => eFields x.val) :=
  (identity fieldsCode).reindex eCode (fun x => eFields x.val) (fun x => (eFields_code x.val).symm)
abbrev bView : Realizes bCode fieldsCode (fun x => bFields x.val) :=
  (identity fieldsCode).reindex bCode (fun x => bFields x.val) (fun x => (bFields_code x.val).symm)

def field (i : ℕ) : Realizes fieldsCode binaryNatCode (fun xs => xs.getD i 0) :=
  ((constant fieldsCode natCode i).both (identity fieldsCode)).then (getD binaryNatCode 0)
instance poly_field (i : ℕ) : PolyTime (field i) := by unfold field;infer_instance

def eNBinary : Realizes eCode binaryNatCode (fun x => x.val.n) :=
  (eView.then (field 0)).congr (by intro x;rfl)
def eMBinary : Realizes eCode binaryNatCode (fun x => x.val.m) :=
  (eView.then (field 1)).congr (by intro x;rfl)
def eKBinary : Realizes eCode binaryNatCode (fun x => x.val.k) :=
  (eView.then (field 2)).congr (by intro x;rfl)
def bNBinary : Realizes bCode binaryNatCode (fun x => x.val.n) :=
  (bView.then (field 0)).congr (by intro x;rfl)
def bPBinary : Realizes bCode binaryNatCode (fun x => x.val.p) :=
  (bView.then (field 1)).congr (by intro x;rfl)
def bKBinary : Realizes bCode binaryNatCode (fun x => x.val.k) :=
  (bView.then (field 2)).congr (by intro x;rfl)
instance poly_eNBinary : PolyTime eNBinary := by unfold eNBinary;apply poly_congr
instance poly_eMBinary : PolyTime eMBinary := by unfold eMBinary;apply poly_congr
instance poly_eKBinary : PolyTime eKBinary := by unfold eKBinary;apply poly_congr
instance poly_bNBinary : PolyTime bNBinary := by unfold bNBinary;apply poly_congr
instance poly_bPBinary : PolyTime bPBinary := by unfold bPBinary;apply poly_congr
instance poly_bKBinary : PolyTime bKBinary := by unfold bKBinary;apply poly_congr

lemma explicit_records_le (x : ExplicitInput) : x.m ≤ x.encode.length := by
  have h := record_count_le_bits (List.ofFn fun i : Fin x.m =>
    CurrentKS.encodeNat (x.graph.left i).val ++ CurrentKS.encodeNat (x.graph.right i).val) (by
      intro bits hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      have hh := framed_nat_length_pos (x.graph.left i).val
      simp only [List.length_append];omega)
  simp only [List.length_ofFn] at h
  simp only [ExplicitInput.encode,List.length_append]
  omega

lemma graph_dimensions {n m k : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hc : G.EdgeConnected k) : k ≤ m ∧ n ≤ 2*m := by
  classical
  have hsingle (v : Fin n) : ({v} : Finset (Fin n)) ≠ univ := by
    intro he
    have he := congrArg Finset.card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at he
    omega
  have hcard (S : Finset (Fin n)) : (G.cut univ S).card ≤ m := by
    have hh : G.cut univ S ⊆ univ := filter_subset _ _
    simpa only [card_univ,Fintype.card_fin] using card_le_card hh
  refine ⟨(hc {⟨0,by omega⟩} (singleton_nonempty _) (hsingle _)).trans (hcard _),?_⟩
  have hcover : univ ⊆ univ.image G.left ∪ univ.image G.right := by
    intro v _
    obtain ⟨e,he⟩ := card_pos.mp (lt_of_lt_of_le (by omega : 0<k)
      (hc {v} (singleton_nonempty _) (hsingle v)))
    rcases (mem_filter.mp he).2 with h | h
    · exact mem_union_left _ (mem_image.mpr ⟨e,mem_univ _,mem_singleton.mp h.1⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨e,mem_univ _,mem_singleton.mp h.1⟩)
  have h := (card_le_card hcover).trans (card_union_le _ _)
  have hl := card_image_le (s:=univ) (f:=G.left)
  have hr := card_image_le (s:=univ) (f:=G.right)
  simp only [card_univ,Fintype.card_fin] at *
  omega

lemma eM_bound (x : E) : x.val.m ≤ (eCode x).length := explicit_records_le _
lemma eN_bound (x : E) : x.val.n ≤ 2*(eCode x).length := by
  have h := (graph_dimensions x.val.graph x.property.1 x.property.2.1 x.property.2.2).2
  have h' := eM_bound x
  omega
lemma eK_bound (x : E) : x.val.k ≤ (eCode x).length :=
  (graph_dimensions x.val.graph x.property.1 x.property.2.1 x.property.2.2).1.trans (eM_bound x)
lemma bP_bound (x : B) : x.val.p ≤ (bCode x).length := x.val.records_le_encoding
lemma bN_bound (x : B) : x.val.n ≤ 2*(bCode x).length := by
  have h := x.val.vertices_le_twice_records x.property.1 x.property.2.1 x.property.2.2
  have h' := bP_bound x
  omega

lemma poly_bounded_binary {α : Type*} {ea : α → Word} {f : α → ℕ}
    (r : Realizes ea binaryNatCode f) [PolyTime r]
    (hf : IsPoly (fun a => (ea a).length) f) : PolyTime (r.then binaryToNat) := by
  have h := RunsPoly.of_poly r id (isPoly_self (fun a => (ea a).length))
  exact ⟨(h.then (runsPoly_binaryToNat f h.output hf)).cost⟩

def eN := eNBinary.then binaryToNat
def eM := eMBinary.then binaryToNat
def eK := eKBinary.then binaryToNat
def bN := bNBinary.then binaryToNat
def bP := bPBinary.then binaryToNat
instance poly_eN : PolyTime eN := by
  apply poly_bounded_binary
  exact ((isPoly_const _ 2).mul (isPoly_self _)).mono eN_bound
instance poly_eM : PolyTime eM := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono eM_bound
instance poly_eK : PolyTime eK := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono eK_bound
instance poly_bN : PolyTime bN := by
  apply poly_bounded_binary
  exact ((isPoly_const _ 2).mul (isPoly_self _)).mono bN_bound
instance poly_bP : PolyTime bP := by
  apply poly_bounded_binary
  exact (isPoly_self _).mono bP_bound

lemma records_lookup {n w : ℕ} (a b c : ℕ) (rows : Fin n → List ℕ)
    (hl : ∀i,(rows i).length=w) (i : Fin n) (j : ℕ) (hj : j<w) :
    ([a,b,c] ++ (List.ofFn rows).flatten).getD (3+i.val*w+j) 0 = (rows i).getD j 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons,List.length_nil];omega)]
  have he : 3+i.val*w+j-[a,b,c].length=i.val*w+j := by simp;omega
  rw [he]
  exact getD_flatten_ofFn rows hl i j hj 0

abbrev eEdgeCode := finFamilyCode eCode (fun x : E => x.val.m)
abbrev eeInput : Realizes eEdgeCode eCode (fun x => x.1) := familyFirst
abbrev eeIndex : Realizes eEdgeCode natCode (fun x => x.2.val) := familyIndex
abbrev bRecCode := finFamilyCode bCode (fun x : B => x.val.p)
abbrev brInput : Realizes bRecCode bCode (fun x => x.1) := familyFirst
abbrev brIndex : Realizes bRecCode natCode (fun x => x.2.val) := familyIndex

def eEndpointBinary (right : Bool) : Realizes eEdgeCode binaryNatCode
    (fun x => if right then (x.1.val.graph.right x.2).val else (x.1.val.graph.left x.2).val) :=
  ((((constant eEdgeCode natCode 3).nadd (eeIndex.nmul (constant eEdgeCode natCode 2))).nadd
    (constant eEdgeCode natCode (if right then 1 else 0))).both (eeInput.then eView)).then
      (getD binaryNatCode 0) |>.congr (by
        intro x
        have hh := records_lookup (w:=2) x.1.val.n x.1.val.m x.1.val.k
          (fun i => [(x.1.val.graph.left i).val,(x.1.val.graph.right i).val])
          (fun _ => rfl) x.2 (if right then 1 else 0) (by cases right <;> decide)
        cases right <;> simpa [eFields] using hh)
instance poly_eEndpointBinary (right : Bool) : PolyTime (eEndpointBinary right) := by
  unfold eEndpointBinary;infer_instance

def eEndpoint (right : Bool) := (eEndpointBinary right).then binaryToNat
instance poly_eEndpoint (right : Bool) : PolyTime (eEndpoint right) := by
  apply poly_bounded_binary
  apply ((isPoly_const _ 2).mul (isPoly_self _)).mono
  intro x
  have hv := eN_bound x.1
  have hl : (eCode x.1).length ≤ (eEdgeCode x).length :=
    le_prodCode_left (ea:=eCode) (eb:=natCode) (x.1,x.2.val)
  have h1 := (x.1.val.graph.left x.2).isLt
  have h2 := (x.1.val.graph.right x.2).isLt
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

def bRecordBinary (j : Fin 3) : Realizes bRecCode binaryNatCode
    (fun x => ([(x.1.val.left x.2).val,(x.1.val.right x.2).val,x.1.val.multiplicity x.2]).getD j.val 0) :=
  ((((constant bRecCode natCode 3).nadd (brIndex.nmul (constant bRecCode natCode 3))).nadd
    (constant bRecCode natCode j.val)).both (brInput.then bView)).then (getD binaryNatCode 0)
      |>.congr (fun x => records_lookup (w:=3) x.1.val.n x.1.val.p x.1.val.k
        (fun i => [(x.1.val.left i).val,(x.1.val.right i).val,x.1.val.multiplicity i])
        (fun _ => rfl) x.2 j.val j.isLt)
instance poly_bRecordBinary (j : Fin 3) : PolyTime (bRecordBinary j) := by
  unfold bRecordBinary;apply poly_congr

def bEndpointBinary (right : Bool) : Realizes bRecCode binaryNatCode
    (fun x => if right then (x.1.val.right x.2).val else (x.1.val.left x.2).val) :=
  (bRecordBinary (if right then 1 else 0)).congr (by intro x;cases right <;> rfl)
instance poly_bEndpointBinary (right : Bool) : PolyTime (bEndpointBinary right) := by
  unfold bEndpointBinary;infer_instance

def bEndpoint (right : Bool) := (bEndpointBinary right).then binaryToNat
instance poly_bEndpoint (right : Bool) : PolyTime (bEndpoint right) := by
  apply poly_bounded_binary
  apply ((isPoly_const _ 2).mul (isPoly_self _)).mono
  intro x
  have hv := bN_bound x.1
  have hl : (bCode x.1).length ≤ (bRecCode x).length :=
    le_prodCode_left (ea:=bCode) (eb:=natCode) (x.1,x.2.val)
  have h1 := (x.1.val.left x.2).isLt
  have h2 := (x.1.val.right x.2).isLt
  cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

end AlgorithmicThinTrees.InputStack
end

end OAI
