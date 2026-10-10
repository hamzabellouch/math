import OAI.Combinatorics.ParityLifts.SparseEncoding

namespace OAI

namespace ParityWL.Complexity

def decodeBits : List Bool → ℕ := List.foldr Nat.bit 0

lemma decodeBits_bits (n : ℕ) : decodeBits n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    change Nat.bit b (decodeBits n.bits)=Nat.bit b n
    rw [ih]

def literalBits {N : ℕ} (l : Literal N) : BitLiteral := (l.1.val.bits,l.2)

lemma literalBits_injective (N : ℕ) : Function.Injective (@literalBits N) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  have hv : a.1.val=b.1.val := by
    simpa only [literalBits,decodeBits_bits] using congrArg decodeBits h1
  exact Prod.ext (Fin.ext hv) h2

@[instance_reducible] def literalCodec (N : ℕ) : TreeCodec (Literal N) where
  encode := fun l => treeEncode (literalBits l)
  injective := fun _ _ h => literalBits_injective N (TreeCodec.injective h)

def Formula.literalLists {N : ℕ} (F : Formula N) : ClauseList (Literal N) := F.map Clause.literals

def Formula.bitList {N : ℕ} (F : Formula N) : BitFormula :=
  List.map (List.map literalBits) F.literalLists

lemma Formula.bitList_parse {N : ℕ} (F : Formula N) : F.bitList=parseFormula (encodeFormula F) := by
  rw [parseFormula_encode]
  simp only [bitList,literalLists,List.map_map,Function.comp_def]
  rfl

lemma Formula.literalLists_width {N : ℕ} (F : Formula N) :
    ∀ C∈F.literalLists, C.length≤3 := by
  intro C hC
  obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hC
  exact D.width

lemma nat_bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

lemma literalBits_size {N : ℕ} (l : Literal N) : (treeEncode (literalBits l)).size≤4*N+5 := by
  have hs := treeEncode_bits_size l.1.val.bits
  have hn := (nat_bits_length_le l.1.val).trans l.1.isLt.le
  have hb : (treeEncode l.2).size≤3 := by cases h : l.2 <;> simp [DataTree.size]
  simp only [literalBits,treeEncode_pair,DataTree.size]
  omega

lemma Formula.controlled {N : ℕ} (F : Formula N) :
    letI := literalCodec N
    ListControlled (4*N+5) (minimizeList F.literalLists) := by
  let _ := literalCodec N
  apply minimize_controlled
  intro C hC
  refine ⟨F.literalLists_width C hC,?_⟩
  intro l hl
  exact literalBits_size l

lemma Formula.listCNF_width {N : ℕ} (F : Formula N) :
    ∀ C∈listCNF F.literalLists, C.card≤3 := by
  intro C hC
  obtain ⟨D,hD,rfl⟩ := mem_listCNF.mp hC
  exact (List.toFinset_card_le D).trans (F.literalLists_width D hD)

lemma Formula.listCNF_sat {N : ℕ} (F : Formula N) (a : Fin N → Bool) :
    Sparsification.Holds (listCNF F.literalLists) (fun l => a l.1=l.2) ↔ F.Satisfied a := by
  rw [listCNF_holds]
  simp only [literalLists,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h C hC; exact h C.literals C hC rfl
  · intro h C D hD he; subst C; exact h D hD

lemma Formula.bitList_sat {N : ℕ} (F : Formula N) (a : Name → Bool) :
    bitSat a F.bitList ↔ F.Satisfied (fun i => a i.val.bits) := by
  simp only [bitSat,bitList,literalLists,List.map_map,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h C hC
    obtain ⟨l,hl,he⟩ := h _ C hC rfl
    obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hl
    exact ⟨l',hl',he⟩
  · intro h C D hD he
    subst C
    obtain ⟨l,hl,hv⟩ := h D hD
    exact ⟨literalBits l,List.mem_map.mpr ⟨l,hl,rfl⟩,hv⟩

lemma Formula.bitList_satisfiable {N : ℕ} (F : Formula N) :
    (∃ a, bitSat a F.bitList) ↔ F.Satisfiable := by
  constructor
  · rintro ⟨a,ha⟩; exact ⟨_,(F.bitList_sat a).mp ha⟩
  · rintro ⟨a,ha⟩
    let b : Name → Bool := fun w => if h : decodeBits w<N then a ⟨decodeBits w,h⟩ else false
    refine ⟨b,(F.bitList_sat b).mpr ?_⟩
    have hb (i : Fin N) : b i.val.bits=a i := by simp only [b,decodeBits_bits,dite_eq_left i.isLt]
    simpa only [hb] using ha

end ParityWL.Complexity

end OAI
