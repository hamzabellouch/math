import OAI.Combinatorics.ParityLifts.BitNormalize

namespace OAI

namespace ParityWL.Complexity

lemma bitSat_literal_map {N : ℕ} (F : ClauseList (Literal N)) (a : Name → Bool) :
    bitSat a (ClauseList.map literalBits F) ↔
      Sparsification.Holds (listCNF F) (fun l => a l.1.val.bits=l.2) := by
  rw [listCNF_holds]
  simp only [bitSat,ClauseList.map,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro h C hC
    obtain ⟨l,hl,he⟩ := h _ C hC rfl
    obtain ⟨l',hl',rfl⟩ := List.mem_map.mp hl
    exact ⟨l',hl',he⟩
  · intro h C D hD he
    subst C
    obtain ⟨l,hl,hv⟩ := h D hD
    exact ⟨literalBits l,List.mem_map.mpr ⟨l,hl,rfl⟩,hv⟩

lemma literal_assignment_extend {N : ℕ} (a : Fin N → Bool) :
    ∃ b : Name → Bool, ∀ i : Fin N, b i.val.bits=a i := by
  let b : Name → Bool := fun w => if h : decodeBits w<N then a ⟨decodeBits w,h⟩ else false
  refine ⟨b,?_⟩
  intro i
  simp only [b,decodeBits_bits,dite_eq_left i.isLt]

lemma holds_minimizeList {α : Type} [DecidableEq α] (F : ClauseList α) (v : α → Prop) :
    Sparsification.Holds (listCNF (minimizeList F)) v ↔ Sparsification.Holds (listCNF F) v := by
  rw [listCNF_minimize]
  exact Sparsification.minimize_holds _ _

def literalSizeBound (N : ℕ) : ℕ := 1+4*(2*N+1)^3*(2+3*(4*N+6))

def sparseDensity (r N : ℕ) : ℕ := 1+2*N*(1+r^2+2*(r^4)^2)

/-- Bit-string certificates are for the very same deterministic sparse program,
not an oracle for a mathematically chosen family. -/
theorem bit_sparse_certificate {N : ℕ} (F : Formula N) (j : ℕ) (hj : 0<j) :
    ∃ T : SparseTree BitLiteral,
      T.root=minimizeList F.bitList ∧ T.Valid (12*j) ∧
      T.All (fun H => (treeEncode H).size≤literalSizeBound N) ∧
      (T.leaves.length : ℝ)≤(2 : ℝ)^((N : ℝ)/j) ∧
      (∀ H∈T.leaves, H.length ≤ sparseDensity (12*j) N ∧ ∀ C∈H, C.length≤3) ∧
      ((∃ H∈T.leaves, ∃ a, bitSat a H) ↔ F.Satisfiable) := by
  let _ := literalCodec N
  let r := 12*j
  have hr : 0<r := by dsimp [r]; omega
  let F₀ := minimizeList F.literalLists
  let s := Sparsification.initialState (listCNF F.literalLists) F.listCNF_width (r^2)
  have hs : listCNF F₀=s.formula := listCNF_minimize F.literalLists
  obtain ⟨U,hroot,hvalid,hleaf,hholds,hcount⟩ := sparse_tree_exists hr s F₀ hs
  have hctrl : U.All (ListControlled (4*N+5)) :=
    U.controlled hvalid (hroot ▸ F.controlled)
  let T := U.map literalBits
  have henc (l : Literal N) : treeEncode (literalBits l)=treeEncode l := rfl
  have hc : Fintype.card (Literal N)=2*N := by simp only [Literal,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; omega
  have hleaves : (U.leaves.length : ℝ)≤(2 : ℝ)^((N : ℝ)/j) := by
    have hb : 1≤Sparsification.branchBase r^s.spent :=
      one_le_pow₀ (Sparsification.branchBase_gt_one hr).le
    calc
      _ ≤ (U.leaves.length : ℝ)*Sparsification.branchBase r^s.spent :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) hb
      _ ≤ _ := hcount
      _ ≤ _ := by rw [hc]; exact Sparsification.indexed_rate_bound j N hj
  refine ⟨T,?_,U.map_valid literalBits henc r hvalid,?_,?_,?_,?_⟩
  · simp only [T,SparseTree.map_root,hroot,F₀]
    exact (minimizeList_map_encode literalBits henc F.literalLists).symm
  · apply U.map_all literalBits (ListControlled (4*N+5)) _ _ hctrl
    intro H hH
    rw [ClauseList.map_encode literalBits henc]
    simpa only [literalSizeBound,hc] using hH.size
  · simpa only [T,SparseTree.map_leaves,List.length_map] using hleaves
  · intro H hH
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp (show H∈U.leaves.map (ClauseList.map literalBits) from by simpa only [T,SparseTree.map_leaves] using hH)
    have hGctrl := hctrl.leaf G hG
    obtain ⟨_,hw,hn2,hn31,hn32⟩ := hleaf G hG
    have hd := Sparsification.sparse_leaf_density (listCNF G) (r^2) (r^4) (pow_pos hr _) hw hn2 hn31 hn32
    have hlen : G.length=(listCNF G).card := by
      simpa only [listCNF,List.length_map] using (List.toFinset_card_of_nodup hGctrl.1).symm
    refine ⟨?_,?_⟩
    · simpa only [ClauseList.map,List.length_map,sparseDensity,hlen,hc,r] using hd
    · intro C hC
      obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hC
      simpa only [List.length_map] using (hGctrl.2 D hD).1
  · have hrholds (a : Name → Bool) :
        (∃ H∈T.leaves, bitSat a H) ↔ F.Satisfied (fun i => a i.val.bits) := by
      simp only [T,SparseTree.map_leaves,List.mem_map,exists_exists_and_eq_and,bitSat_literal_map]
      rw [← hholds,holds_minimizeList]
      exact F.listCNF_sat (fun i => a i.val.bits)
    constructor
    · rintro ⟨H,hH,a,ha⟩
      exact ⟨_,(hrholds a).mp ⟨H,hH,ha⟩⟩
    · rintro ⟨a,ha⟩
      obtain ⟨b,hb⟩ := literal_assignment_extend a
      have hs : F.Satisfied (fun i => b i.val.bits) := by simpa only [hb] using ha
      obtain ⟨H,hH,hh⟩ := (hrholds b).mpr hs
      exact ⟨H,hH,b,hh⟩

end ParityWL.Complexity

end OAI
