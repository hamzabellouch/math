import OAI.Computability.WitnessedChoice.AnchoredTree

namespace OAI

section

namespace WitnessedChoice.BGS.QuotedTerm

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A B : Type} [Fintype A] [Fintype B] {k : ℕ}

lemma mem_tupleProduct_image (m : ℕ) (r : QuotedTerm k) (S : Input A) (env : Fin k → HF A)
    (code : B → HF A) (hr : r.meaning S env = ofFinset (Finset.univ.image code)) (z : HF A) :
    z ∈ elements ((tupleProduct m r).meaning S env) ↔
      ∃ f : Fin m → B, tupleCode (List.ofFn (code ∘ f)) = z := by
  rw [mem_tupleProduct]
  simp only [hr,elements_ofFinset,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨g,hg,hz⟩
    choose f hf using hg
    exact ⟨f,by simpa only [show code ∘ f = g from funext hf] using hz⟩
  · rintro ⟨f,hf⟩
    exact ⟨code ∘ f,fun i => ⟨f i,rfl⟩,hf⟩

end

end WitnessedChoice.BGS.QuotedTerm

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma endpoints_incident_iff (e : Edge n) (u v : Vertex n) :
    ((u = tail e ∧ v = head e) ∨ (v = tail e ∧ u = head e)) ↔
      u ≠ v ∧ incident u e ∧ incident v e := by
  constructor
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨(head_ne_tail e).symm,Or.inr rfl,Or.inl rfl⟩
    · exact ⟨head_ne_tail e,Or.inl rfl,Or.inr rfl⟩
  · rintro ⟨hne,(hu|hu),(hv|hv)⟩
    · exact (hne (hu.symm.trans hv)).elim
    · exact Or.inr ⟨hv.symm,hu.symm⟩
    · exact Or.inl ⟨hu.symm,hv.symm⟩
    · exact (hne (hu.symm.trans hv)).elim

def frameCode (b : Vertex n → Scalar) (C : CycleFrame n) : HF (Atom b) :=
  Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ C.vertex)))
    (tupleCode (List.ofFn (edgeCode b ∘ C.edge)))

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

@[simp] lemma next4_eq_add (i : Fin 4) : next4 i = i+1 := rfl

@[simp] lemma prev4_eq_add (i : Fin 4) : prev4 i = i+3 := rfl

lemma adjacent_index_iff (i j : Fin 4) : (j=next4 i ∨ j=prev4 i) ↔ AdjacentIndex i j := by
  rw [next4_eq_add,prev4_eq_add]
  revert i j
  unfold AdjacentIndex
  decide

lemma meaning_fv_pair (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (i : Fin 4) :
    (fv ft i).meaning (atomInput b) env = vertexCode b (v i) := by
  exact meaning_component_ofFn _ _ _ _ (meaning_fst_of_eq _ _ _ _ _ hf) i

lemma meaning_fe_pair (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (i : Fin 4) :
    (fe ft i).meaning (atomInput b) env = edgeCode b (e i) := by
  exact meaning_component_ofFn _ _ _ _ (meaning_snd_of_eq _ _ _ _ _ hf) i

lemma meaning_faceDescription (env : Fin k → HF (Atom b)) (ft : QuotedTerm k)
    (v : Fin 4 → Vertex n) (e : Fin 4 → Edge n)
    (hf : ft.meaning (atomInput b) env = Hereditary.pair (tupleCode (List.ofFn (vertexCode b ∘ v)))
      (tupleCode (List.ofFn (edgeCode b ∘ e)))) (hn : 1 ≤ n) :
    (faceDescription ft).meaning (atomInput b) env ↔
      Function.Injective v ∧ Function.Injective e ∧
      ∀ i, (v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
        (v (i+1) = tail (e i) ∧ v i = head (e i)) := by
  have hv := meaning_fv_pair env ft v e hf
  have he := meaning_fe_pair env ft v e hf
  have ha (i : Fin 4) : (hasEndpoints (fe ft i) (fv ft i) (fv ft (next4 i))).meaning (atomInput b) env ↔
      ((v i = tail (e i) ∧ v (i+1) = head (e i)) ∨
        (v (i+1) = tail (e i) ∧ v i = head (e i))) := by
    simp only [next4_eq_add,hasEndpoints,meaning_and,meaning_neg,meaning_eq,hv,(vertexCode_injective hn).eq_iff,
      meaning_incident env _ _ _ _ (hv i) (he i) hn,
      meaning_incident env _ _ _ _ (hv (i+1)) (he i) hn]
    exact (endpoints_incident_iff (e i) (v i) (v (i+1))).symm
  have hne (i j : Fin 4) : (if i=j then truth else
      (eq (fv ft i) (fv ft j)).neg.and (eq (fe ft i) (fe ft j)).neg).meaning (atomInput b) env ↔
      (i ≠ j → v i ≠ v j ∧ e i ≠ e j) := by
    split_ifs with hij
    · simp [truth,hij]
    · simp only [meaning_and,meaning_neg,meaning_eq,hv,he,(vertexCode_injective hn).eq_iff,
        edgeCode_injective.eq_iff,Ne,hij,not_false_eq_true,true_implies]
  simp only [faceDescription,meaning_allFin,meaning_and,hne,ha]
  constructor
  · intro hh
    refine ⟨?_,?_,fun i => (hh i).2⟩
    · intro i j hij
      by_contra hn
      exact ((hh i).1 j hn).1 hij
    · intro i j hij
      by_contra hn
      exact ((hh i).1 j hn).2 hij
  · rintro ⟨hv,he,hh⟩ i
    exact ⟨fun j hij => ⟨fun h => hij (hv h),fun h => hij (he h)⟩,hh i⟩

lemma mem_faces (env : Fin k → HF (Atom b)) (VT Et : QuotedTerm k)
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements ((faces VT Et).meaning (atomInput b) env) ↔
      ∃ C : CycleFrame n, frameCode b C = z := by
  have hTV (t : HF (Atom b)) := mem_tupleProduct_image 4 VT (atomInput b) env (vertexCode b) hV t
  have hTE (t u : HF (Atom b)) := mem_tupleProduct_image 4 Et.up (atomInput b) (Fin.cons t env)
    (edgeCode b) (by exact hE) u
  simp only [faces,QuotedTerm.meaning_filter,meaning_bind,meaning_map,meaning_pair,meaning_var,
    Fin.cons_zero,Fin.cons_one,elements_ofFinset,Finset.mem_filter,Finset.mem_biUnion,
    Finset.mem_image,hTV,hTE,exists_exists_eq_and]
  constructor
  · rintro ⟨⟨v,e,rfl⟩,hd⟩
    have hh := (meaning_faceDescription (Fin.cons _ env) (var 0) v e rfl hn).mp hd
    exact ⟨⟨v,e,hh.1,hh.2.1,hh.2.2⟩,rfl⟩
  · rintro ⟨C,rfl⟩
    refine ⟨⟨C.vertex,C.edge,rfl⟩,?_⟩
    exact (meaning_faceDescription (Fin.cons _ env) (var 0) C.vertex C.edge rfl hn).mpr
      ⟨C.vertex_injective,C.edge_injective,C.endpoints⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_hasEndpoints (env : Fin k → HF (Atom b)) (et ut vt : QuotedTerm k)
    (e : Edge n) (u v : Vertex n)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (hasEndpoints et ut vt).meaning (atomInput b) env ↔
      ((u=tail e ∧ v=head e) ∨ (v=tail e ∧ u=head e)) := by
  simp only [hasEndpoints,meaning_and,meaning_neg,meaning_eq,hu,hv,
    (vertexCode_injective hn).eq_iff,meaning_incident env ut et u e hu he hn,
    meaning_incident env vt et v e hv he hn]
  exact (endpoints_incident_iff e u v).symm

lemma meaning_tree (env : Fin k → HF (Atom b)) (ats VT Et R : QuotedTerm k)
    (α : Fin 4 → Vertex n) (hres : AnchoredTree.Resolving (boxGraph n) α)
    (hα : ats.meaning (atomInput b) env = tupleCode (List.ofFn (vertexCode b ∘ α)))
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : Et.meaning (atomInput b) env = ofFinset (Finset.univ.image (edgeCode b)))
    (hR : R.meaning (atomInput b) env = ofFinset
      ((BFS.closure (boxGraph n) (Fintype.card (Atom b))).image (distanceCode (vertexCode b))))
    (hn : 1 ≤ n) :
    (tree ats VT Et R).meaning (atomInput b) env =
      ofFinset ((anchoredParents α).treeEdges.image (edgeCode b)) := by
  have hr := QuotedTerm.meaning_root (atomInput b) env ats VT R (vertexCode b)
    (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) α hα hV hR (vertex_card_le_atoms hn)
  have hpred (e : Edge n) :
      (existsIn VT.up (existsIn VT.up.up
        ((QuotedFormula.parent ats.up.up.up VT.up.up.up Et.up.up.up R.up.up.up
          (root ats VT R).up.up.up (var 1) (var 0)).and
            (hasEndpoints (var 2) (var 1) (var 0))))).meaning (atomInput b)
              (Fin.cons (edgeCode b e) env) ↔ e ∈ (anchoredParents α).treeEdges := by
    have hp (v w : Vertex n) := meaning_parent
      (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (edgeCode b e) env)))
      ats.up.up.up VT.up.up.up Et.up.up.up R.up.up.up (root ats VT R).up.up.up (var 1) (var 0)
      α v w hres hα hV hE hR hr rfl rfl hn
    have hep (v w : Vertex n) := meaning_hasEndpoints
      (Fin.cons (vertexCode b w) (Fin.cons (vertexCode b v) (Fin.cons (edgeCode b e) env)))
      (var 2) (var 1) (var 0) e v w rfl rfl rfl hn
    simp only [meaning_existsIn,QuotedTerm.meaning_up,hV,elements_ofFinset,Finset.mem_image,
      Finset.mem_univ,true_and,exists_exists_eq_and,meaning_and,hp,hep]
    constructor
    · rintro ⟨v,w,⟨hv,rfl⟩,he⟩
      have hpe := (anchoredParents α).endpoints v hv
      have heq : e = (anchoredParents α).edge v hv := by
        apply edge_eq_of_endpoints
        rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> rcases hpe with ⟨hp,hp'⟩ | ⟨hp',hp⟩
        · exact Or.inr ⟨ht.symm.trans hp.symm,hh.symm.trans hp'.symm⟩
        · exact Or.inl ⟨ht.symm.trans hp'.symm,hh.symm.trans hp.symm⟩
        · exact Or.inl ⟨ht.symm.trans hp'.symm,hh.symm.trans hp.symm⟩
        · exact Or.inr ⟨ht.symm.trans hp.symm,hh.symm.trans hp'.symm⟩
      rw [heq]
      exact (anchoredParents α).edge_mem v hv
    · intro he
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
      refine ⟨v.val,(anchoredTree α).parent v.val,⟨v.property,rfl⟩,?_⟩
      rcases (anchoredParents α).endpoints v.val v.property with ⟨hh,ht⟩ | ⟨ht,hh⟩
      · exact Or.inr ⟨ht.symm,hh.symm⟩
      · exact Or.inl ⟨ht.symm,hh.symm⟩
  simp only [tree,QuotedTerm.meaning_filter,hE,elements_ofFinset]
  congr 1
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨e,rfl⟩,h⟩
    exact ⟨e,(hpred e).mp h,rfl⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨⟨e,rfl⟩,(hpred e).mpr he⟩

end QuotedGrid

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {k : ℕ} {A V : Type} [Fintype A] [Fintype V]

lemma meaning_tripleDomain (S : Input A) (env : Fin k → HF A) (VT : QuotedTerm k)
    (code : V → HF A) (hV : VT.meaning S env = ofFinset (Finset.univ.image code)) :
    (tripleDomain VT).meaning S env =
      ofFinset (Finset.univ.image (distanceCode code)) := by
  simp only [tripleDomain,meaning_bind,meaning_up,hV,elements_ofFinset,meaning_map,
    meaning_indices,meaning_triple,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨_,⟨v,rfl⟩,_,⟨w,rfl⟩,i,hi,rfl⟩
    obtain ⟨k,hk,rfl⟩ := (mem_ordinal i (Fintype.card A+1)).mp hi
    exact ⟨(v,w,⟨k,hk⟩),rfl⟩
  · rintro ⟨⟨v,w,i⟩,rfl⟩
    exact ⟨code v,⟨v,rfl⟩,code w,⟨w,rfl⟩,ordinal i.val,
      (ordinal_mem_elements _ _).mpr i.isLt,rfl⟩

end QuotedTerm

namespace SourceProgram

def cost : Polynomial ℕ :=
  Polynomial.X^2*(Polynomial.X+1) +
  (QuotedTerm.tripleDomain (QuotedTerm.vertexBlocks : QuotedTerm 0)).code.traceBound.comp
    (Polynomial.X+1) + Polynomial.X+2

def polynomial : Polynomial ℝ := cost.map (Nat.castRingHom ℝ)

lemma resource_polynomial (m : ℕ) : resource polynomial m = cost.eval m := by
  unfold resource polynomial
  rw [Polynomial.eval_map]
  have h : Polynomial.eval₂ (Nat.castRingHom ℝ) (m : ℝ) cost = ((cost.eval m : ℕ) : ℝ) := by
    exact Polynomial.eval₂_at_apply (Nat.castRingHom ℝ) m
  rw [h,Nat.floor_natCast]

lemma resource_basic (m : ℕ) : m+2 ≤ resource polynomial m := by
  rw [resource_polynomial]
  simp only [cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  omega

end SourceProgram

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

structure GridResources (p : Polynomial ℝ) (b : Vertex n → Scalar) : Prop where
  basic : Fintype.card (Atom b)+2 ≤ resource p (Fintype.card (Atom b))
  time : Fintype.card (BFS.Item (Vertex n) (Fintype.card (Atom b))) ≤ resource p (Fintype.card (Atom b))
  space : (TC (ofFinset (Finset.univ.image (distanceCode (vertexCode b))))).card ≤
    resource p (Fintype.card (Atom b))

lemma gridResources (hn : 1 ≤ n) : GridResources SourceProgram.polynomial b := by
  refine ⟨SourceProgram.resource_basic _,?_,?_⟩
  · rw [SourceProgram.resource_polynomial]
    simp only [SourceProgram.cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    have h := vertex_card_le_atoms (b := b) hn
    have hc : Fintype.card (BFS.Item (Vertex n) (Fintype.card (Atom b))) ≤
        Fintype.card (Atom b)^2*(Fintype.card (Atom b)+1) := by
      have h₂ := Nat.mul_le_mul_right (Fintype.card (Atom b)+1) (Nat.mul_self_le_mul_self h)
      simpa only [BFS.Item,Fintype.card_prod,Fintype.card_fin,pow_two,Nat.mul_assoc] using h₂
    omega
  · have h := QuotedTerm.TC_bound
      (QuotedTerm.tripleDomain (QuotedTerm.vertexBlocks : QuotedTerm 0))
      (atomInput b) Fin.elim0 (Fintype.card (Atom b)+1) (by simp [tracePotential])
    rw [QuotedTerm.meaning_tripleDomain _ _ _ (vertexCode b) (quoted_vertexBlocks hn _)] at h
    apply h.trans
    rw [SourceProgram.resource_polynomial]
    simp only [SourceProgram.cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_comp]
    omega

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma mem_edgeCode_iff (e : Edge n) (z : HF (Atom b)) :
    z ∈ elements (edgeCode b e) ↔ ∃ s : LocalGroup e, z = atom (.inl ⟨e,s⟩) := by
  simp only [edgeCode,stateCode,elements_ofFinset,Finset.mem_image,mem_edgeBlockSet]
  constructor
  · rintro ⟨a,⟨s,rfl⟩,rfl⟩
    exact ⟨s,rfl⟩
  · rintro ⟨s,rfl⟩
    exact ⟨_,⟨s,rfl⟩,rfl⟩

lemma mem_vertexCode_iff (v : Vertex n) (z : HF (Atom b)) :
    z ∈ elements (vertexCode b v) ↔ ∃ s : Configuration b v, z = atom (.inr ⟨v,s⟩) := by
  simp only [vertexCode,stateCode,elements_ofFinset,Finset.mem_image,mem_vertexBlockSet]
  constructor
  · rintro ⟨a,⟨s,rfl⟩,rfl⟩
    exact ⟨s,rfl⟩
  · rintro ⟨s,rfl⟩
    exact ⟨_,⟨s,rfl⟩,rfl⟩

lemma exists_edgeCode (e : Edge n) (P : HF (Atom b) → Prop) :
    (∃ z ∈ elements (edgeCode b e), P z) ↔ ∃ s : LocalGroup e, P (atom (.inl ⟨e,s⟩)) := by
  simp only [mem_edgeCode_iff]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,h⟩
    exact ⟨s,h⟩
  · rintro ⟨s,h⟩
    exact ⟨_,⟨s,rfl⟩,h⟩

lemma exists_vertexCode (v : Vertex n) (P : HF (Atom b) → Prop) :
    (∃ z ∈ elements (vertexCode b v), P z) ↔ ∃ s : Configuration b v, P (atom (.inr ⟨v,s⟩)) := by
  simp only [mem_vertexCode_iff]
  constructor
  · rintro ⟨_,⟨s,rfl⟩,h⟩
    exact ⟨s,h⟩
  · rintro ⟨s,h⟩
    exact ⟨_,⟨s,rfl⟩,h⟩

@[simp] lemma atom_mem_edgeCode (e d : Edge n) (s : LocalGroup e) :
    atom (.inl ⟨e,s⟩) ∈ elements (edgeCode b d) ↔ e=d := by
  rw [mem_edgeCode_iff]
  constructor
  · rintro ⟨t,ht⟩
    exact congrArg Sigma.fst (Sum.inl.inj (atom_injective ht))
  · rintro rfl
    exact ⟨s,rfl⟩

lemma input_inc_iff (v : Vertex n) (c : Configuration b v) (e : Edge n) (s : LocalGroup e) :
    inputHF (atomInput b) .I (atom (.inr ⟨v,c⟩)) (atom (.inl ⟨e,s⟩)) = true ↔
      ∃ h : incident v e, c.state ⟨e,h⟩ = s := by
  rw [inputHF_atoms]
  change decide (AtomRelation b .I (.inr ⟨v,c⟩) (.inl ⟨e,s⟩)) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    cases h with | inc v c e => exact ⟨e.property,rfl⟩
  · rintro ⟨h,rfl⟩
    exact .inc v c ⟨e,h⟩

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_adjacentMatch (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j))
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨C.edge i,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨C.edge j,t⟩)) :
    (adjacentMatch ft st tt i j).meaning (atomInput b) env ↔ C.Across (b := b) i j s t := by
  have hv := meaning_fv_pair env ft C.vertex C.edge hf
  have he := meaning_fe_pair env ft C.vertex C.edge hf
  have hj : C.vertex (if j=next4 i then j else i) = C.joint i j := by
    by_cases h : j=i+1 <;> simp [next4_eq_add,CycleFrame.joint,h]
  simp only [adjacentMatch,meaning_allList,List.mem_cons,List.mem_nil_iff,forall_eq_or_imp,
    forall_false,implies_true,and_true,meaning_mem,hs,ht,he,atom_mem_edgeCode,meaning_existsIn,hv,hj,
    exists_vertexCode,meaning_and,meaning_input,meaning_var,
    Fin.cons_zero,QuotedTerm.meaning_up,input_inc_iff,true_and]
  constructor
  · rintro ⟨c,⟨hi,hs⟩,⟨hj,ht⟩⟩
    exact ⟨hi,hj,c,hs,ht⟩
  · rintro ⟨hi,hj,c,hs,ht⟩
    exact ⟨c,⟨hi,hs⟩,⟨hj,ht⟩⟩

lemma meaning_matchFace (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (i j : Fin 4) (s : LocalGroup (C.edge i)) (t : LocalGroup (C.edge j))
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨C.edge i,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨C.edge j,t⟩)) :
    (matchFace ft st tt).meaning (atomInput b) env ↔ C.Match (b := b) i j s t := by
  have he := meaning_fe_pair env ft C.vertex C.edge hf
  simp only [matchFace,meaning_anyFin,meaning_and,meaning_mem,hs,ht,he,
    atom_mem_edgeCode,C.edge_injective.eq_iff,exists_and_left,exists_eq_left']
  simp only [adjacent_index_iff]
  unfold CycleFrame.Match
  split_ifs with h
  · exact meaning_adjacentMatch env ft st tt C i j s t hf hs ht
  · simp only [meaning_existsIn,he,next4_eq_add,exists_edgeCode,
      meaning_and]
    apply exists_congr
    intro q
    exact and_congr (meaning_adjacentMatch (Fin.cons _ env) ft.up st.up (var 0) C i (i+1) s q hf hs rfl)
      (meaning_adjacentMatch (Fin.cons _ env) ft.up tt.up (var 0) C j (i+1) t q hf ht rfl)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

lemma edgeGraph_erase (T : Finset (Edge n)) (h : Edge n) :
    edgeGraph (T.erase h) = (edgeGraph T).deleteEdges {symEdge h} := by
  apply SimpleGraph.edgeSet_injective
  rw [SimpleGraph.edgeSet_deleteEdges]
  apply Set.ext
  intro q
  rw [← SimpleGraph.mem_edgeFinset,edgeGraph_edgeFinset]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  rw [← SimpleGraph.mem_edgeFinset,edgeGraph_edgeFinset]
  simp only [Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨e,⟨he,heT⟩,rfl⟩
    exact ⟨⟨e,heT,rfl⟩,fun hh => he (symEdge_injective hh)⟩
  · rintro ⟨⟨e,heT,rfl⟩,he⟩
    exact ⟨e,⟨fun hh => he (congrArg symEdge hh),heT⟩,rfl⟩

lemma cut_cover (T : Finset (Edge n)) (hT : (edgeGraph T).Connected) (h : Edge n) (v : Vertex n) :
    (edgeGraph (T.erase h)).Reachable (head h) v ∨
      (edgeGraph (T.erase h)).Reachable (tail h) v := by
  have transport {u v : Vertex n} (p : (edgeGraph T).Walk u v) :
      ((edgeGraph (T.erase h)).Reachable (head h) u ∨
       (edgeGraph (T.erase h)).Reachable (tail h) u) →
      ((edgeGraph (T.erase h)).Reachable (head h) v ∨
       (edgeGraph (T.erase h)).Reachable (tail h) v) := by
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      obtain ⟨e,he,hh⟩ := hadj
      by_cases heh : e = h
      · subst e
        rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl .rfl
        · exact Or.inr .rfl
      · have hw : (edgeGraph (T.erase h)).Adj u w := ⟨e,Finset.mem_erase.mpr ⟨heh,he⟩,hh⟩
        exact hu.imp (fun x => x.trans hw.reachable) (fun x => x.trans hw.reachable)
  exact transport (hT (head h) v).some (Or.inl .rfl)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

def cut (h : Edge n) : SimpleGraph (Vertex n) := edgeGraph (P.treeEdges.erase h)

lemma cut_separated (h : Edge n) (hh : h ∈ P.treeEdges) :
    ¬(P.cut h).Reachable (tail h) (head h) := by
  have ha : (edgeGraph P.treeEdges).Adj (tail h) (head h) := ⟨h,hh,Or.inl ⟨rfl,rfl⟩⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp P.graph_isTree.isAcyclic) ha
  simpa only [SimpleGraph.isBridge_iff,cut,edgeGraph_erase,symEdge] using hb

lemma cut_reachable_iff (h : Edge n) (_hh : h ∈ P.treeEdges) (u v : Vertex n) :
    (P.cut h).Reachable u v ↔
      ((P.cut h).Reachable (head h) u ↔ (P.cut h).Reachable (head h) v) := by
  constructor
  · intro huv
    exact ⟨fun hu => hu.trans huv,fun hv => hv.trans huv.symm⟩
  · intro huv
    rcases cut_cover P.treeEdges P.graph_connected h u with hu | hu
    · exact hu.symm.trans (huv.mp hu)
    · rcases cut_cover P.treeEdges P.graph_connected h v with hv | hv
      · exact (huv.mpr hv).symm.trans hv
      · exact hu.symm.trans hv

def cutIndicator (h : Edge n) (v : Vertex n) : Scalar :=
  if (P.cut h).Reachable (head h) v then 1 else 0

lemma cutIndicator_head (h : Edge n) : P.cutIndicator h (head h) = 1 := by
  simp [cutIndicator,SimpleGraph.Reachable.rfl]

lemma cutIndicator_tail (h : Edge n) (hh : h ∈ P.treeEdges) : P.cutIndicator h (tail h) = 0 := by
  rw [cutIndicator,ite_eq_right (fun hth => P.cut_separated h hh hth.symm)]

lemma cutIndicator_eq (h : Edge n) {u v : Vertex n} (huv : (P.cut h).Reachable u v) :
    P.cutIndicator h u = P.cutIndicator h v := by
  have he : (P.cut h).Reachable (head h) u ↔ (P.cut h).Reachable (head h) v :=
    ⟨fun hu => hu.trans huv, fun hv => hv.trans huv.symm⟩
  simp only [cutIndicator,he]

lemma cut_gradient_self (h : Edge n) (hh : h ∈ P.treeEdges) :
    gradient (P.cutIndicator h) h = 1 := by
  rw [gradient,P.cutIndicator_head,P.cutIndicator_tail h hh,sub_zero]

lemma cut_gradient_other (h f : Edge n) (hf : f ∈ P.treeEdges) (hne : f ≠ h) :
    gradient (P.cutIndicator h) f = 0 := by
  have ha : (P.cut h).Adj (tail f) (head f) := ⟨f,Finset.mem_erase.mpr ⟨hne,hf⟩,Or.inl ⟨rfl,rfl⟩⟩
  rw [gradient,P.cutIndicator_eq h ha.reachable,sub_self]

lemma flow_cut (e : Edge n) (he : e ∉ P.treeEdges) (a : Scalar)
    (h : Edge n) (hh : h ∈ P.treeEdges) :
    (P.flow e a).val h =
      (P.cutIndicator h (tail e) - P.cutIndicator h (head e)) * a := by
  have hhe : h ≠ e := by intro hhe; subst h; exact he hh
  have hp := pairing_gradient_flow (P.cutIndicator h) (P.flow e a)
  change (∑ f, gradient (P.cutIndicator h) f * (P.flow e a).val f) = 0 at hp
  have hs : (∑ f, gradient (P.cutIndicator h) f * (P.flow e a).val f) =
      gradient (P.cutIndicator h) h * (P.flow e a).val h +
      gradient (P.cutIndicator h) e * (P.flow e a).val e := by
    apply Fintype.sum_eq_add _ _ hhe
    rintro f ⟨hfh,hfe⟩
    by_cases hf : f ∈ P.treeEdges
    · rw [P.cut_gradient_other h f hf hfh,zero_mul]
    · rw [P.flow_other e f hf hfe a,mul_zero]
  rw [hs,P.cut_gradient_self h hh,one_mul,P.flow_self e he a,gradient] at hp
  linear_combination hp

end ParentEdges

end

end WitnessedSeparation.Grid


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {k : ℕ} {A V : Type} [Fintype A] [Fintype V]

lemma meaning_connected (S : Input A) (env : Fin k → HF A)
    (RT ut vt : QuotedTerm k) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (u v : V)
    (hR : RT.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (connected RT ut vt).meaning S env ↔ G.Reachable u v := by
  simp only [connected,meaning_mem,meaning_triple,hu,hv,meaning_card,meaning_atoms,hR]
  rw [show cardHF (stateCode (Finset.univ : Finset A)) = ordinal (Fintype.card A) by
    simp [cardHF,stateCode,Finset.card_image_of_injective _ atom_injective]]
  change HFTriple (code u) (code v) (ordinal (Fintype.card A)) ∈
    elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔ _
  rw [coded_closure_mem code hc G u v _ le_rfl]
  constructor
  · rintro ⟨w,_⟩
    exact ⟨w⟩
  · intro h
    obtain ⟨w,hw⟩ := h.exists_isPath
    exact ⟨w,(Nat.le_of_lt hw.length_lt).trans hcard⟩

end QuotedFormula

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

def distancesCode (b : Vertex n → Scalar) (G : SimpleGraph (Vertex n)) : HF (Atom b) :=
  ofFinset ((BFS.closure G (Fintype.card (Atom b))).image (distanceCode (vertexCode b)))

def connTableCode (b : Vertex n → Scalar) (T : Finset (Edge n)) : HF (Atom b) :=
  ofFinset (T.image (fun h => Hereditary.pair (edgeCode b h) (distancesCode b (edgeGraph (T.erase h)))))

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_connWithout (env : Fin k → HF (Atom b)) (HT ht ut vt : QuotedTerm k)
    (T : Finset (Edge n)) (h : Edge n) (u v : Vertex n)
    (hH : HT.meaning (atomInput b) env = connTableCode b T)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (connWithout HT ht ut vt).meaning (atomInput b) env ↔
      h ∈ T ∧ (edgeGraph (T.erase h)).Reachable u v := by
  have hm (e : Edge n) := QuotedFormula.meaning_connected (atomInput b)
    (Fin.cons (Hereditary.pair (edgeCode b e) (distancesCode b (edgeGraph (T.erase e)))) env)
    (var 0).snd ut.up vt.up (vertexCode b) (vertexCode_injective hn) (edgeGraph (T.erase e)) u v
    (meaning_snd_of_eq _ _ _ _ _ rfl) hu hv (vertex_card_le_atoms hn)
  simp only [connWithout,meaning_existsIn,hH,connTableCode,elements_ofFinset,Finset.mem_image,
    exists_exists_and_eq_and,meaning_and,meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,
    firstHF_pair (atomInput b),QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff,hm]
  constructor
  · rintro ⟨a,ha,rfl,hr⟩
    exact ⟨ha,hr⟩
  · rintro ⟨hh,hr⟩
    exact ⟨h,hh,rfl,hr⟩

end QuotedGrid

end

end WitnessedSeparation.Grid

end


namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax SourceProgram

variable {k : ℕ}

lemma value_distance_edges (env : Fin k → HF (Atom b)) (V E : QuotedTerm k)
    (D : Finset (Edge n)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hE : E.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) (hn : 1 ≤ n) :
    (CPTTerm.distance (.quoted V) (.quoted E)).value (atomInput b) p env = distancesCode b (edgeGraph D) := by
  apply CPTTerm.distance_value (.quoted V) (.quoted E) (atomInput b) p env
    (vertexCode b) (vertexCode_injective hn) (edgeGraph D) (by simpa only [CPTTerm.value_quoted] using hV) _ hp.time hp.space
  intro u v
  simpa only [CPTTerm.value_quoted,hE] using blockAdjacent_edges (b := b) hn D u v

lemma value_distances (env : Fin k → HF (Atom b)) (p : Polynomial ℝ)
    (hp : GridResources p b) (hn : 1 ≤ n) :
    (SourceProgram.distances : CPTTerm k).value (atomInput b) p env = distancesCode b (boxGraph n) := by
  unfold SourceProgram.distances
  rw [value_distance_edges env _ _ Finset.univ p hp (quoted_vertexBlocks hn env) (quoted_edgeBlocks env) hn,
    edgeGraph_univ]

lemma value_connTable (env : Fin k → HF (Atom b)) (V T : QuotedTerm k)
    (D : Finset (Edge n)) (p : Polynomial ℝ) (hp : GridResources p b)
    (hV : V.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : T.meaning (atomInput b) env = ofFinset (D.image (edgeCode b))) (hn : 1 ≤ n) :
    (SourceProgram.connTable V T).value (atomInput b) p env = connTableCode b D := by
  have hd (e : Edge n) :
      (T.up.diff (var 0).singleton).meaning (atomInput b) (Fin.cons (edgeCode b e) env) =
        ofFinset ((D.erase e).image (edgeCode b)) := by
    simp only [meaning_diff,QuotedTerm.meaning_up,hT,meaning_singleton,meaning_var,
      Fin.cons_zero,elements_ofFinset,Hereditary.singleton]
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hne⟩
      exact ⟨f,⟨fun h => hne (by rw [h]),hf⟩,rfl⟩
    · rintro ⟨f,⟨hne,hf⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,fun h => hne (edgeCode_injective h)⟩
  simp only [SourceProgram.connTable,CPTTerm.value_map,CPTTerm.value_quoted,hT,elements_ofFinset,
    connTableCode,Finset.image_image]
  apply congrArg ofFinset
  apply Finset.image_congr
  intro e he
  simp only [Function.comp_apply]
  rw [CPTTerm.value_letIn,value_distance_edges (Fin.cons (edgeCode b e) env) V.up (T.up.diff (var 0).singleton)
    (D.erase e) p hp hV (hd e) hn]
  simp only [CPTTerm.value_quoted,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one]

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

def Traverses (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (h : Edge n) (a c : Vertex n) : Prop :=
  (h=e ∧ a=u ∧ c=v) ∨ h ∈ T ∧
    ((a=tail h ∧ c=head h) ∨ (c=tail h ∧ a=head h)) ∧
    ¬(edgeGraph (T.erase h)).Reachable v u ∧
    (edgeGraph (T.erase h)).Reachable v a ∧
    (edgeGraph (T.erase h)).Reachable u c

def traversalCode (b : Vertex n → Scalar) (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) : HF (Atom b) :=
  ofFinset ((Finset.univ.filter fun hac : Edge n × Vertex n × Vertex n =>
    Traverses T e u v hac.1 hac.2.1 hac.2.2).image fun hac =>
      HFTriple (edgeCode b hac.1) (vertexCode b hac.2.1) (vertexCode b hac.2.2))

lemma mem_traversalCode (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (z : HF (Atom b)) :
    z ∈ elements (traversalCode b T e u v) ↔ ∃ h a c,
      Traverses T e u v h a c ∧ HFTriple (edgeCode b h) (vertexCode b a) (vertexCode b c) = z := by
  simp only [traversalCode,elements_ofFinset,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and,Prod.exists]

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_traversal (env : Fin k → HF (Atom b)) (VT TT HT et ut vt : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (hV : VT.meaning (atomInput b) env = ofFinset (Finset.univ.image (vertexCode b)))
    (hT : TT.meaning (atomInput b) env = ofFinset (T.image (edgeCode b)))
    (hH : HT.meaning (atomInput b) env = connTableCode b T)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hu : ut.meaning (atomInput b) env = vertexCode b u)
    (hv : vt.meaning (atomInput b) env = vertexCode b v) (hn : 1 ≤ n) :
    (traversal VT TT HT et ut vt).meaning (atomInput b) env = traversalCode b T e u v := by
  have hend (h : Edge n) (a c : Vertex n) := meaning_hasEndpoints
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    (var 2) (var 1) (var 0) h a c rfl rfl rfl hn
  have h0 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) vt.up.up.up ut.up.up.up T h v u hH rfl hv hu hn
  have h1 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) vt.up.up.up (var 1) T h v a hH rfl hv rfl hn
  have h2 (h : Edge n) (a c : Vertex n) := meaning_connWithout
    (Fin.cons (vertexCode b c) (Fin.cons (vertexCode b a) (Fin.cons (edgeCode b h) env)))
    HT.up.up.up (var 2) ut.up.up.up (var 0) T h u c hH rfl hu rfl hn
  rw [traversal,meaning_cup]
  apply ofFinset_inj.mpr
  ext z
  simp only [meaning_singleton,Hereditary.singleton,meaning_triple,he,hu,hv,
    elements_ofFinset,Finset.mem_union,Finset.mem_singleton,meaning_bind,
    QuotedTerm.meaning_up,hT,hV,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    meaning_map,QuotedTerm.meaning_filter,Finset.mem_filter,
    meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two]
  constructor
  · rintro (hz | ⟨_,⟨h,hh,rfl⟩,_,⟨a,rfl⟩,_,⟨⟨c,rfl⟩,hq⟩,hz⟩)
    · exact ⟨(e,u,v),Or.inl ⟨rfl,rfl,rfl⟩,hz.symm⟩
    · simp only [meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
        forall_false,implies_true,and_true,meaning_neg,hend,h0,h1,h2] at hq
      exact ⟨(h,a,c),Or.inr ⟨hh,hq.1,fun hr => hq.2.1 ⟨hh,hr⟩,hq.2.2.1.2,hq.2.2.2.2⟩,hz⟩
  · rintro ⟨⟨h,a,c⟩,htr,hz⟩
    rcases htr with ⟨rfl,rfl,rfl⟩ | ⟨hh,hends,hvu,hva,huc⟩
    · exact Or.inl hz.symm
    · refine Or.inr ⟨edgeCode b h,⟨h,hh,rfl⟩,vertexCode b a,⟨a,rfl⟩,
        vertexCode b c,⟨⟨c,rfl⟩,?_⟩,hz⟩
      simpa only [meaning_allList,List.mem_cons,List.not_mem_nil,forall_eq_or_imp,
        forall_false,implies_true,and_true,meaning_neg,hend,h0,h1,h2] using
        (show ((a=tail h ∧ c=head h) ∨ (c=tail h ∧ a=head h)) ∧
          ¬(h ∈ T ∧ (edgeGraph (T.erase h)).Reachable v u) ∧
          (h ∈ T ∧ (edgeGraph (T.erase h)).Reachable v a) ∧
          (h ∈ T ∧ (edgeGraph (T.erase h)).Reachable u c) from
            ⟨hends,fun hr => hvu hr.2,⟨hh,hva⟩,⟨hh,huc⟩⟩)

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open QuotedTerm QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_side (env : Fin k → HF (Atom b)) (ft et : QuotedTerm k)
    (C : CycleFrame n) (e : Edge n)
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (he : et.meaning (atomInput b) env = edgeCode b e) :
    (side ft et).meaning (atomInput b) env ↔ cycle C.face e ≠ 0 := by
  simp only [side,meaning_anyFin,meaning_eq,he,meaning_fe_pair env ft C.vertex C.edge hf,
    edgeCode_injective.eq_iff]
  exact (C.support_iff e).symm

lemma meaning_onSide (env : Fin k → HF (Atom b)) (ft st : QuotedTerm k)
    (C : CycleFrame n) (e : Edge n) (s : LocalGroup e)
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩)) :
    (onSide ft st).meaning (atomInput b) env ↔ cycle C.face e ≠ 0 := by
  simp only [onSide,meaning_anyFin,meaning_mem,hs,meaning_fe_pair env ft C.vertex C.edge hf,
    atom_mem_edgeCode]
  exact (C.support_iff e).symm

lemma meaning_matchFace_atoms (env : Fin k → HF (Atom b)) (ft st tt : QuotedTerm k)
    (C : CycleFrame n) (e d : Edge n) (s : LocalGroup e) (t : LocalGroup d)
    (hf : ft.meaning (atomInput b) env = frameCode b C)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨d,t⟩))
    (he : cycle C.face e ≠ 0) (hd : cycle C.face d ≠ 0) (hn : 1 ≤ n) :
    (matchFace ft st tt).meaning (atomInput b) env ↔ s.face ⟨C.face,he⟩ = t.face ⟨C.face,hd⟩ := by
  obtain ⟨i,rfl⟩ := (C.support_iff e).mp he
  obtain ⟨j,rfl⟩ := (C.support_iff d).mp hd
  exact (meaning_matchFace env ft st tt C i j s t hf hs ht).trans (C.match_iff hn i j s t)

lemma meaning_baseEq (env : Fin k → HF (Atom b)) (F et st tt : QuotedTerm k)
    (e : Edge n) (s t : LocalGroup e)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩))
    (ht : tt.meaning (atomInput b) env = atom (.inl ⟨e,t⟩)) (hn : 1 ≤ n) :
    (baseEq F et st tt).meaning (atomInput b) env ↔ s.face = t.face := by
  have hside (C : CycleFrame n) := meaning_side (Fin.cons (frameCode b C) env) (var 0) et.up C e rfl he
  simp only [baseEq,meaning_allIn,hF,forall_exists_index,forall_apply_eq_imp_iff,meaning_imp,hside]
  constructor
  · intro h
    funext f
    have hf : cycle (standardFrame f.val).face e ≠ 0 := by simpa using f.property
    simpa only [standardFrame_face] using (meaning_matchFace_atoms (Fin.cons (frameCode b (standardFrame f.val)) env)
      (var 0) st.up tt.up _ e e s t rfl hs ht hf hf hn).mp (h _ hf)
  · intro h C hC
    apply (meaning_matchFace_atoms (Fin.cons (frameCode b C) env) (var 0) st.up tt.up C e e s t rfl hs ht hC hC hn).mpr
    exact congrFun h ⟨C.face,hC⟩

lemma meaning_acceptsFaces (env : Fin k → HF (Atom b)) (F xt et st : QuotedTerm k)
    (x : Finset (Σ e : Edge n, LocalGroup e)) (e : Edge n) (s : LocalGroup e)
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl))
    (he : et.meaning (atomInput b) env = edgeCode b e)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨e,s⟩)) (hn : 1 ≤ n) :
    (allIn F ((side (var 0) et.up).imp
      (allIn xt.up ((onSide (var 1) (var 0)).imp
        (matchFace (var 1) st.up.up (var 0)))))).meaning (atomInput b) env ↔ AcceptsFaces x e s := by
  have hside (C : CycleFrame n) := meaning_side (Fin.cons (frameCode b C) env) (var 0) et.up C e rfl he
  have hon (C : CycleFrame n) (a : Σ e : Edge n, LocalGroup e) :=
    meaning_onSide (Fin.cons (atom (.inl a)) (Fin.cons (frameCode b C) env))
      (var 1) (var 0) C a.1 a.2 rfl rfl
  simp only [meaning_allIn,hF,forall_exists_index,forall_apply_eq_imp_iff,meaning_imp,hside,
    QuotedTerm.meaning_up,hx,all_stateCode,Finset.forall_mem_image,hon]
  constructor
  · intro h a ha f he hf
    have he' : cycle (standardFrame f).face e ≠ 0 := by simpa using he
    have hf' : cycle (standardFrame f).face a.1 ≠ 0 := by simpa using hf
    simpa only [standardFrame_face] using (meaning_matchFace_atoms (Fin.cons (atom (.inl a)) (Fin.cons (frameCode b (standardFrame f)) env))
      (var 1) st.up.up (var 0) _ e a.1 s a.2 rfl hs rfl he' hf' hn).mp (h _ he' ha hf')
  · intro h C hC a ha hCa
    exact (meaning_matchFace_atoms (Fin.cons (atom (.inl a)) (Fin.cons (frameCode b C) env))
      (var 1) st.up.up (var 0) C e a.1 s a.2 rfl hs rfl hC hCa hn).mpr (h a ha C.face hC hCa)

lemma mem_candidates (env : Fin k → HF (Atom b)) (F N xt : QuotedTerm k)
    (D : Finset (Edge n)) (x : Finset (Σ e : Edge n, LocalGroup e))
    (hF : ∀ z, z ∈ elements (F.meaning (atomInput b) env) ↔ ∃ C : CycleFrame n, frameCode b C = z)
    (hN : N.meaning (atomInput b) env = ofFinset (D.image (edgeCode b)))
    (hx : xt.meaning (atomInput b) env = stateCode (x.image Sum.inl)) (hn : 1 ≤ n) (z : HF (Atom b)) :
    z ∈ elements ((candidates F N xt).meaning (atomInput b) env) ↔
      ∃ e ∈ D, ∃ s : LocalGroup e, z = atom (.inl ⟨e,s⟩) ∧ AcceptsFaces x e s := by
  have hac (e : Edge n) (s : LocalGroup e) :=
    meaning_acceptsFaces (Fin.cons (atom (.inl ⟨e,s⟩)) (Fin.cons (edgeCode b e) env))
      F.up.up xt.up.up (var 1) (var 0) x e s hF hx rfl rfl hn
  simp only [candidates,meaning_bind,hN,elements_ofFinset,Finset.mem_biUnion,Finset.mem_image,
    QuotedTerm.meaning_filter,meaning_var,Fin.cons_zero,elements_ofFinset,Finset.mem_filter]
  constructor
  · rintro ⟨_,⟨e,he,rfl⟩,hz,hs⟩
    obtain ⟨s,rfl⟩ := (mem_edgeCode_iff e z).mp hz
    exact ⟨e,he,s,rfl,(hac e s).mp hs⟩
  · rintro ⟨e,he,s,rfl,hs⟩
    exact ⟨edgeCode b e,⟨e,he,rfl⟩,(mem_edgeCode_iff e _).mpr ⟨s,rfl⟩,(hac e s).mpr hs⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary QuotedTerm

variable {n : ℕ} {b : Vertex n → Scalar}

def originVertex : Vertex n := (0,0,0)

lemma dist_origin_head (h : Edge n) :
    (boxGraph n).dist originVertex (head h) = (boxGraph n).dist originVertex (tail h) + 1 := by
  rcases h with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [boxGraph_dist,originVertex,head,tail,Nat.dist] ; omega

lemma exists_traversalCode (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n)
    (Q : HF (Atom b) → Prop) :
    (∃ z ∈ elements (traversalCode b T e u v), Q z) ↔
      ∃ h a c, Traverses T e u v h a c ∧ Q (HFTriple (edgeCode b h) (vertexCode b a) (vertexCode b c)) := by
  constructor
  · rintro ⟨z,hz,hQ⟩
    obtain ⟨h,a,c,htr,rfl⟩ := (mem_traversalCode T e u v z).mp hz
    exact ⟨h,a,c,htr,hQ⟩
  · rintro ⟨h,a,c,htr,hQ⟩
    exact ⟨_,(mem_traversalCode T e u v _).mpr ⟨h,a,c,htr,rfl⟩,hQ⟩

lemma input_z_iff (e : Edge n) (s t : LocalGroup e) (δ : Scalar) :
    inputHF (atomInput b) (.Z δ) (atom (.inl ⟨e,s⟩)) (atom (.inl ⟨e,t⟩)) = true ↔
      (s⁻¹*t).flow = δ := by
  rw [inputHF_atoms]
  change decide (AtomRelation b (.Z δ) (.inl ⟨e,s⟩) (.inl ⟨e,t⟩)) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h; cases h with | z e s t δ h => exact h
  · intro h; exact .z e s t δ h

namespace QuotedGrid

open QuotedFormula SourceSyntax

variable {k : ℕ}

lemma meaning_traversalEdge (env : Fin k → HF (Atom b)) (Γ ht : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (h : Edge n)
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b T e u v)
    (hh : ht.meaning (atomInput b) env = edgeCode b h) :
    (traversalEdge Γ ht).meaning (atomInput b) env ↔ ∃ a c, Traverses T e u v h a c := by
  simp only [traversalEdge,meaning_existsIn,hΓ,exists_traversalCode,
    meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,HFTriple,firstHF_pair (atomInput b),
    QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff]
  constructor
  · rintro ⟨d,a,c,htr,rfl⟩
    exact ⟨a,c,htr⟩
  · rintro ⟨a,c,htr⟩
    exact ⟨h,a,c,htr,rfl⟩

lemma meaning_directedZ (env : Fin k → HF (Atom b)) (R Γ ot ht st tt : QuotedTerm k)
    (T : Finset (Edge n)) (e : Edge n) (u v : Vertex n) (o : Vertex n)
    (h : Edge n) (s t : LocalGroup h)
    (hR : R.meaning (atomInput b) env = distancesCode b (boxGraph n))
    (hΓ : Γ.meaning (atomInput b) env = traversalCode b T e u v)
    (ho : ot.meaning (atomInput b) env = vertexCode b o)
    (hh : ht.meaning (atomInput b) env = edgeCode b h)
    (hs : st.meaning (atomInput b) env = atom (.inl ⟨h,s⟩))
    (ht' : tt.meaning (atomInput b) env = atom (.inl ⟨h,t⟩)) (hn : 1 ≤ n) :
    (directedZ R Γ ot ht st tt).meaning (atomInput b) env ↔ ∃ a c,
      Traverses T e u v h a c ∧
        if (boxGraph n).dist o a < (boxGraph n).dist o c then
          (s⁻¹*t).flow = 1 else (s⁻¹*t).flow = 2 := by
  have hd1 (d : Edge n) (a c : Vertex n) :
      (distanceAt R.up ot.up (var 0).snd.fst).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
      ordinal ((boxGraph n).dist o a) := by
    have hRu : R.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
        distancesCode b (boxGraph n) := hR
    have hov : ot.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b o := ho
    have hav : ((var 0).snd.fst : QuotedTerm (k+1)).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b a := by
      simp only [meaning_fst,meaning_snd,meaning_var,Fin.cons_zero,HFTriple,
        secondHF_pair (atomInput b),firstHF_pair (atomInput b)]
    exact meaning_distanceAt (atomInput b) _ R.up ot.up (var 0).snd.fst
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) o a
      hRu hov hav (vertex_card_le_atoms hn)
  have hd2 (d : Edge n) (a c : Vertex n) :
      (distanceAt R.up ot.up (var 0).snd.snd).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
      ordinal ((boxGraph n).dist o c) := by
    have hRu : R.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) =
        distancesCode b (boxGraph n) := hR
    have hov : ot.up.meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b o := ho
    have hcv : ((var 0).snd.snd : QuotedTerm (k+1)).meaning (atomInput b)
        (Fin.cons (HFTriple (edgeCode b d) (vertexCode b a) (vertexCode b c)) env) = vertexCode b c := by
      simp only [meaning_snd,meaning_var,Fin.cons_zero,HFTriple,secondHF_pair (atomInput b)]
    exact meaning_distanceAt (atomInput b) _ R.up ot.up (var 0).snd.snd
      (vertexCode b) (vertexCode_injective hn) (boxGraph n) (boxGraph_connected n) o c
      hRu hov hcv (vertex_card_le_atoms hn)
  simp only [HFTriple] at hd1 hd2
  simp only [directedZ,meaning_existsIn,hΓ,exists_traversalCode,
    meaning_and,meaning_eq,meaning_fst,meaning_var,Fin.cons_zero,HFTriple,firstHF_pair (atomInput b),
    QuotedTerm.meaning_up,hh,edgeCode_injective.eq_iff,meaning_or,meaning_mem,meaning_neg,
    meaning_input,hs,ht',input_z_iff]
  constructor
  · rintro ⟨d,a,c,htr,hd,hZ⟩
    subst d
    refine ⟨a,c,htr,?_⟩
    change (_ ∧ _) ∨ (¬_ ∧ _) at hZ
    rw [hd1,hd2,ordinal_mem_elements] at hZ
    split_ifs with hl
    · exact hZ.elim And.right (fun hz => False.elim (hz.1 hl))
    · exact hZ.elim (fun hz => False.elim (hl hz.1)) And.right
  · rintro ⟨a,c,htr,hZ⟩
    refine ⟨h,a,c,htr,rfl,?_⟩
    rw [hd1,hd2,ordinal_mem_elements]
    split_ifs at hZ with hl
    · exact Or.inl ⟨hl,hZ⟩
    · exact Or.inr ⟨hl,hZ⟩

end QuotedGrid

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.TreeTest

variable {n : ℕ}

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma cut_reachable_tail_iff (h : Edge n) (hh : h ∈ P.treeEdges) (v : Vertex n) :
    (P.cut h).Reachable v (tail h) ↔ ¬(P.cut h).Reachable (head h) v := by
  constructor
  · intro hv hh'
    exact P.cut_separated h hh (hh'.trans hv).symm
  · intro hv
    rcases cut_cover P.treeEdges P.graph_connected h v with h' | h'
    · exact False.elim (hv h')
    · exact h'.symm

lemma cut_reachable_head_iff (h : Edge n) (v : Vertex n) :
    (P.cut h).Reachable v (head h) ↔ (P.cut h).Reachable (head h) v :=
  ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩

lemma traverses_forward (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    Traverses P.treeEdges e (tail e) (head e) h (tail h) (head h) ↔
      (P.flow e 1).val h = 1 := by
  by_cases hhe : h=e
  · subst h
    simp [Traverses,he,P.flow_self e he]
  by_cases hh : h ∈ P.treeEdges
  · have hf := P.flow_cut e he 1 h hh
    have hr := P.cut_reachable_iff h hh (head e) (tail e)
    have ht := P.cut_reachable_tail_iff h hh (head e)
    have hu := P.cut_reachable_head_iff h (tail e)
    change _ ↔ _ at hr ht hu
    simp only [Traverses,hhe,false_and,false_or,hh,true_and,
      and_self,true_or,head_ne_tail h,Ne.symm (head_ne_tail h)]
    change (¬(P.cut h).Reachable (head e) (tail e) ∧
      (P.cut h).Reachable (head e) (tail h) ∧ (P.cut h).Reachable (tail e) (head h)) ↔ _
    rw [hr,ht,hu,hf,mul_one]
    unfold cutIndicator
    by_cases ha : (P.cut h).Reachable (head h) (tail e) <;>
      by_cases hb : (P.cut h).Reachable (head h) (head e) <;> simp [ha,hb] ; decide
  · rw [P.flow_other e h hh hhe 1]
    simp [Traverses,hhe,hh]

lemma traverses_reverse (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    Traverses P.treeEdges e (tail e) (head e) h (head h) (tail h) ↔
      (P.flow e 1).val h = -1 := by
  by_cases hhe : h=e
  · subst h
    simp [Traverses,he,P.flow_self e he,head_ne_tail] ; decide
  by_cases hh : h ∈ P.treeEdges
  · have hf := P.flow_cut e he 1 h hh
    have hr := P.cut_reachable_iff h hh (head e) (tail e)
    have ht := P.cut_reachable_tail_iff h hh (tail e)
    have hu := P.cut_reachable_head_iff h (head e)
    simp only [Traverses,hhe,false_and,false_or,hh,true_and,and_self,
      or_true,head_ne_tail h,Ne.symm (head_ne_tail h)]
    change (¬(P.cut h).Reachable (head e) (tail e) ∧
      (P.cut h).Reachable (head e) (head h) ∧ (P.cut h).Reachable (tail e) (tail h)) ↔ _
    rw [hr,ht,hu,hf,mul_one]
    unfold cutIndicator
    by_cases ha : (P.cut h).Reachable (head h) (tail e) <;>
      by_cases hb : (P.cut h).Reachable (head h) (head e) <;> simp [ha,hb] ; decide
  · rw [P.flow_other e h hh hhe 1]
    simp [Traverses,hhe,hh]

lemma traverses_endpoints {e h : Edge n} {u v : Vertex n}
    (htr : Traverses P.treeEdges e (tail e) (head e) h u v) :
    (u=tail h ∧ v=head h) ∨ (v=tail h ∧ u=head h) := by
  rcases htr with ⟨rfl,rfl,rfl⟩ | ⟨_,hh,_⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · exact hh

end ParentEdges

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS WitnessedChoice.TreeTest Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma scalar_cases (a : Scalar) : a=0 ∨ a=1 ∨ a= -1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

namespace ParentEdges

variable {T : RootedTree (Vertex n)} (P : ParentEdges T)

lemma traverses_iff_nonzero (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c) ↔ (P.flow e 1).val h ≠ 0 := by
  constructor
  · rintro ⟨a,c,htr⟩
    rcases P.traverses_endpoints htr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(P.traverses_forward e he h).mp htr]; decide
    · rw [(P.traverses_reverse e he h).mp htr]; decide
  · intro hne
    rcases scalar_cases ((P.flow e 1).val h) with hz | hp | hm
    · exact False.elim (hne hz)
    · exact ⟨tail h,head h,(P.traverses_forward e he h).mpr hp⟩
    · exact ⟨head h,tail h,(P.traverses_reverse e he h).mpr hm⟩

lemma directed_flow_iff (e : Edge n) (he : e ∉ P.treeEdges) (h : Edge n) (z : Scalar) :
    (∃ a c, Traverses P.treeEdges e (tail e) (head e) h a c ∧
      if (boxGraph n).dist originVertex a < (boxGraph n).dist originVertex c then z=1 else z=2) ↔
      (P.flow e 1).val h ≠ 0 ∧ z=(P.flow e 1).val h := by
  have hlt := dist_origin_head h
  have hm : (2 : Scalar) = -1 := by decide
  constructor
  · rintro ⟨a,c,htr,hz⟩
    have hne := (P.traverses_iff_nonzero e he h).mp ⟨a,c,htr⟩
    refine ⟨hne,?_⟩
    rcases P.traverses_endpoints htr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [(P.traverses_forward e he h).mp htr]
      simpa only [ite_eq_left (show (boxGraph n).dist originVertex (tail h) <
        (boxGraph n).dist originVertex (head h) by omega)] using hz
    · rw [(P.traverses_reverse e he h).mp htr]
      simpa only [ite_eq_right (show ¬(boxGraph n).dist originVertex (head h) <
        (boxGraph n).dist originVertex (tail h) by omega),hm] using hz
  · rintro ⟨hne,rfl⟩
    rcases scalar_cases ((P.flow e 1).val h) with hz | hp | hm'
    · exact False.elim (hne hz)
    · refine ⟨tail h,head h,(P.traverses_forward e he h).mpr hp,?_⟩
      rw [ite_eq_left (by omega),hp]
    · refine ⟨head h,tail h,(P.traverses_reverse e he h).mpr hm',?_⟩
      rw [ite_eq_right (by omega),hm',hm]

end ParentEdges

lemma local_central_iff (h : Edge n) (s t : LocalGroup h) (z : Scalar) :
    t = (⟨0,z⟩ : LocalGroup h) * s ↔ s.face = t.face ∧ (s⁻¹*t).flow = z := by
  constructor
  · rintro rfl
    simp only [Support.H.mul_face,zero_add,true_and,Support.H.mul_flow,Support.H.inv_flow,
      Support.H.inv_face,Support.correction_zero_left,add_zero,Support.correction_neg_left,
      Support.correction_self,neg_zero]
    abel
  · rintro ⟨hf,hz⟩
    apply Support.H.ext
    · simpa only [Support.H.mul_face,zero_add] using hf.symm
    · simp only [Support.H.mul_flow,Support.H.inv_flow,Support.H.inv_face,←hf,
        Support.correction_neg_left,Support.correction_self,neg_zero,add_zero] at hz
      simp only [Support.H.mul_flow,Support.correction_zero_left,add_zero]
      rw [←hz]
      abel

end

end WitnessedSeparation.Grid

end OAI
