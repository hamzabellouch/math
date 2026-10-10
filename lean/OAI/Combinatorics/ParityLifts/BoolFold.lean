import OAI.Combinatorics.ParityLifts.LeafBounds

namespace OAI

namespace ParityWL.Complexity

def FCode.anyStep (p : FCode) : FCode :=
  .cond .right (.seq .left p) (.const (treeEncode true))

def FCode.any (p : FCode) : FCode :=
  .seq (.pair .id (.const (treeEncode false)))
    (.seq (.loop p.anyStep.foldBody) .right)

lemma bool_size (b : Bool) : (treeEncode b).size≤3 := by
  cases b <;> decide

lemma BEval.anyStep {α : Type} [TreeCodec α] (p : FCode) (a : α) (acc b : Bool) (B : ℕ)
    (h : BEval p (treeEncode a) B (treeEncode b)) :
    BEval p.anyStep (treeEncode (a,acc))
      (10*((treeEncode a).size+B+5)) (treeEncode (acc||b)) := by
  have ha := bool_size acc
  cases acc
  · apply (BEval.nil_cond (g:=FCode.const (treeEncode true))
      (by simpa only [treeEncode_pair,DataTree.child,ite_true,ite_false,treeEncode_false] using BEval.right (treeEncode (a,false)))
      ((BEval.left (treeEncode (a,false))).seq h)).mono
    simp only [treeEncode_pair,treeEncode_false,DataTree.size]
    omega
  · apply (BEval.node_cond (f:=FCode.seq .left p)
      (by simpa only [treeEncode_pair,DataTree.child,ite_true,ite_false,treeEncode_false] using BEval.right (treeEncode (a,true)))
      (by simp : treeEncode true≠.nil) (BEval.const (treeEncode true) (treeEncode (a,true)))).mono
    simp only [treeEncode_pair,treeEncode_true,DataTree.size]
    omega

lemma BEval.foldBody {α β : Type} [TreeCodec α] [TreeCodec β]
    {p : FCode} {a : α} {xs : List α} {b c : β} {B : ℕ}
    (h : BEval p (treeEncode (a,b)) B (treeEncode c)) :
    BEval p.foldBody (treeEncode (a::xs,b))
      (10*((treeEncode (a::xs,b)).size+1)+B) (treeEncode (xs,c)) := by
  let s := treeEncode (a::xs,b)
  have ht := ((BEval.left s).seq (BEval.right (s.child false)))
  have hh := ((BEval.left s).seq (BEval.left (s.child false))).pair (BEval.right s)
  have hr := ht.pair (hh.seq h)
  apply hr.mono
  have := s.size_child false
  change _≤10*(s.size+1)+B
  omega

lemma BEval.anyLoop {α : Type} [TreeCodec α] (p : FCode) (P : α → Prop)
    (S B : ℕ) (xs : List α) (acc : Bool)
    (hs : ∀ a∈xs, (treeEncode a).size≤S)
    (hb : ∀ a∈xs, ∃ b, BEval p (treeEncode a) B (treeEncode b) ∧ (b=true↔P a)) :
    ∃ b, BEval (.loop p.anyStep.foldBody) (treeEncode (xs,acc))
      (100*(xs.length+1)^2*(S+B+5)) (treeEncode (([]:List α),b)) ∧
      (b=true↔acc=true ∨ ∃ a∈xs, P a) := by
  induction xs generalizing acc with
  | nil =>
    refine ⟨acc,(BEval.loop_stop _ _ rfl).mono ?_,by simp⟩
    have := bool_size acc
    simp only [List.length_nil,Nat.zero_add,one_pow,Nat.mul_one,treeEncode_pair,treeEncode_nil,DataTree.size]
    omega
  | cons a xs ih =>
    obtain ⟨b,hb',he⟩ := hb a (by simp)
    obtain ⟨c,hc,hec⟩ := ih (acc||b) (fun x hx => hs x (by simp [hx]))
      (fun x hx => hb x (by simp [hx]))
    refine ⟨c,?_,by simp only [hec,Bool.or_eq_true,List.mem_cons,exists_eq_or_imp,he]; tauto⟩
    have ha := hs a (by simp)
    have hsize : (treeEncode (a::xs)).size≤1+(a::xs).length*(S+1) := by
      rw [treeEncode_list_size]
      have h := list_sum_map_le (a::xs) (fun x => (treeEncode x).size+1) (S+1) (fun x hx => Nat.add_le_add_right (hs x hx) 1)
      omega
    have hacc := bool_size acc
    have hstep := (BEval.anyStep p a acc b B hb').foldBody (xs:=xs)
    apply (BEval.loop_next (by simp [DataTree.child]) hstep hc).mono
    simp only [treeEncode_pair,DataTree.size,List.length_cons] at *
    nlinarith

lemma BEval.any {α : Type} [TreeCodec α] (p : FCode) (P : α → Prop)
    (S B : ℕ) (xs : List α)
    (hs : ∀ a∈xs, (treeEncode a).size≤S)
    (hb : ∀ a∈xs, ∃ b, BEval p (treeEncode a) B (treeEncode b) ∧ (b=true↔P a)) :
    ∃ b, BEval p.any (treeEncode xs)
      (500*(xs.length+1)^2*(S+B+5)) (treeEncode b) ∧ (b=true ↔ ∃ a∈xs,P a) := by
  obtain ⟨b,hb',he⟩ := BEval.anyLoop p P S B xs false hs hb
  have hinit := (BEval.id (treeEncode xs)).pair (BEval.const (treeEncode false) (treeEncode xs))
  have hlast := BEval.right (treeEncode (([]:List α),b))
  refine ⟨b,(hinit.seq (hb'.seq hlast)).mono ?_,by simpa using he⟩
  have hsize : (treeEncode xs).size≤1+xs.length*(S+1) := by
    rw [treeEncode_list_size]
    have h := list_sum_map_le xs (fun x => (treeEncode x).size+1) (S+1) (fun x hx => Nat.add_le_add_right (hs x hx) 1)
    omega
  have hbool := bool_size b
  simp only [treeEncode_false,DataTree.size,treeEncode_pair,treeEncode_nil] at *
  nlinarith
end ParityWL.Complexity

end OAI
