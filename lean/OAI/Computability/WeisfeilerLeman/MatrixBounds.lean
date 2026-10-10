import OAI.Computability.WeisfeilerLeman.MatrixWriter

namespace OAI

universe uJ uK uL uA

namespace WLTime.OneTape
open CircuitEncoding
variable (M : OneTape)

noncomputable def matrixCoefficient (d q : ℕ) : ℕ := by
  classical
  let P := Schematic.Node (Tableau.Gate M.Cell) (BoxTableau.Label M.Cell d (q+1))
  let E := Schematic.Edge (BoxTableau.Label M.Cell d (q+1)) (M.Cell ⊕ Fin q)
    {f : M.Cell // M.letterAccepting f}
  exact (((d+q+1)*(Fintype.card P+Fintype.card E*(8*(d+q+2)+1)))*4^4+1)^3

theorem computation_matrices (w : List Bool) (hm : 2 ≤ w.length) (d q T n : ℕ)
    (hr : 2 ≤ d+q) (hT : T ≤ w.length^d-1)
    (hL : 2*T+w.length+2< w.length^(q+1))
    (hh : (M.run lineShift (M.initial w) T).state.val=1 ∨
      (M.run lineShift (M.initial w) T).state.val=2)
    (hn : M.matrixCoefficient d q*w.length^6 ≤ n) :
    ∃ G H : Graph n, G.diameterTwo ∧ H.diameterTwo ∧
      (Equivalent .joint (d+q+1) G H ↔ ¬M.toTM.accepts w) ∧
      (Equivalent .separate (d+q+2) G H ↔ ¬M.toTM.accepts w) := by
  classical
  let C : Schematic (d+(q+1)) w.length _ _ _ _ :=
    BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting
  let : Nonempty (Schematic.Node (Tableau.Gate M.Cell) (BoxTableau.Label M.Cell d (q+1))) :=
    ⟨.dummy⟩
  have hdim (p) : 2^(C.consistency.dim p) ≤ 4 := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (C.dim_le_two p)
    exact h
  obtain ⟨G,H,hG,hH,hj,hs⟩ := C.consistency.matrix_compression_six hr hm 4 (by decide)
    hdim n (by exact hn)
  have hc : C.consistency.ArcConsistent ↔ ¬M.toTM.accepts w :=
    C.consistency_iff_tests_false.trans (M.product_simulation w (by omega) d q T hT hL hh)
  exact ⟨G,H,hG,hH,hj.trans hc,hs.trans hc⟩

end WLTime.OneTape

namespace WLTime.OneTape
variable (M : OneTape)
open CircuitEncoding

theorem bounded_acceptance (w : List Bool) (T : ℕ) :
    (M.run lineShift (M.initial w) T).state.val=1 ↔
      ∃ t ≤ T,(M.toTM.run w t).state.val=1 := by
  have he := congrArg (fun C : M.toTM.Config => C.state.val) (M.embed_run w T)
  change (M.run lineShift (M.initial w) T).state.val=(M.toTM.run w T).state.val at he
  rw [he]
  constructor
  · intro h; exact ⟨T,le_rfl,h⟩
  · rintro ⟨t,ht,h⟩
    rw [M.toTM.run_frozen w (Or.inl h) ht]
    exact h

theorem product_bounded (w : List Bool) (hm : 0<w.length) (d q : ℕ)
    (hL : 2*(w.length^d-1)+w.length+2<w.length^(q+1)) :
    (∀ g, (BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting :
      Schematic (d+(q+1)) w.length _ _ _ _).expand.test g=true →
      ¬(BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting).expand.TrueAt g) ↔
      ¬∃ t ≤ w.length^d-1,(M.toTM.run w t).state.val=1 := by
  let : NeZero (w.length^(q+1)) := ⟨Nat.ne_of_gt (Nat.pow_pos hm)⟩
  rw [BoxTableau.local_equivalence M.localRule (M.inputCell w) M.blankCell M.letterAccepting hm]
  rw [← M.bounded_acceptance w (w.length^d-1)]
  have hr := M.ring_run_agrees w (w.length^d-1) (w.length^(q+1)) hL (w.length^d-1) le_rfl
  rw [← hr.1,← M.accepting_snapshot, M.run_snapshot]
  simp only [not_exists]
  constructor
  · intro h j
    let f : Fin (w.length^(q+1)) ≃ ZMod (w.length^(q+1)) := (ZMod.finEquiv _).toEquiv
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) f
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) (f.symm j)
    exact (by simpa only [f.apply_symm_apply] using he) ▸ h (f.symm j)
  · intro h j
    have he := Tableau.run_reindex M.localRule (Digits.inc _) (ringShift _) (ZMod.finEquiv _).toEquiv
      (BoxTableau.initialRing (M.inputCell w) M.blankCell) (M.snapshot (M.ringInitial _ w))
      Digits.finEquiv_shift (M.ring_initial_digits w hm q) (w.length^d-1) j
    rw [he]
    exact h _

theorem bounded_matrices (w : List Bool) (hm : 2 ≤ w.length) (d q n : ℕ)
    (hr : 2 ≤ d+q) (hL : 2*(w.length^d-1)+w.length+2<w.length^(q+1))
    (hn : M.matrixCoefficient d q*w.length^6 ≤ n) :
    ∃ G H : Graph n, G.diameterTwo ∧ H.diameterTwo ∧
      (Equivalent .joint (d+q+1) G H ↔ ¬∃ t ≤ w.length^d-1,(M.toTM.run w t).state.val=1) ∧
      (Equivalent .separate (d+q+2) G H ↔ ¬∃ t ≤ w.length^d-1,(M.toTM.run w t).state.val=1) := by
  classical
  let C : Schematic (d+(q+1)) w.length _ _ _ _ :=
    BoxTableau.schematic M.localRule (M.inputCell w) M.blankCell M.letterAccepting
  let : Nonempty (Schematic.Node (Tableau.Gate M.Cell) (BoxTableau.Label M.Cell d (q+1))) :=
    ⟨.dummy⟩
  have hdim (p) : 2^(C.consistency.dim p) ≤ 4 := Nat.pow_le_pow_right (by decide) (C.dim_le_two p)
  obtain ⟨G,H,hG,hH,hj,hs⟩ := C.consistency.matrix_compression_six hr hm 4 (by decide)
    hdim n hn
  have hc : C.consistency.ArcConsistent ↔ ¬∃ t ≤ w.length^d-1,(M.toTM.run w t).state.val=1 :=
    C.consistency_iff_tests_false.trans (M.product_bounded w (by omega) d q hL)
  exact ⟨G,H,hG,hH,hj.trans hc,hs.trans hc⟩
end WLTime.OneTape

namespace WLTime.OneTape.Symbolic
open CircuitEncoding NatCode Compression Enumeration
variable (M : OneTape) (d q : ℕ)
open scoped Classical

noncomputable def baseOrder (m : ℕ) : ℕ :=
  let C := coefficient M d q (d+q+2)
  1+C*m^2*((C*m^2+1)^2+1)

 theorem listing_length (w : List Bool) (pad : ℕ) :
    (listing M d q (d+q+2) w pad).items.length=baseOrder M d q w.length+pad := by
  rw [Enumeration.Listing.length_eq_card]
  simp only [RawVertex,Enumeration.Vertex,Fintype.card_option,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  have hL : (instanceData M d q w).slotLimit (d+q+2)=
      (coefficient M d q (d+q+2)*w.length^2+1)^2+1 := rfl
  rw [hL]
  unfold baseOrder coefficient ConsistencyData.rectCoefficient
  simp only [ConsistencyData.BlockTag,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  ring_nf

noncomputable def pairGraph (hr : 2≤d+q) (w : List Bool) (pad : ℕ) (ε : F₂) :
    Graph (listing M d q (d+q+2) w pad).items.length :=
  (listing M d q (d+q+2) w pad).matrix
    ((instanceData M d q w).rectangularGraph (d+q+2) (by omega) (by omega) ε pad)

 theorem pairGraph_diameter (hr : 2≤d+q) (w : List Bool) (pad : ℕ) (ε : F₂) :
    (pairGraph M d q hr w pad ε).diameterTwo := by
  apply Graph.ofSimple_diameter
  · rw [listing_length]; dsimp [baseOrder]; omega
  · exact Marking.raw_diameter _ _

 theorem pairGraph_correct (hr : 2≤d+q) (w : List Bool) (hm : 2≤w.length) (pad : ℕ)
    (hL : 2*(w.length^d-1)+w.length+2<w.length^(q+1)) :
    (Equivalent .joint (d+q+1) (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1) ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1) ∧
    (Equivalent .separate (d+q+2) (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1) ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1) := by
  have hn : 0<(listing M d q (d+q+2) w pad).items.length := by
    rw [listing_length]; dsimp [baseOrder]; omega
  let : Nonempty (Node M d q) := ⟨.dummy⟩
  have he : Wins (pairGraph M d q hr w pad 0) (pairGraph M d q hr w pad 1)
      (fun _ : Fin (d+q+2) => none) ↔ (instanceData M d q w).ArcConsistent :=
    (wins_ofSimple_iff _ _ _ _).trans ((instanceData M d q w).rectangular_wins_iff_ac hr hm pad)
  have ha : (instanceData M d q w).ArcConsistent ↔
      ¬∃t≤w.length^d-1,(M.toTM.run w t).state.val=1 :=
    (schema M d q w).consistency_iff_tests_false.trans (M.product_bounded w (by omega) d q hL)
  exact ⟨(joint_equivalent_iff_wins hn (by omega)).trans (he.trans ha),
    (separate_equivalent_iff_wins hn).trans (he.trans ha)⟩

variable {J : Type uJ}
noncomputable def pairWriter (N L P : Expr J) : Writer J :=
  .seq (matrixWriter M d q (d+q+2) N L P 0) (matrixWriter M d q (d+q+2) N L P 1)

 theorem pairWriter_eval (N L P : Expr J) (hr : 2≤d+q)
    (σ : J → ℕ) (w : List Bool) (pad : ℕ)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit (d+q+2))
    (hP : P.eval σ w=pad) :
    (pairWriter M d q N L P).eval σ w=
      matrixBits (pairGraph M d q hr w pad 0)++matrixBits (pairGraph M d q hr w pad 1) := by
  simp only [pairWriter,Writer.eval,pairGraph]
  erw [Listing.matrix_bits,Listing.matrix_bits]
  rw [matrixWriter_eval M d q _ _ _ _ (by omega) (by omega) 0 σ w pad hN hL hP,
    matrixWriter_eval M d q _ _ _ _ (by omega) (by omega) 1 σ w pad hN hL hP]
  rfl

 theorem pairWriter_depth (N L P : Expr J) : (pairWriter M d q N L P).depth≤6 :=
  max_le (matrixWriter_depth M d q _ N L P 0) (matrixWriter_depth M d q _ N L P 1)

 theorem pairWriter_safe (N L P : Expr J) (σ : J → ℕ) (w : List Bool) (B : ℕ) (hm : 1≤w.length)
    (hN : N.eval σ w=w.length) (hL : L.eval σ w=(instanceData M d q w).slotLimit (d+q+2))
    (hNB : N.Bounded σ w B) (hLB : L.Bounded σ w B) (hPB : P.Bounded σ w B)
    (hC : coefficient M d q (d+q+2)≤B) :
    (pairWriter M d q N L P).Safe σ w (6*B) :=
  ⟨matrixWriter_safe M d q _ N L P 0 σ w B hm hN hL hNB hLB hPB hC,
    matrixWriter_safe M d q _ N L P 1 σ w B hm hN hL hNB hLB hPB hC⟩
end WLTime.OneTape.Symbolic

namespace WLTime.TypedStack.Code
variable {K : Type uK} {L : Type uL} {A : Type uA}
def controlSize : Code K A → ℕ
  | .skip => 1
  | .push _ _ | .pushDyn _ _ | .pop _ => 2
  | .seq p q => p.controlSize+q.controlSize
  | .branch _ p q => 1+p.controlSize+q.controlSize
  | .loop _ p => 1+p.controlSize
 theorem card_state (p : Code K A) : Fintype.card p.State=p.controlSize := by
  induction p with
  | skip => exact Fintype.card_unique
  | push | pushDyn | pop => exact Fintype.card_fin 2
  | seq p q hp hq => simpa only [State,Fintype.card_sum,controlSize] using congrArg₂ (·+·) hp hq
  | branch t p q hp hq => simpa only [State,Fintype.card_sum,Fintype.card_unique,controlSize,Nat.add_assoc] using congrArg (1+·) (congrArg₂ (·+·) hp hq)
  | loop t p hp => simpa only [State,Fintype.card_sum,Fintype.card_unique,controlSize] using congrArg (1+·) hp
 @[simp] theorem relabel_controlSize (p : Code K A) (f : K → L) : (p.relabel f).controlSize=p.controlSize := by
  induction p <;> simp_all [relabel,controlSize]
end WLTime.TypedStack.Code

namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]

def seqShared (p q : Program K) : Program K :=
  ⟨max p.scratch q.scratch,.seq
    (p.code.relabel (embed (Fin.castLE (Nat.le_max_left _ _))))
    (q.code.relabel (embed (Fin.castLE (Nat.le_max_right _ _))))⟩
 theorem seqShared_exec {p q : Program K} {s t u mid out}
    (hp : p.Exec s t mid) (hq : q.Exec mid u out) : (seqShared p q).Exec s (t+u) out := by
  exact .seq (raise_exec p hp _ (Fin.castLE_injective _)) (raise_exec q hq _ (Fin.castLE_injective _))
 omit [DecidableEq K] in
 @[simp] theorem seqShared_size (p q : Program K) :
    (seqShared p q).code.controlSize=p.code.controlSize+q.code.controlSize := by
  simp only [seqShared,Code.controlSize,Code.relabel_controlSize]
 omit [DecidableEq K] in
 @[simp] theorem pushes_scratch (a : K) (bs : List Bool) : (pushes a bs).scratch=0 := by
  induction bs <;> simp_all [pushes,skip,push,seq,ofCode]
 omit [DecidableEq K] in
 @[simp] theorem pushes_size (a : K) (bs : List Bool) : (pushes a bs).code.controlSize=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [pushes,seq,Code.controlSize,Code.relabel_controlSize,push,ofCode,ih,List.length_cons]; omega

 def doubleUnary (a : K) : Program K :=
  allocate (seqShared (copy (Sum.inr a) (Sum.inl (0 : Fin 1)))
    (ofCode (Code.transfer (Sum.inl (0 : Fin 1)) (Sum.inr a) false)))
 theorem doubleUnary_exec (a : K) (m : ℕ) (s : Stacks K Bool) (hm : s a=UnaryPrograms.numeral m) :
    (doubleUnary a).Exec s (17*m+3) (Function.update s a (UnaryPrograms.numeral (2*m))) := by
  let z : Stacks (Fin 1 ⊕ K) Bool := Sum.elim (fun _ => []) s
  let mid := Function.update z (.inl 0) (UnaryPrograms.numeral m)
  have hc : (copy (.inr a) (.inl (0 : Fin 1))).Exec z (12*m+2) mid := by
    simpa only [z,Sum.elim_inr,Sum.elim_inl,hm,List.append_nil,UnaryPrograms.numeral_length] using
      copy_exec (Sum.inr a) (Sum.inl (0 : Fin 1)) (by simp) z
  have ht := ofCode_exec (Code.transfer_exec (Sum.inl (0 : Fin 1)) (Sum.inr a) (by simp) false mid)
  have he := seqShared_exec hc ht
  have hout : Function.update (Function.update mid (.inl 0) []) (.inr a)
      ((mid (.inl 0)).reverse++mid (.inr a))=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s a (UnaryPrograms.numeral (2*m))) := by
    funext k; cases k with
    | inl i => have hi : i=0 := Subsingleton.elim _ _; subst i; simp only [Function.update_of_ne (Sum.inl_ne_inr),Function.update_self,Sum.elim_inl]
    | inr k =>
      by_cases hk : k=a
      · subst k
        simp only [Function.update_self,mid,z,Function.update_of_ne (Sum.inr_ne_inl),Sum.elim_inr,hm,
          UnaryPrograms.numeral,List.reverse_replicate,List.replicate_append_replicate,two_mul]
      · simp only [mid,z,Function.update_of_ne (Sum.inr_ne_inl),
          Function.update_of_ne (fun h : Sum.inr k=Sum.inr a => hk (Sum.inr.inj h)),
          Function.update_of_ne hk,Sum.elim_inr]
  rw [hout] at he
  apply local_exec
  convert he using 1
  simp only [mid,Function.update_self,UnaryPrograms.numeral_length]
  omega
 omit [DecidableEq K] in
 @[simp] theorem doubleUnary_scratch (a : K) : (doubleUnary a).scratch=2 := rfl

 def loadDigits (a : K) : List ℕ → Program K
  | [] => skip
  | b::bs => seqShared (loadDigits a bs)
      (seqShared (doubleUnary a) (pushes a (UnaryPrograms.numeral b)))
 omit [DecidableEq K] in
 theorem loadDigits_scratch (a : K) (ds : List ℕ) : (loadDigits a ds).scratch≤2 := by
  induction ds with
  | nil => exact Nat.zero_le _
  | cons b bs ih => simpa only [loadDigits,seqShared,doubleUnary_scratch,pushes_scratch,max_zero] using max_le ih le_rfl
 omit [DecidableEq K] in
 theorem loadDigits_size (a : K) (ds : List ℕ) (hd : ∀b∈ds,b<2) :
    (loadDigits a ds).code.controlSize≤((doubleUnary a).code.controlSize+3)*ds.length+1 := by
  induction ds with
  | nil => rfl
  | cons b bs ih =>
    have hb := hd b (by simp)
    have hi := ih (fun c hc => hd c (by simp [hc]))
    simp only [loadDigits,seqShared_size,pushes_size,UnaryPrograms.numeral_length,List.length_cons]
    rw [Nat.mul_succ]
    omega
 theorem loadDigits_exec (a : K) (ds : List ℕ) (s : Stacks K Bool) (hs : s a=[]) :
    ∃t≤24*(ds.length+1)*(Nat.ofDigits 2 ds+1),
      (loadDigits a ds).Exec s t (Function.update s a (UnaryPrograms.numeral (Nat.ofDigits 2 ds))) := by
  induction ds with
  | nil =>
    refine ⟨1,by simp [Nat.ofDigits],?_⟩
    simpa only [loadDigits,Nat.ofDigits,UnaryPrograms.numeral,List.replicate_zero,←hs,Function.update_eq_self] using skip_exec s
  | cons b bs ih =>
    obtain ⟨t,ht,he⟩ := ih
    have hdouble := doubleUnary_exec a (Nat.ofDigits 2 bs)
      (Function.update s a (UnaryPrograms.numeral (Nat.ofDigits 2 bs))) (by simp)
    simp only [Function.update_idem] at hdouble
    have hpush := pushes_exec a (UnaryPrograms.numeral b)
      (Function.update s a (UnaryPrograms.numeral (2*Nat.ofDigits 2 bs)))
    have hf := seqShared_exec he (seqShared_exec hdouble hpush)
    refine ⟨t+(17*Nat.ofDigits 2 bs+3+(2*b+1)),?_,?_⟩
    · simp only [List.length_cons,Nat.ofDigits_cons]
      have hv : Nat.ofDigits 2 bs≤b+2*Nat.ofDigits 2 bs := by omega
      have hprod := Nat.mul_le_mul_left (24*(bs.length+1)) (Nat.add_le_add_right hv 1)
      nlinarith
    · simpa only [loadDigits,Function.update_self,Function.update_idem,UnaryPrograms.numeral_length,
        UnaryPrograms.numeral,List.length_replicate,←List.replicate_add,Nat.ofDigits_cons] using hf
 def loadNat (a : K) (n : ℕ) : Program K := loadDigits a (Nat.digits 2 n)
 theorem loadNat_exec (a : K) (n : ℕ) (s : Stacks K Bool) (hs : s a=[]) :
    ∃t≤24*((Nat.digits 2 n).length+1)*(n+1),
      (loadNat a n).Exec s t (Function.update s a (UnaryPrograms.numeral n)) := by
  simpa only [loadNat,Nat.ofDigits_digits] using loadDigits_exec a (Nat.digits 2 n) s hs
 omit [DecidableEq K] in
 theorem loadNat_size (a : K) (n : ℕ) :
    (loadNat a n).code.controlSize≤((doubleUnary a).code.controlSize+3)*(Nat.digits 2 n).length+1 := by
  exact loadDigits_size a _ (fun b hb => Nat.digits_lt_base (by decide) hb)
end WLTime.TypedStack.Program

namespace WLTime.TypedStack.Code
variable {K : Type uK} [DecidableEq K]
def countLoop (a b : K) : Code K Bool := .loop (nonempty a) (.seq (.pop a) (.push b true))
theorem countLoop_exec (a b : K) (hab : a≠b) (xs : List Bool) (s : Stacks K Bool) (hs : s a=xs) :
    (countLoop a b).Exec s (5*xs.length+1)
      (Function.update (Function.update s a []) b (UnaryPrograms.numeral xs.length++s b)) := by
  induction xs generalizing s with
  | nil =>
    have h := Exec.loop_false (p:=nonempty a) (a:=Code.seq (.pop a) (.push b true)) (s:=s)
      (by simp [nonempty,tops,hs])
    have hout : (Function.update (Function.update s a []) b (UnaryPrograms.numeral 0++s b))=s := by
      simp only [UnaryPrograms.numeral,List.replicate_zero,List.nil_append]
      funext k; by_cases hb : k=b
      · subst k; simp
      · by_cases ha : k=a
        · subst k; simp [hab,hs]
        · simp [hb,ha]
    change (countLoop a b).Exec s 1 _
    simp only [List.length_nil]
    rw [hout]
    exact h
  | cons x xs ih =>
    let z := Function.update (Function.update s a xs) b (true::s b)
    have he : (Code.seq (.pop a) (.push b true)).Exec s 4 z := by
      simpa only [hs,List.tail_cons,Function.update_of_ne hab.symm,z] using
        Exec.seq (Exec.pop s a) (Exec.push (Function.update s a (s a).tail) b true)
    have hz : z a=xs := by simp [z,hab]
    have hi := ih z hz
    have h := Exec.loop_true (p:=nonempty a) (by simp [nonempty,tops,hs]) he hi
    have hout : Function.update (Function.update s a []) b (UnaryPrograms.numeral (x::xs).length++s b)=
        Function.update (Function.update z a []) b (UnaryPrograms.numeral xs.length++z b) := by
      funext k; by_cases hb : k=b
      · subst k
        simp only [Function.update_self,z,UnaryPrograms.numeral,List.length_cons]
        rw [List.replicate_succ']; simp only [List.append_assoc,List.singleton_append]
      · by_cases ha : k=a
        · subst k; simp [hab,z]
        · simp [hb,ha,z]
    rw [hout]
    have htime : 5*(x::xs).length+1=4+(5*xs.length+1)+1 := by simp only [List.length_cons]; omega
    rw [htime]
    exact h
end WLTime.TypedStack.Code
namespace WLTime.TypedStack.Program
variable {K : Type uK} [DecidableEq K]
def countLength (a b : K) : Program K := allocate
  (seq (copy (.inr a) (.inl (0 : Fin 1))) (ofCode (Code.countLoop (.inl (0 : Fin 1)) (.inr b))))
theorem countLength_exec (a b : K) (s : Stacks K Bool) :
    (countLength a b).Exec s (17*(s a).length+3)
      (Function.update s b (UnaryPrograms.numeral (s a).length++s b)) := by
  let z : Stacks (Fin 1 ⊕ K) Bool := Sum.elim (fun _ => []) s
  let mid := Function.update z (.inl (0 : Fin 1)) (s a)
  have hc : (copy (.inr a) (.inl (0 : Fin 1))).Exec z (12*(s a).length+2) mid := by
    simpa only [z,Sum.elim_inr,Sum.elim_inl,List.append_nil] using
      copy_exec (Sum.inr a) (Sum.inl (0 : Fin 1)) (by simp) z
  have hl := ofCode_exec (Code.countLoop_exec (Sum.inl (0 : Fin 1)) (Sum.inr b) (by simp)
    (s a) mid (by simp [mid]))
  have he := seq_exec hc hl
  have hout : Function.update (Function.update mid (.inl 0) []) (.inr b)
      (UnaryPrograms.numeral (s a).length++mid (.inr b))=
      Sum.elim (fun _ : Fin 1 => []) (Function.update s b (UnaryPrograms.numeral (s a).length++s b)) := by
    funext k; cases k with
    | inl i => have hi:i=0 := Subsingleton.elim _ _; subst i; simp
    | inr k => simp only [mid,z,Function.update_of_ne Sum.inr_ne_inl,Sum.elim_inr,
        Function.update_apply,Sum.inr.injEq]
  rw [hout] at he
  apply local_exec
  convert he using 1
  omega
end WLTime.TypedStack.Program

namespace WLTime.NatCode.Expr
variable {K : Type uK}
def degree : Expr K → ℕ
  | .const _ | .var _ => 1
  | .binary _ a b => a.degree+b.degree+1
  | .bit a => a.degree+1

def AtomsBounded (σ : K → ℕ) (Q : ℕ) : Expr K → Prop
  | .const n => n≤Q
  | .var k => σ k≤Q
  | .binary _ a b => a.AtomsBounded σ Q ∧ b.AtomsBounded σ Q
  | .bit a => a.AtomsBounded σ Q

 theorem degree_pos (e : Expr K) : 1≤e.degree := by cases e <;> simp only [degree] <;> omega

 theorem bounded_degree (e : Expr K) (σ : K → ℕ) (w : List Bool) (Q : ℕ) (hQ : 2≤Q)
    (h : e.AtomsBounded σ Q) : e.Bounded σ w (Q^e.degree) := by
  induction e with
  | const n => simpa only [Bounded,degree,pow_one,AtomsBounded] using h
  | var k => simpa only [Bounded,degree,pow_one,AtomsBounded] using h
  | binary op a b ia ib =>
    have ha := ia h.1
    have hb := ib h.2
    have hqa : Q^a.degree≤Q^(a.degree+b.degree+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hqb : Q^b.degree≤Q^(a.degree+b.degree+1) := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨a.bounded_mono σ w ha hqa,b.bounded_mono σ w hb hqb,?_⟩
    have va := a.eval_le σ w _ ha
    have vb := b.eval_le σ w _ hb
    have h1a : 1≤Q^a.degree := Nat.one_le_pow _ _ (by omega)
    have h1b : 1≤Q^b.degree := Nat.one_le_pow _ _ (by omega)
    change op.eval (a.eval σ w) (b.eval σ w)≤Q^(a.degree+b.degree+1)
    rw [pow_succ,pow_add]
    cases op with
    | add =>
      change a.eval σ w+b.eval σ w≤_
      have haa : Q^a.degree≤Q^a.degree*Q^b.degree := Nat.le_mul_of_pos_right _ (by omega)
      have hbb : Q^b.degree≤Q^a.degree*Q^b.degree := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
    | mul =>
      change a.eval σ w*b.eval σ w≤_
      exact (Nat.mul_le_mul va vb).trans (Nat.le_mul_of_pos_right _ (by omega))
    | sub =>
      change a.eval σ w-b.eval σ w≤_
      exact (Nat.sub_le _ _).trans (va.trans (by simpa only [pow_succ,pow_add] using hqa))
  | bit a ia =>
    have ha := ia h
    exact ⟨a.bounded_mono σ w ha (Nat.pow_le_pow_right (by omega) (by simp [degree])),
      Nat.one_le_pow _ _ (by omega)⟩
end WLTime.NatCode.Expr

end OAI
