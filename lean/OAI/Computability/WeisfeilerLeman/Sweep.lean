import OAI.Computability.WeisfeilerLeman.Stacks

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

abbrev Tops := Fin M.count → Option (Fin M.alphabet)
abbrev TrackSymbol := Bool × M.Tops

inductive Purpose (K a q : ℕ) where
  | peek (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | push (k : Fin K) (letter : Fin a) (state : Fin q)
  | pop (k : Fin K) (state : Fin q)
  deriving Fintype, DecidableEq

inductive SweepControl (K a q : ℕ) where
  | mark
  | seekEnd
  | take
  | bring (letter : Fin a)
  | append (letter : Fin a)
  | back
  | start (state : Fin q)
  | seek (purpose : Purpose K a q)
  | read (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | returnPeek (k : Fin K) (state : Fin q) (tops : Fin K → Option (Fin a))
  | erase (k : Fin K) (state : Fin q)
  | ret (state : Fin q)
  deriving Fintype, DecidableEq

abbrev Control := SweepControl M.count M.alphabet M.states
abbrev Purpose' := Purpose M.count M.alphabet M.states
abbrev TapeSymbol := TypedTape.Symbol M.TrackSymbol
abbrev TapeState := TypedTape.State M.Control
abbrev TapeConfig := TypedTape.Config M.Control M.TrackSymbol

 def symbolTracks (_M : Machine) : _M.TapeSymbol → _M.Tops
  | .inl _ => fun _ => none
  | .inr x => x.2

 def symbolBottom (_M : Machine) : _M.TapeSymbol → Bool
  | .inl _ => false
  | .inr x => x.1

 def trackSymbol (bottom : Bool) (v : M.Tops) : M.TapeSymbol :=
  if bottom=false ∧ v=fun _ => none then .inl 0 else .inr (bottom,v)

@[simp] theorem tracks_trackSymbol (b : Bool) (v : M.Tops) :
    M.symbolTracks (M.trackSymbol b v)=v := by
  unfold trackSymbol
  split_ifs with h
  · simp only [symbolTracks,h.2]
  · rfl

@[simp] theorem bottom_trackSymbol (b : Bool) (v : M.Tops) :
    M.symbolBottom (M.trackSymbol b v)=b := by
  unfold trackSymbol
  split_ifs with h
  · exact h.1.symm
  · rfl

 def purposeStack (_M : Machine) : _M.Purpose' → Fin _M.count
  | .peek k _ _ => k
  | .push k _ _ => k
  | .pop k _ => k

 def dispatch (a : Command M.count M.alphabet M.states) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move := match a with
  | .next q => (.inr (.start q),s,.stay)
  | .push k x q => (.inr (.seek (.push k x q)),s,.left)
  | .pop k q => (.inr (.seek (.pop k q)),s,.left)
  | .halt b => (.inl (if b then 1 else 2),s,.stay)

 def finishPeek (k : Fin M.count) (q : Fin M.states) (v : M.Tops) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move :=
  if h : k.val+1<M.count then (.inr (.seek (.peek ⟨k.val+1,h⟩ q v)),s,.left)
  else M.dispatch (M.transition q v) s

 def sweepTransition (p : M.TapeState) (s : M.TapeSymbol) :
    M.TapeState × M.TapeSymbol × Move := match p with
  | .inl i => if i.val=0 then (.inr .mark,s,.left) else (.inl i,s,.stay)
  | .inr .mark => (.inr .seekEnd,M.trackSymbol true (fun _ => none),.right)
  | .inr .seekEnd => if s=.inl 1 ∨ s=.inl 2 then (.inr .seekEnd,s,.right)
      else (.inr .take,s,.left)
  | .inr .take => if M.symbolBottom s then (.inr (.start M.initial),s,.stay)
      else (.inr (.bring (M.inputLetter (s=.inl 2))),.inl 0,.left)
  | .inr (.bring x) => if M.symbolBottom s then (.inr (.append x),s,.left)
      else (.inr (.bring x),s,.left)
  | .inr (.append x) => if (M.symbolTracks s ⟨0,M.count_pos⟩).isSome then
      (.inr (.append x),s,.left)
      else (.inr .back,M.trackSymbol (M.symbolBottom s)
        (Function.update (M.symbolTracks s) ⟨0,M.count_pos⟩ (some x)),.right)
  | .inr .back => if M.symbolBottom s then (.inr .seekEnd,s,.right)
      else (.inr .back,s,.right)
  | .inr (.start q) => (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none))),s,.left)
  | .inr (.seek purpose) => if (M.symbolTracks s (M.purposeStack purpose)).isSome then
      (.inr (.seek purpose),s,.left)
      else match purpose with
      | .peek k q v => (.inr (.read k q v),s,.right)
      | .push k x q => (.inr (.ret q),M.trackSymbol (M.symbolBottom s)
          (Function.update (M.symbolTracks s) k (some x)),.right)
      | .pop k q => (.inr (.erase k q),s,.right)
  | .inr (.read k q v) => let v' := Function.update v k (M.symbolTracks s k)
      (.inr (.returnPeek k q v'),s,.stay)
  | .inr (.returnPeek k q v) => if M.symbolBottom s then M.finishPeek k q v s
      else (.inr (.returnPeek k q v),s,.right)
  | .inr (.erase k q) => if M.symbolBottom s then (.inr (.start q),s,.stay)
      else (.inr (.ret q),M.trackSymbol (M.symbolBottom s)
        (Function.update (M.symbolTracks s) k none),.right)
  | .inr (.ret q) => if M.symbolBottom s then (.inr (.start q),s,.stay)
      else (.inr (.ret q),s,.right)

 def sweep : TypedTape.Machine M.Control M.TrackSymbol := ⟨M.sweepTransition⟩

 def stackCell (_M : Machine) (s : List (Fin _M.alphabet)) (i : ℕ) : Option (Fin _M.alphabet) :=
  s.reverse[i]?

 def storageTracks (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) : M.Tops :=
  if z < -1 then fun k => M.stackCell (s k) (-z-2).toNat else fun _ => none

 def storage (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) : M.TapeSymbol :=
  M.trackSymbol (decide (z=-1)) (M.storageTracks s z)

@[simp] theorem storage_bottom (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) :
    M.symbolBottom (M.storage s z)=decide (z=-1) := by simp [storage]

@[simp] theorem storage_tracks (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) :
    M.symbolTracks (M.storage s z)=M.storageTracks s z := by simp [storage]

@[simp] theorem storage_origin (s : Fin M.count → List (Fin M.alphabet)) :
    M.storage s (-1)=M.trackSymbol true (fun _ => none) := by
  simp [storage,storageTracks]

@[simp] theorem storageTracks_origin (s : Fin M.count → List (Fin M.alphabet)) :
    M.storageTracks s (-1)=(fun _ => none) := by simp [storageTracks]

@[simp] theorem storageTracks_index (s : Fin M.count → List (Fin M.alphabet)) (i : ℕ) :
    M.storageTracks s (-(i:ℤ)-2)= fun k => M.stackCell (s k) i := by
  have hi : -(i:ℤ)-2< -1 := by omega
  have he : (-(-(i:ℤ)-2)-2).toNat=i := by omega
  simp only [storageTracks,ite_eq_left hi,he]

 theorem stackCell_push (s : List (Fin M.alphabet)) (x : Fin M.alphabet) (i : ℕ) :
    M.stackCell (x::s) i = if i=s.length then some x else M.stackCell s i := by
  simp only [stackCell,List.reverse_cons,List.getElem?_append,List.length_reverse]
  by_cases h : i<s.length
  · rw [ite_eq_left h,ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    by_cases he : i=s.length
    · simp [he]
    · have hi : s.length ≤ i := by omega
      have hx : i-s.length ≠ 0 := by omega
      rw [ite_eq_right he]
      rw [List.getElem?_eq_none (l := [x]) (by simp only [List.length_singleton]; omega)]
      rw [List.getElem?_eq_none (l := s.reverse) (by simpa using hi)]

 theorem stackCell_pop (s : List (Fin M.alphabet)) (i : ℕ) :
    M.stackCell s.tail i = if i+1=s.length then none else M.stackCell s i := by
  simp only [stackCell,← List.dropLast_reverse,List.getElem?_dropLast,List.length_reverse]
  by_cases h : i+1<s.length
  · rw [ite_eq_left (show i<s.length-1 by omega),ite_eq_right (show i+1≠s.length by omega)]
  · rw [ite_eq_right (show ¬i<s.length-1 by omega)]
    by_cases he : i+1=s.length
    · rw [ite_eq_left he]
    · rw [ite_eq_right he,List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]

 theorem stackCell_none (s : List (Fin M.alphabet)) : M.stackCell s s.length=none := by
  exact List.getElem?_eq_none (by simp)

 theorem stackCell_some (s : List (Fin M.alphabet)) (i : ℕ) (hi : i<s.length) :
    (M.stackCell s i).isSome=true := by
  rw [stackCell,List.getElem?_eq_getElem (by simpa using hi)]
  rfl

 theorem stackCell_last (s : List (Fin M.alphabet)) :
    M.stackCell s (s.length-1) = s.head? := by
  cases s with
  | nil => rfl
  | cons x xs =>
    simp only [List.length_cons,Nat.add_sub_cancel,M.stackCell_push,ite_true,List.head?_cons]

 def located (_M : Machine) (p : _M.TapeState) (z : ℤ) (tape : ℤ → _M.TapeSymbol) : _M.TapeConfig :=
  ⟨p,z,tape⟩

 def sweepEmbed (C : M.Config) : M.TapeConfig :=
  M.located (match C.state with | .inl b => .inl (if b then 1 else 2) | .inr q => .inr (.start q))
    (-1) (M.storage C.stack)

 theorem storage_change (s s' : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (i : ℕ) (x : Option (Fin M.alphabet))
    (hj : ∀ j ≠ k,s' j=s j)
    (hk : ∀ u,M.stackCell (s' k) u=if u=i then x else M.stackCell (s k) u) :
    M.storage s'=Function.update (M.storage s) (-(i:ℤ)-2)
      (M.trackSymbol false (Function.update (M.storageTracks s (-(i:ℤ)-2)) k x)) := by
  funext z
  by_cases hz : z= -(i:ℤ)-2
  · subst z
    rw [Function.update_self,storage]
    have he : decide (-(i:ℤ)-2= -1)=false := by simp; omega
    rw [he,M.storageTracks_index,M.storageTracks_index]
    congr 1
    funext j
    by_cases h : j=k
    · subst j; simp only [Function.update_self,hk,ite_true]
    · simp only [Function.update_of_ne h,hj j h]
  · rw [Function.update_of_ne hz,storage,storage]
    congr 1
    unfold storageTracks
    split_ifs with h
    · funext j
      by_cases he : j=k
      · subst j
        rw [hk,ite_eq_right (by omega)]
      · rw [hj j he]
    · rfl

 theorem storage_push (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (x : Fin M.alphabet) :
    M.storage (Function.update s k (x::s k))=
      Function.update (M.storage s) (-((s k).length:ℤ)-2)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x))) := by
  apply M.storage_change s _ k (s k).length (some x)
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i; rw [Function.update_self,M.stackCell_push]

 theorem storage_pop (s : Fin M.count → List (Fin M.alphabet))
    (k : Fin M.count) (hk : 0<(s k).length) :
    M.storage (Function.update s k (s k).tail)=
      Function.update (M.storage s) (-((s k).length:ℤ)-1)
        (M.trackSymbol false (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none)) := by
  have he : -(((s k).length-1:ℕ):ℤ)-2= -((s k).length:ℤ)-1 := by omega
  rw [← he]
  apply M.storage_change s _ k ((s k).length-1) none
  · intro j hj; exact Function.update_of_ne hj _ _
  · intro i
    rw [Function.update_self,M.stackCell_pop]
    have he : (i+1=(s k).length) ↔ (i=(s k).length-1) := by omega
    simp only [he]

 theorem seek_run (purpose : M.Purpose') (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[(s (M.purposeStack purpose)).length]
      (M.located (.inr (.seek purpose)) (-2) (M.storage s))=
      M.located (.inr (.seek purpose)) (-((s (M.purposeStack purpose)).length:ℤ)-2) (M.storage s) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.seek purpose)) (-(i:ℤ)-2) (M.storage s))
  intro i hi
  have ht : M.sweep.transition (.inr (.seek purpose)) (M.storage s (-(i:ℤ)-2))=
      (.inr (.seek purpose),M.storage s (-(i:ℤ)-2),.left) := by
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index]
    rw [M.stackCell_some _ i hi]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem return_run (p : M.Control) (s : Fin M.count → List (Fin M.alphabet))
    (n : ℕ) (h : ∀ z< -1,M.sweep.transition (.inr p) (M.storage s z)=
      (.inr p,M.storage s z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr p) (-1) (M.storage s) := by
  have he : M.located (.inr p) (-1) (M.storage s)=
      M.located (.inr p) ((n:ℤ)-(n:ℤ)-1) (M.storage s) := by simp
  rw [he]
  have hz0 : -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 := by omega
  rw [hz0]
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.storage s))
  intro i hi
  have hz : (i:ℤ)-(n:ℤ)-1< -1 := by omega
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ hz)]
  simp only [Move.displacement,located,Nat.cast_add,Nat.cast_one]
  congr 1
  omega

 theorem storage_top (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    M.storageTracks s (-((s k).length:ℤ)-1) k=(s k).head? := by
  cases he : s k with
  | nil => simp
  | cons x xs =>
    have hz : -((x::xs).length:ℤ)-1= -(xs.length:ℤ)-2 := by simp; omega
    rw [hz,M.storageTracks_index]
    change M.stackCell (s k) xs.length=_
    rw [he,M.stackCell_push,ite_eq_left rfl]
    rfl

 theorem peek_run (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.peek k q v))) (-2) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?))) (-1) (M.storage s) := by
  have h0 := M.seek_run (.peek k q v) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.peek k q v))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.peek k q v)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.read k q v),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 : M.sweep.step^[1]
      (M.located (.inr (.read k q v)) (-((s k).length:ℤ)-1) (M.storage s))=
      M.located (.inr (.returnPeek k q (Function.update v k (s k).head?)))
        (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.read k q v))
        (M.storage s (-((s k).length:ℤ)-1))=
        (.inr (.returnPeek k q (Function.update v k (s k).head?)),
          M.storage s (-((s k).length:ℤ)-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_tracks,M.storage_top]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    simp only [Move.displacement,add_zero,located]
  have h3 := M.return_run (.returnPeek k q (Function.update v k (s k).head?)) s (s k).length
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
  rw [show (s k).length+1+1+(s k).length=2*(s k).length+2 by omega] at h
  exact h

 def partialTops (s : Fin M.count → List (Fin M.alphabet)) (i : ℕ) : M.Tops :=
  fun k => if k.val < i then (s k).head? else none

 def topTuple (_M : Machine) (s : Fin _M.count → List (Fin _M.alphabet)) : _M.Tops :=
  fun k => (s k).head?

 theorem partialTops_update (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count) :
    Function.update (M.partialTops s k.val) k (s k).head?=M.partialTops s (k.val+1) := by
  funext j
  by_cases h : j=k
  · subst j; simp [partialTops]
  · rw [Function.update_of_ne h]
    unfold partialTops
    have hn : j.val≠k.val := fun he => h (Fin.ext he)
    have he : (j.val<k.val) ↔ (j.val<k.val+1) := by omega
    simp only [he]

 theorem partialTops_all (s : Fin M.count → List (Fin M.alphabet)) :
    M.partialTops s M.count=M.topTuple s := by
  funext k
  exact ite_eq_left k.isLt

 theorem finish_next (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v))) (-2) (M.storage s) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      (.inr (.seek (.peek ⟨k.val+1,hk⟩ q v)),M.storage s (-1),.left) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_left hk]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  rfl

 def dispatchLocation (a : Command M.count M.alphabet M.states)
    (s : Fin M.count → List (Fin M.alphabet)) : M.TapeConfig := match a with
  | .next q => M.located (.inr (.start q)) (-1) (M.storage s)
  | .push k x q => M.located (.inr (.seek (.push k x q))) (-2) (M.storage s)
  | .pop k q => M.located (.inr (.seek (.pop k q))) (-2) (M.storage s)
  | .halt b => M.located (.inl (if b then 1 else 2)) (-1) (M.storage s)

 theorem finish_last (k : Fin M.count) (q : Fin M.states) (v : M.Tops)
    (s : Fin M.count → List (Fin M.alphabet)) (hk : ¬k.val+1<M.count) :
    M.sweep.step^[1] (M.located (.inr (.returnPeek k q v)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q v) s := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr (.returnPeek k q v)) (M.storage s (-1))=
      M.dispatch (M.transition q v) (M.storage s (-1)) := by
    simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true,finishPeek,dite_eq_right hk]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht]
  cases M.transition q v <;> simp only [Function.update_eq_self] <;> rfl

 theorem scan_prefix (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) (i : ℕ) (hi : i<M.count) :
    ∃ t ≤ i*(2*L+3), M.sweep.step^[t]
      (M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨i,hi⟩ q (M.partialTops s i)))) (-2) (M.storage s) := by
  induction i with
  | zero =>
    refine ⟨0,by omega,?_⟩
    have hh : M.partialTops s 0=(fun _ => none) := by
      funext k; exact ite_eq_right (Nat.not_lt_zero _)
    rw [hh]
    rfl
  | succ i ih =>
    have hii : i<M.count := by omega
    obtain ⟨t,ht,hp⟩ := ih hii
    let k : Fin M.count := ⟨i,hii⟩
    have h1 := M.peek_run k q (M.partialTops s i) s
    rw [show i=k.val from rfl,M.partialTops_update] at h1
    have h2 := M.finish_next k q (M.partialTops s (i+1)) s hi
    refine ⟨t+(2*(s k).length+2)+1,?_,M.sweep.concat (M.sweep.concat hp h1) h2⟩
    have := hL k
    nlinarith

 theorem collect_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 1+M.count*(2*L+3),M.sweep.step^[t]
      (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.dispatchLocation (M.transition q (M.topTuple s)) s := by
  have hi : M.count-1<M.count := by have := M.count_pos; omega
  let k : Fin M.count := ⟨M.count-1,hi⟩
  have he : k.val+1=M.count := by have := M.count_pos; dsimp [k]; omega
  obtain ⟨t,ht,hp⟩ := M.scan_prefix s q L hL (M.count-1) hi
  have h0 : M.sweep.step^[1] (M.located (.inr (.start q)) (-1) (M.storage s))=
      M.located (.inr (.seek (.peek ⟨0,M.count_pos⟩ q (fun _ => none)))) (-2) (M.storage s) := by
    change M.sweep.step _=_
    rw [located,M.sweep.step_keep _ _ _ _ _ (by rfl)]
    rfl
  have h1 := M.peek_run k q (M.partialTops s k.val) s
  rw [M.partialTops_update,he,M.partialTops_all] at h1
  have h2 := M.finish_last k q (M.topTuple s) s (by omega)
  refine ⟨1+t+(2*(s k).length+2)+1,?_,
    M.sweep.concat (M.sweep.concat (M.sweep.concat h0 hp) h1) h2⟩
  have hlen := hL k
  have hkval : M.count-1+1=M.count := he
  nlinarith

 theorem ret_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr (.ret q)) (-(n:ℤ)-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
  have h0 := M.return_run (.ret q) s n
    (by intro z hz; simp [sweep,sweepTransition,M.storage_bottom,show z≠ -1 by omega])
  have h1 : M.sweep.step^[1] (M.located (.inr (.ret q)) (-1) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.ret q)) (M.storage s (-1))=
        (.inr (.start q),M.storage s (-1),.stay) := by
      simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem push_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (x : Fin M.alphabet) (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.push k x q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (x::s k))) := by
  have h0 := M.seek_run (.push k x q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.push k x q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.ret q)) (-((s k).length:ℤ)-1)
        (M.storage (Function.update s k (x::s k))) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.push k x q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.ret q),M.trackSymbol false
          (Function.update (M.storageTracks s (-((s k).length:ℤ)-2)) k (some x)),.right) := by
      have hz : -((s k).length:ℤ)-2≠ -1 := by omega
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,
        M.stackCell_none,Option.isSome_none,Bool.false_eq_true,ite_false,M.storage_bottom,
        decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  have h2 := M.ret_run (Function.update s k (x::s k)) q (s k).length
  have h := M.sweep.concat (M.sweep.concat h0 h1) h2
  rw [show (s k).length+1+((s k).length+1)=2*(s k).length+2 by omega] at h
  exact h

 theorem pop_run (s : Fin M.count → List (Fin M.alphabet)) (k : Fin M.count)
    (q : Fin M.states) :
    M.sweep.step^[2*(s k).length+2]
      (M.located (.inr (.seek (.pop k q))) (-2) (M.storage s))=
      M.located (.inr (.start q)) (-1) (M.storage (Function.update s k (s k).tail)) := by
  have h0 := M.seek_run (.pop k q) s
  simp only [purposeStack] at h0
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.seek (.pop k q))) (-((s k).length:ℤ)-2) (M.storage s))=
      M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.seek (.pop k q)))
        (M.storage s (-((s k).length:ℤ)-2))=
        (.inr (.erase k q),M.storage s (-((s k).length:ℤ)-2),.right) := by
      simp only [sweep,sweepTransition,purposeStack,M.storage_tracks,M.storageTracks_index,M.stackCell_none]
      rfl
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  by_cases hk : (s k).length=0
  · have hs : s k=[] := List.eq_nil_of_length_eq_zero hk
    have hu : Function.update s k (s k).tail=s := by rw [hs,List.tail_nil,← hs,Function.update_eq_self]
    have h2 : M.sweep.step^[1] (M.located (.inr (.erase k q)) (-1) (M.storage s))=
        M.located (.inr (.start q)) (-1) (M.storage s) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q)) (M.storage s (-1))=
          (.inr (.start q),M.storage s (-1),.stay) := by
        simp only [sweep,sweepTransition,M.storage_bottom,decide_true,ite_true]
      rw [located,M.sweep.step_keep _ _ _ _ _ ht]
      rfl
    simp only [hk,Nat.cast_zero,neg_zero,zero_sub] at h1
    rw [hk,hu]
    simpa only [zero_mul,zero_add] using M.sweep.concat h1 h2
  · have hpos : 0<(s k).length := by omega
    have h2 : M.sweep.step^[1]
        (M.located (.inr (.erase k q)) (-((s k).length:ℤ)-1) (M.storage s))=
        M.located (.inr (.ret q)) (-(((s k).length-1:ℕ):ℤ)-1)
          (M.storage (Function.update s k (s k).tail)) := by
      change M.sweep.step _=_
      have ht : M.sweep.transition (.inr (.erase k q))
          (M.storage s (-((s k).length:ℤ)-1))=
          (.inr (.ret q),M.trackSymbol false
            (Function.update (M.storageTracks s (-((s k).length:ℤ)-1)) k none),.right) := by
        have hz : -((s k).length:ℤ)-1≠ -1 := by omega
        simp only [sweep,sweepTransition,M.storage_tracks,M.storage_bottom,
          decide_eq_false_iff_not.mpr hz,Bool.false_eq_true,ite_false]
      rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.storage_pop s k hpos]
      unfold located
      congr 1
      simp only [Move.displacement]
      omega
    have h3 := M.ret_run (Function.update s k (s k).tail) q ((s k).length-1)
    have h := M.sweep.concat (M.sweep.concat (M.sweep.concat h0 h1) h2) h3
    rw [show (s k).length+1+1+((s k).length-1+1)=2*(s k).length+2 by omega] at h
    exact h

 theorem dispatch_run (s : Fin M.count → List (Fin M.alphabet)) (q : Fin M.states)
    (a : Command M.count M.alphabet M.states) (L : ℕ) (hL : ∀ k,(s k).length ≤ L) :
    ∃ t ≤ 2*L+3,M.sweep.step^[t] (M.dispatchLocation a s)=
      M.sweepEmbed (M.perform ⟨.inr q,s⟩ a) := by
  cases a with
  | next q' => exact ⟨0,by omega,rfl⟩
  | halt b => exact ⟨0,by omega,rfl⟩
  | push k x q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.push_run s k x q'⟩
  | pop k q' => exact ⟨2*(s k).length+2,by have := hL k; omega,M.pop_run s k q'⟩

 theorem sweep_simulate_step (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∃ t ≤ 4*(M.count+1)*(L+1),M.sweep.step^[t] (M.sweepEmbed C)=M.sweepEmbed (M.step C) := by
  obtain ⟨p,s⟩ := C
  cases p with
  | inl b => exact ⟨0,by positivity,rfl⟩
  | inr q =>
    obtain ⟨t,ht,hc⟩ := M.collect_run s q L hL
    obtain ⟨u,hu,ha⟩ := M.dispatch_run s q (M.transition q (M.topTuple s)) L hL
    refine ⟨t+u,?_,M.sweep.concat hc ha⟩
    nlinarith

end Machine
end WLTime.StackMachine

end OAI
