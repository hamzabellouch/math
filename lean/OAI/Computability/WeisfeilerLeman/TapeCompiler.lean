import OAI.Computability.WeisfeilerLeman.Sweep

namespace OAI

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 def inputStacks (w : List Bool) := (M.initialConfig w).stack
 def rawTape (w : List Bool) := (M.sweep.initial w).tape
 def mixed (u v : List Bool) (z : ℤ) : M.TapeSymbol :=
  if 0 ≤ z then M.rawTape u z else M.storage (M.inputStacks v) z

 theorem rawTape_nil (z : ℤ) : M.rawTape [] z=.inl 0 := by
  simp [rawTape,TypedTape.Machine.initial]
 theorem rawTape_bit (w : List Bool) (i : ℕ) (hi : i<w.length) :
    M.rawTape w i=.inl (if w[i] then 2 else 1) := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,hi,and_self,ite_true]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
 theorem rawTape_beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    M.rawTape w i=.inl 0 := by
  simp only [rawTape,TypedTape.Machine.initial,Nat.cast_nonneg,Int.toNat_natCast,true_and,
    ite_eq_right (by omega : ¬i<w.length)]
 theorem mixed_nonneg (u v : List Bool) (z : ℤ) (hz : 0 ≤ z) :
    M.mixed u v z=M.rawTape u z := ite_eq_left hz
 theorem mixed_neg (u v : List Bool) (z : ℤ) (hz : z<0) :
    M.mixed u v z=M.storage (M.inputStacks v) z := ite_eq_right (by omega)
 theorem mixed_bottom (u v : List Bool) (z : ℤ) :
    M.symbolBottom (M.mixed u v z)=decide (z= -1) := by
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz]
    have hh : z≠ -1 := by omega
    simp only [rawTape,TypedTape.Machine.initial,decide_eq_false_iff_not.mpr hh]
    split_ifs <;> rfl
  · rw [M.mixed_neg u v z (by omega),M.storage_bottom]
 theorem inputStacks_zero (v : List Bool) :
    M.inputStacks v ⟨0,M.count_pos⟩=v.map M.inputLetter := by
  simp [inputStacks,initialConfig]
 theorem inputStacks_cons (b : Bool) (v : List Bool) :
    M.inputStacks (b::v)=Function.update (M.inputStacks v) ⟨0,M.count_pos⟩
      (M.inputLetter b::M.inputStacks v ⟨0,M.count_pos⟩) := by
  funext k
  by_cases hk : k=⟨0,M.count_pos⟩
  · subst k; simp only [Function.update_self,M.inputStacks_zero,List.map_cons]
  · have hn : k.val≠0 := fun he => hk (Fin.ext he)
    simp only [Function.update_of_ne hk,inputStacks,initialConfig,hn,ite_false]
 theorem storage_nonneg (s : Fin M.count → List (Fin M.alphabet)) (z : ℤ) (hz : 0 ≤ z) :
    M.storage s z=.inl 0 := by
  have h0 : z≠ -1 := by omega
  have h1 : ¬z< -1 := by omega
  simp only [storage,decide_eq_false_iff_not.mpr h0,storageTracks,ite_eq_right h1,trackSymbol,and_self,ite_true]
 theorem mixed_nil (v : List Bool) : M.mixed [] v=M.storage (M.inputStacks v) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg [] v z hz,M.rawTape_nil,M.storage_nonneg _ z hz]
  · exact M.mixed_neg [] v z (by omega)
 theorem rawTape_erase (u : List Bool) (b : Bool) :
    M.rawTape u=Function.update (M.rawTape (u++[b])) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases he : z=(u.length:ℤ)
  · subst z; rw [Function.update_self,M.rawTape_beyond u u.length (by omega)]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · have hzz : z=(z.toNat:ℤ) := by omega
      rw [hzz]
      by_cases hi : z.toNat<u.length
      · rw [M.rawTape_bit u _ hi,M.rawTape_bit (u++[b]) _ (by simp; omega)]
        simp only [List.getElem_append_left hi]
      · rw [M.rawTape_beyond u _ (by omega),M.rawTape_beyond (u++[b]) _ (by simp; omega)]
    · simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]
 theorem mixed_erase (u v : List Bool) (b : Bool) :
    M.mixed u v=Function.update (M.mixed (u++[b]) v) (u.length:ℤ) (.inl 0) := by
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u v z hz,M.rawTape_erase u b]
    by_cases he : z=(u.length:ℤ)
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_nonneg _ _ z hz]
  · have he : z≠(u.length:ℤ) := by omega
    rw [Function.update_of_ne he,M.mixed_neg _ _ z (by omega),M.mixed_neg _ _ z (by omega)]
 theorem mixed_push (u v : List Bool) (b : Bool) :
    M.mixed u (b::v)=Function.update (M.mixed u v) (-(v.length:ℤ)-2)
      (M.trackSymbol false (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
        ⟨0,M.count_pos⟩ (some (M.inputLetter b)))) := by
  have hv : (M.inputStacks v ⟨0,M.count_pos⟩).length=v.length := by
    rw [M.inputStacks_zero,List.length_map]
  rw [M.mixed_neg u v _ (by omega),M.storage_tracks]
  have hh := M.storage_push (M.inputStacks v) ⟨0,M.count_pos⟩ (M.inputLetter b)
  rw [hv,← M.inputStacks_cons] at hh
  funext z
  by_cases hz : 0 ≤ z
  · rw [M.mixed_nonneg u (b::v) z hz,Function.update_of_ne (by omega),M.mixed_nonneg u v z hz]
  · rw [M.mixed_neg u (b::v) z (by omega),hh]
    by_cases he : z= -(v.length:ℤ)-2
    · simp only [he,Function.update_self]
    · rw [Function.update_of_ne he,Function.update_of_ne he,M.mixed_neg u v z (by omega)]

 theorem seekEnd_run (u v : List Bool) :
    M.sweep.step^[u.length] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i => M.located (.inr .seekEnd) (i:ℤ) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (i:ℤ))=
      (.inr .seekEnd,M.mixed u v (i:ℤ),.right) := by
    rw [M.mixed_nonneg u v _ (by omega),M.rawTape_bit u i hi]
    cases u[i] <;> simp [sweep,sweepTransition]
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  simp [located,Move.displacement]

 theorem reverse_path (p : M.Control) (tape : ℤ → M.TapeSymbol) (n : ℕ)
    (h : ∀ i<n,M.sweep.transition (.inr p) (tape (i:ℤ))=(.inr p,tape (i:ℤ),.left)) :
    M.sweep.step^[n] (M.located (.inr p) ((n:ℤ)-1) tape)=M.located (.inr p) (-1) tape := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((n:ℤ)-(i:ℤ)-1) tape)
  intro i hi
  have hz : (n:ℤ)-(i:ℤ)-1= ((n-i-1:ℕ):ℤ) := by omega
  have ht := h (n-i-1) (by omega)
  rw [← hz] at ht
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem mixed_return (p : M.Control) (u v : List Bool) (n : ℕ)
    (h : ∀ z< -1,M.sweep.transition (.inr p) (M.mixed u v z)=
      (.inr p,M.mixed u v z,.right)) :
    M.sweep.step^[n] (M.located (.inr p) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr p) (-1) (M.mixed u v) := by
  have he : (-1:ℤ)=(n:ℤ)-(n:ℤ)-1 := by omega
  rw [he]
  rw [show -(n:ℤ)-1=(0:ℤ)-(n:ℤ)-1 by omega]
  apply M.sweep.path_iterate (fun i => M.located (.inr p) ((i:ℤ)-(n:ℤ)-1) (M.mixed u v))
  intro i hi
  rw [located,M.sweep.step_keep _ _ _ _ _ (h _ (by omega))]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem append_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length] (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v) := by
  apply M.sweep.path_iterate (fun i =>
    M.located (.inr (.append (M.inputLetter b))) (-(i:ℤ)-2) (M.mixed u v))
  intro i hi
  have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(i:ℤ)-2))=
      (.inr (.append (M.inputLetter b)),M.mixed u v (-(i:ℤ)-2),.left) := by
    rw [M.mixed_neg u v _ (by omega)]
    simp only [sweep,sweepTransition,M.storage_tracks,M.storageTracks_index,M.inputStacks_zero]
    rw [M.stackCell_some _ i (by simpa using hi)]
    rfl
  rw [located,M.sweep.step_keep _ _ _ _ _ ht]
  unfold located
  congr 1
  simp only [Move.displacement,Nat.cast_add,Nat.cast_one]
  omega

 theorem seekEnd_finish (u v : List Bool) :
    M.sweep.step^[u.length+1] (M.located (.inr .seekEnd) 0 (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
  have h1 : M.sweep.step^[1] (M.located (.inr .seekEnd) (u.length:ℤ) (M.mixed u v))=
      M.located (.inr .take) ((u.length:ℤ)-1) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .seekEnd) (M.mixed u v (u.length:ℤ))=
        (.inr .take,M.mixed u v (u.length:ℤ),.left) := by
      rw [M.mixed_nonneg u v _ (by omega),M.rawTape_beyond u u.length (by omega)]
      simp [sweep,sweepTransition]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat (M.seekEnd_run u v) h1

 theorem take_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[1] (M.located (.inr .take) (u.length:ℤ) (M.mixed (u++[b]) v))=
      M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v) := by
  change M.sweep.step _=_
  have ht : M.sweep.transition (.inr .take) (M.mixed (u++[b]) v (u.length:ℤ))=
      (.inr (.bring (M.inputLetter b)),.inl 0,.left) := by
    have hb : M.mixed (u++[b]) v (u.length:ℤ)=.inl (if b then 2 else 1) := by
      rw [M.mixed_nonneg _ _ _ (by omega),M.rawTape_bit _ _ (by simp)]
      simp only [List.getElem_append_right (by omega : u.length ≤ u.length),Nat.sub_self,List.getElem_cons_zero]
    rw [hb]
    cases b <;> simp [sweep,sweepTransition,symbolBottom,inputLetter]
  rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_erase]
  rfl

 theorem bring_run (u v : List Bool) (b : Bool) :
    M.sweep.step^[u.length+1]
      (M.located (.inr (.bring (M.inputLetter b))) ((u.length:ℤ)-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
  have h0 := M.reverse_path (.bring (M.inputLetter b)) (M.mixed u v) u.length (by
    intro i hi
    have hz : (i:ℤ)≠ -1 := by omega
    simp only [sweep,sweepTransition,M.mixed_bottom,decide_eq_false_iff_not.mpr hz,
      Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.bring (M.inputLetter b))) (-1) (M.mixed u v))=
      M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr (.bring (M.inputLetter b))) (M.mixed u v (-1))=
        (.inr (.append (M.inputLetter b)),M.mixed u v (-1),.left) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem append_finish (u v : List Bool) (b : Bool) :
    M.sweep.step^[v.length+1]
      (M.located (.inr (.append (M.inputLetter b))) (-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
  have h1 : M.sweep.step^[1]
      (M.located (.inr (.append (M.inputLetter b))) (-(v.length:ℤ)-2) (M.mixed u v))=
      M.located (.inr .back) (-(v.length:ℤ)-1) (M.mixed u (b::v)) := by
    change M.sweep.step _=_
    have hz : -(v.length:ℤ)-2≠ -1 := by omega
    have ht : M.sweep.transition (.inr (.append (M.inputLetter b))) (M.mixed u v (-(v.length:ℤ)-2))=
        (.inr .back,M.trackSymbol false
          (Function.update (M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)))
            ⟨0,M.count_pos⟩ (some (M.inputLetter b))),.right) := by
      have hv : M.symbolTracks (M.mixed u v (-(v.length:ℤ)-2)) ⟨0,M.count_pos⟩=none := by
        rw [M.mixed_neg u v _ (by omega),M.storage_tracks,M.storageTracks_index]
        change M.stackCell (M.inputStacks v ⟨0,M.count_pos⟩) v.length=none
        rw [M.inputStacks_zero,← List.length_map (f:=M.inputLetter) (as:=v),M.stackCell_none]
      simp only [sweep,sweepTransition,hv,Option.isSome_none,Bool.false_eq_true,ite_false,
        M.mixed_bottom,decide_eq_false_iff_not.mpr hz]
    rw [located,M.sweep.step_live _ _ _ _ _ _ ht,← M.mixed_push]
    unfold located
    congr 1
    simp only [Move.displacement]
    omega
  exact M.sweep.concat (M.append_run u v b) h1

 theorem back_run (u v : List Bool) (n : ℕ) :
    M.sweep.step^[n+1] (M.located (.inr .back) (-(n:ℤ)-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
  have h0 := M.mixed_return .back u v n (by
    intro z hz
    simp only [sweep,sweepTransition,M.mixed_bottom,
      decide_eq_false_iff_not.mpr (by omega : z≠ -1),Bool.false_eq_true,ite_false])
  have h1 : M.sweep.step^[1] (M.located (.inr .back) (-1) (M.mixed u v))=
      M.located (.inr .seekEnd) 0 (M.mixed u v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .back) (M.mixed u v (-1))=
        (.inr .seekEnd,M.mixed u v (-1),.right) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_cycle (u v : List Bool) (b : Bool) :
    M.sweep.step^[2*(u.length+v.length)+6]
      (M.located (.inr .seekEnd) 0 (M.mixed (u++[b]) v))=
      M.located (.inr .seekEnd) 0 (M.mixed u (b::v)) := by
  have h0 := M.seekEnd_finish (u++[b]) v
  have he : (((u++[b]).length:ℤ)-1)=(u.length:ℤ) := by simp
  rw [he] at h0
  have h := M.sweep.concat (M.sweep.concat (M.sweep.concat (M.sweep.concat h0
    (M.take_run u v b)) (M.bring_run u v b)) (M.append_finish u v b)) (M.back_run u (b::v) v.length)
  have hn : (u++[b]).length+1+1+(u.length+1)+(v.length+1)+(v.length+1)=
      2*(u.length+v.length)+6 := by simp only [List.length_append,List.length_singleton]; omega
  rw [hn] at h
  exact h

 theorem init_empty (v : List Bool) :
    M.sweep.step^[2] (M.located (.inr .seekEnd) 0 (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
  have h0 := M.seekEnd_finish [] v
  have h1 : M.sweep.step^[1] (M.located (.inr .take) (-1) (M.mixed [] v))=
      M.sweepEmbed (M.initialConfig v) := by
    change M.sweep.step _=_
    have ht : M.sweep.transition (.inr .take) (M.mixed [] v (-1))=
        (.inr (.start M.initial),M.mixed [] v (-1),.stay) := by
      simp only [sweep,sweepTransition,M.mixed_bottom,decide_true,ite_true]
    rw [located,M.sweep.step_keep _ _ _ _ _ ht,M.mixed_nil]
    rfl
  exact M.sweep.concat h0 h1

 theorem init_process (u v : List Bool) :
    M.sweep.step^[u.length*(2*(u.length+v.length)+4)+2]
      (M.located (.inr .seekEnd) 0 (M.mixed u v))=M.sweepEmbed (M.initialConfig (u++v)) := by
  induction u using List.reverseRecOn generalizing v with
  | nil => simpa only [List.length_nil,zero_mul,zero_add,List.nil_append] using M.init_empty v
  | append_singleton u b ih =>
    have h0 := M.init_cycle u v b
    have h1 := ih (b::v)
    have h := M.sweep.concat h0 h1
    have he : 2*(u.length+v.length)+6+(u.length*(2*(u.length+(b::v).length)+4)+2)=
        (u++[b]).length*(2*((u++[b]).length+v.length)+4)+2 := by
      simp only [List.length_cons,List.length_append,List.length_nil]
      ring
    rw [he] at h
    simpa only [List.append_assoc,List.singleton_append] using h

end Machine
end WLTime.StackMachine

namespace WLTime.StackMachine
namespace Machine
variable (M : Machine)

 theorem storage_empty (z : ℤ) : M.storage (M.inputStacks []) z =
    if z= -1 then M.trackSymbol true (fun _ => none) else .inl 0 := by
  have hs : M.storageTracks (M.inputStacks []) z=(fun _ => none) := by
    unfold storageTracks
    split_ifs
    · funext k
      simp [stackCell,inputStacks,initialConfig]
    · rfl
  simp only [storage,hs]
  by_cases hz : z= -1
  · simp only [hz,decide_true,ite_true]
  · simp only [decide_eq_false_iff_not.mpr hz,ite_eq_right hz,trackSymbol,and_self,ite_true]

 theorem mixed_initial (w : List Bool) :
    M.mixed w []=Function.update (M.rawTape w) (-1) (M.trackSymbol true (fun _ => none)) := by
  funext z
  by_cases he : z= -1
  · subst z
    rw [Function.update_self,M.mixed_neg _ _ _ (by omega),M.storage_origin]
  · rw [Function.update_of_ne he]
    by_cases hz : 0 ≤ z
    · exact M.mixed_nonneg w [] z hz
    · rw [M.mixed_neg _ _ z (by omega),M.storage_empty,ite_eq_right he]
      simp only [rawTape,TypedTape.Machine.initial,hz,false_and,ite_false]

 theorem init_mark (w : List Bool) :
    M.sweep.run w 2=M.located (.inr .seekEnd) 0 (M.mixed w []) := by
  have h0 : M.sweep.step (M.sweep.initial w)=M.located (.inr .mark) (-1) (M.rawTape w) := by
    have hh : ¬M.sweep.halted (.inl 0) := by simp [TypedTape.Machine.halted]
    have ha : M.sweep.action (.inl 0) (M.rawTape w 0)=
        (.inr .mark,M.rawTape w 0,.left) := by
      rw [TypedTape.Machine.action,ite_eq_right hh]
      rfl
    change M.sweep.step ⟨.inl 0,0,M.rawTape w⟩=_
    simp only [TypedTape.Machine.step,ha,Function.update_eq_self]
    rfl
  change M.sweep.step (M.sweep.step (M.sweep.initial w))=_
  rw [h0,located,M.sweep.step_live _ _ _ _ _ _ (by rfl),← M.mixed_initial]
  rfl

 theorem sweep_initial (w : List Bool) :
    ∃ t ≤ 4*(w.length+1)^2,M.sweep.run w t=M.sweepEmbed (M.initialConfig w) := by
  have h := M.sweep.concat (M.init_mark w) (M.init_process w [])
  simp only [List.length_nil,Nat.add_zero,List.append_nil] at h
  refine ⟨2+(w.length*(2*w.length+4)+2),by nlinarith,h⟩

 theorem step_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) :
    ∀ k,((M.step C).stack k).length ≤ L+1 := by
  intro k
  obtain ⟨p,s⟩ := C
  dsimp only at hL
  cases p with
  | inl b => exact (hL k).trans (by omega)
  | inr q =>
    simp only [step]
    cases M.transition q (fun k => (s k).head?) with
    | next q' => exact (hL k).trans (by omega)
    | halt b => exact (hL k).trans (by omega)
    | push j x q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_cons]; exact Nat.add_le_add_right (hL j) 1
      · exact (hL k).trans (by omega)
    | pop j q' =>
      simp only [perform,Function.update_apply]
      split_ifs with hj
      · subst k; simp only [List.length_tail]; have := hL j; omega
      · exact (hL k).trans (by omega)

 theorem iterate_length (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∀ k,((M.step^[t] C).stack k).length ≤ L+t := by
  induction t with
  | zero => simpa only [Function.iterate_zero_apply,Nat.add_zero] using hL
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simpa only [Nat.add_assoc] using M.step_length (M.step^[t] C) (L+t) ih

 theorem sweep_iterate (C : M.Config) (L : ℕ) (hL : ∀ k,(C.stack k).length ≤ L) (t : ℕ) :
    ∃ u ≤ 4*(M.count+1)*t*(L+t+1),
      M.sweep.step^[u] (M.sweepEmbed C)=M.sweepEmbed (M.step^[t] C) := by
  induction t with
  | zero => exact ⟨0,by omega,rfl⟩
  | succ t ih =>
    obtain ⟨u,hu,he⟩ := ih
    obtain ⟨v,hv,hf⟩ := M.sweep_simulate_step (M.step^[t] C) (L+t) (M.iterate_length C L hL t)
    refine ⟨u+v,?_,?_⟩
    · nlinarith
    · rw [Nat.add_comm,Function.iterate_add_apply,he,hf,Function.iterate_succ_apply']

 theorem sweep_run (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,
      M.sweep.run w u=M.sweepEmbed (M.run w t) := by
  obtain ⟨a,ha,he⟩ := M.sweep_initial w
  have hL : ∀ k,((M.initialConfig w).stack k).length ≤ w.length := by
    intro k; simp only [initialConfig]; split_ifs <;> simp
  obtain ⟨b,hb,hf⟩ := M.sweep_iterate (M.initialConfig w) w.length hL t
  refine ⟨a+b,?_,M.sweep.concat he hf⟩
  have hh : (w.length+1)^2 ≤ (w.length+t+1)^2 := by nlinarith
  have htt : t ≤ w.length+t+1 := by omega
  have hmul := Nat.mul_le_mul_right (w.length+t+1) htt
  have hprod := Nat.mul_le_mul_left (4*(M.count+1)) hmul
  nlinarith

noncomputable abbrev oneTape : OneTape := M.sweep.compile

 theorem oneTape_simulate (w : List Bool) (t : ℕ) :
    ∃ u ≤ 8*(M.count+1)*(w.length+t+1)^2,M.oneTape.run OneTape.lineShift (M.oneTape.initial w) u=
      M.sweep.embed (M.sweepEmbed (M.run w t)) := by
  obtain ⟨u,hu,he⟩ := M.sweep_run w t
  refine ⟨u,hu,?_⟩
  rw [← M.sweep.embed_run,he]

 theorem oneTape_correct (w : List Bool) (t : ℕ) (b : Bool)
    (hh : (M.run w t).state=.inl b) :
    M.oneTape.toTM.halts w ∧ M.oneTape.toTM.time w ≤ 8*(M.count+1)*(w.length+t+1)^2 ∧
      (M.oneTape.toTM.accepts w ↔ b=true) := by
  obtain ⟨u,hu,he⟩ := M.oneTape_simulate w t
  have hs : (M.oneTape.toTM.run w u).state.val=if b then 1 else 2 := by
    rw [← M.oneTape.embed_run,he]
    simp only [OneTape.embed,TypedTape.Machine.embed,sweepEmbed,located,hh]
    cases b <;> rfl
  have hx : M.oneTape.toTM.halted (M.oneTape.toTM.run w u) := by
    change (M.oneTape.toTM.run w u).state.val=1 ∨ (M.oneTape.toTM.run w u).state.val=2
    rw [hs]
    cases b <;> simp
  refine ⟨⟨u,hx⟩,(M.oneTape.toTM.time_le_of_halted w hx).trans hu,?_⟩
  rw [M.oneTape.toTM.accepts_iff_at_halt w hx]
  rw [hs]
  cases b <;> simp

end Machine
end WLTime.StackMachine

end OAI
