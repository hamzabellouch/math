import OAI.Computability.RandomMean.Chunks

namespace OAI

section
namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take
 theorem quiet_hop_all {K : ℕ} (F : Program K) (p : Fin F.nodes)
    (hq : CoinFree (F.block p)) (s t : Fin K→List Bool) (out out' : List Bool) (N : ℕ)
    (h : ∀ bits, advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,out'⟩)
    (d : Config (compile F)) (he : ∀ b, RegisterBits.step (compile F) (edge F p t out') b=d) :
    ∃ n≤N+1, ∀ bits, advance (compile F) bits (state F p s out) n=d := by
  obtain ⟨n,hn,hh⟩ := quiet_runs F p hq s t out out' N h
  exact ⟨n+1,by omega,fun bits => by rw [advance,hh,he]⟩
 theorem skip_edge (F : Program 5) (p : Fin F.nodes) (hp : F.block p=TreeDevice.skip)
    (s : Fin 5→List Bool) (out : List Bool) (b : Bool) :
    RegisterBits.step (compile F) (state F p s out) b=edge F p s out := by
  have h := step_inner F p ⟨some (F.block p).start,s,out⟩ (by simp) b
  change RegisterBits.step _ (state F p s out) b=_ at h
  rw [h]
  have ht : ∀ q top b, (F.block p).transition q top b=none := by
    rw [hp]; intros; rfl
  simp only [RegisterBits.step,ht]
  rfl
end MeanPayoff.RegisterBits.Flow
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
noncomputable def flow : Flow.Program 5 where
  nodes := 12
  start := 0
  block p := if p=0 then pre else if p=9 then moveCode 1 0 else if p=11 then post else skip
  read p := if p=2 ∨ p=5 ∨ p=6 ∨ p=7 ∨ p=8 then 1 else 0
  next p top bit := match p.val with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.pop,none⟩
    | 2 => some ⟨3,.push false,none⟩
    | 3 => some ⟨if top=some true then 4 else 9,.pop,none⟩
    | 4 => some ⟨5,.pop,none⟩
    | 5 => some ⟨if bit then 6 else 8,.push false,none⟩
    | 6 => some ⟨7,.push false,none⟩
    | 7 => some ⟨8,.push true,none⟩
    | 8 => some ⟨3,.push true,none⟩
    | 9 => some ⟨10,.keep,none⟩
    | 10 => some ⟨11,.push true,none⟩
    | _ => none
noncomputable def program := Flow.compile (flow pre post)
noncomputable def cfg (p : Fin 12) (xs ys : List Bool) (out : List Bool) : Config (program pre post) :=
  Flow.state (flow pre post) p (core xs ys []) out
noncomputable def edge (p : Fin 12) (xs ys : List Bool) (out : List Bool) : Config (program pre post) :=
  Flow.edge (flow pre post) p (core xs ys []) out
 theorem skip_step (p : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (cfg pre post p xs ys out) b=edge pre post p xs ys out := by
  exact Flow.skip_edge (flow pre post) p (by simp [flow,h0,h9,h11]) _ _ _
 theorem boundary (p : Fin 12) (xs ys out : List Bool) (b : Bool) :
    RegisterBits.step (program pre post) (edge pre post p xs ys out) b =
    match (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b with
    | none => ⟨none,core xs ys [],out⟩
    | some a => Flow.state (flow pre post) a.next
        (Function.update (core xs ys []) ((flow pre post).read p)
          (BinaryStack.applyOp a.work ((core xs ys []) ((flow pre post).read p)))) (out++a.emit.toList) :=
  by
    convert Flow.step_boundary (flow pre post) p (core xs ys []) out b using 1 <;> try rfl
    cases (flow pre post).next p ((core xs ys []) ((flow pre post).read p)).head? b <;> rfl
 theorem wait_two (p q : Fin 12) (h0 : p≠0) (h9 : p≠9) (h11 : p≠11)
    (xs ys xs' ys' out : List Bool)
    (h : ∀ b, RegisterBits.step (program pre post) (edge pre post p xs ys out) b=cfg pre post q xs' ys' out)
    (bits : ℕ→Bool) : advance (program pre post) bits (cfg pre post p xs ys out) 2=cfg pre post q xs' ys' out := by
  simp only [advance,skip_step pre post p h0 h9 h11,h]
 theorem loop_one (ns xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (true::false::ns++xs) ys out) 5 =
      edge pre post 5 (ns++xs) ys out := by
  have h3 : ∀ b, RegisterBits.step (program pre post) (edge pre post 3 (true::false::ns++xs) ys out) b=
      cfg pre post 4 (false::ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h4 : ∀ b, RegisterBits.step (program pre post) (edge pre post 4 (false::ns++xs) ys out) b=
      cfg pre post 5 (ns++xs) ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+1)) = _
  rw [advance_add,wait_two pre post 3 4 (by decide) (by decide) (by decide) _ _ _ _ _ h3,
    advance_add,wait_two pre post 4 5 (by decide) (by decide) (by decide) _ _ _ _ _ h4]
  exact skip_step pre post 5 (by decide) (by decide) (by decide) _ _ _ _
 theorem toss_false (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) false=cfg pre post 8 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem toss_true (xs ys out : List Bool) :
    RegisterBits.step (program pre post) (edge pre post 5 xs ys out) true=cfg pre post 6 xs (false::ys) out := by
  rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_false (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 8 xs (false::ys) out) 2=cfg pre post 3 xs (consCode false++ys) out := by
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem cons_true (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 6 xs (false::ys) out) 6=cfg pre post 3 xs (consCode true++ys) out := by
  have h6 : ∀ b, RegisterBits.step (program pre post) (edge pre post 6 xs (false::ys) out) b=
      cfg pre post 7 xs (false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h7 : ∀ b, RegisterBits.step (program pre post) (edge pre post 7 xs (false::false::ys) out) b=
      cfg pre post 8 xs (true::false::false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+(2+2)) = _
  rw [advance_add,wait_two pre post 6 7 (by decide) (by decide) (by decide) _ _ _ _ _ h6,
    advance_add,wait_two pre post 7 8 (by decide) (by decide) (by decide) _ _ _ _ _ h7]
  apply wait_two pre post 8 3 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
end MeanPayoff.RandomTable

end

section
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice RandomTree
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
 theorem loop_zero (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 3 (false::xs) ys out) 2=cfg pre post 9 xs ys out := by
  apply wait_two pre post 3 9 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem pair_up (xs out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 10 xs [] out) 2=cfg pre post 11 (true::xs) [] out := by
  apply wait_two pre post 10 11 (by decide) (by decide) (by decide)
  intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
  funext i; fin_cases i <;> rfl
 theorem moves (x : Data) (xs out : List Bool) :
    ∃ n≤6*treeSize x+4, ∀ bits, advance (program pre post) bits
      (cfg pre post 9 xs (encode x) out) n=cfg pre post 10 (encode x++xs) [] out := by
  apply Flow.quiet_hop_all (flow pre post) (9 : Fin 12) (by intro q top bit; rfl)
    (core xs (encode x) []) (core (encode x++xs) [] []) out out (6*treeSize x+3)
  · intro bits
    change advance (moveCode 1 0) bits ⟨some (moveCode 1 0).start,core xs (encode x) [],out⟩ _ = _
    convert move10 x [] xs [] out bits using 1 ; simp only [List.append_nil] ; rfl
  · intro b
    change RegisterBits.step _ (edge pre post 9 (encode x++xs) [] out) b=_
    rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
 theorem finishes (hq : CoinFree post) (x : Data) (out result : List Bool) (N : ℕ)
    (h : ∀ bits, advance post bits ⟨some post.start,store x [],out⟩ N=⟨none,core [] [] [],result⟩) :
    ∃ n≤N+1, ∀ bits, advance (program pre post) bits (cfg pre post 11 (encode x) [] out) n=
      ⟨none,core [] [] [],result⟩ := by
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (11 : Fin 12) (core [] [] []) result) b=
      ⟨none,core [] [] [],result⟩ := by intro b; exact boundary pre post 11 [] [] result b
  obtain ⟨n,hn,hh⟩ := Flow.quiet_hop_all (flow pre post) (11 : Fin 12) hq
    (store x []) (core [] [] []) out result N h _ he
  refine ⟨n,hn,fun bits => ?_⟩
  simpa only [program,cfg,store,List.append_nil,core] using hh bits
 theorem list_size (bs : List Bool) : treeSize (listData bs)≤4*bs.length+1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change (encode (listData (b::bs))).length≤_
    rw [encode_list_cons,List.length_append,List.length_cons]
    have h := consCode_length_le b
    change (encode (listData bs)).length≤_ at ih
    omega
 theorem sample_trace (hq : CoinFree post) (x : Data) (result : List Bool→List Bool) (U N : ℕ)
    (hp : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ N=
        ⟨none,core [] [] [],result bs⟩) (n : ℕ) (bs : List Bool) (hn : n+bs.length=U) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 3
        (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x) (encode (listData bs)) []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤12*n+24*U+N+15 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc n bs).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  induction n generalizing bs with
  | zero =>
    obtain ⟨a,ha,ea⟩ := moves pre post (listData bs) (encode x) []
    obtain ⟨b,hb,eb⟩ := finishes pre post hq (.pair (listData bs) x) [] (result bs) N (hp bs (by omega))
    let d : Config (program pre post) := ⟨none,core [] [] [],result bs⟩
    let t : RandomTree (Config (program pre post)) := wait (2+a+2+b) (.leaf d)
    refine ⟨t,?_,?_,?_,?_⟩
    · apply Traces.wait _ ?_ (Traces.leaf d)
      intro bits
      change advance _ bits (cfg pre post 3 (false::encode x) (encode (listData bs)) []) (2+a+2+b)=d
      rw [advance_add,advance_add,advance_add,loop_zero,ea,pair_up]
      exact eb _
    · simp [t,All,d]
    · simp only [t,depth_wait,bitDepth,Nat.add_zero]
      have hs := list_size bs
      omega
    · intro f; simp only [t,expect_wait,expect,FairBits.acc]; rfl
  | succ n ih =>
    obtain ⟨l,hl,hal,hdl,hel⟩ := ih (false::bs) (by simp only [List.length_cons]; omega)
    obtain ⟨r,hr,har,hdr,her⟩ := ih (true::bs) (by simp only [List.length_cons]; omega)
    let t := wait 5 (RandomTree.coin (wait 2 l) (wait 6 r))
    refine ⟨t,?_,?_,?_,?_⟩
    · refine Traces.wait (d:=edge pre post 5
          (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))++encode x)
          (encode (listData bs)) []) 5 ?_ ?_
      · intro bits
        exact loop_one pre post (encode (listTree (fun _ : Unit => Data.nil) (List.replicate n ()))) (encode x) (encode (listData bs)) [] bits
      · apply Traces.coin
        · rw [toss_false]
          apply Traces.wait 2 (cons_false pre post _ _ [])
          simpa only [encode_list_cons] using hl
        · rw [toss_true]
          apply Traces.wait 6 (cons_true pre post _ _ [])
          simpa only [encode_list_cons] using hr
    · simp only [t,all_wait,All]; exact ⟨hal,har⟩
    · simp only [t,depth_wait,bitDepth]
      omega
    · intro f
      simp only [t,expect_wait,expect,FairBits.acc,hel,her]
 theorem begin_steps (xs ys out : List Bool) (bits : ℕ→Bool) :
    advance (program pre post) bits (cfg pre post 1 (true::xs) ys out) 4=
      cfg pre post 3 xs (false::ys) out := by
  have h1 : ∀ b, RegisterBits.step (program pre post) (edge pre post 1 (true::xs) ys out) b=
      cfg pre post 2 xs ys out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  have h2 : ∀ b, RegisterBits.step (program pre post) (edge pre post 2 xs ys out) b=
      cfg pre post 3 xs (false::ys) out := by
    intro b; rw [boundary]; apply config_ext <;> (try rfl) <;> (try exact List.append_nil out)
    funext i; fin_cases i <;> rfl
  change advance _ bits _ (2+2)=_
  rw [advance_add,wait_two pre post 1 2 (by decide) (by decide) (by decide) _ _ _ _ _ h1]
  exact wait_two pre post 2 3 (by decide) (by decide) (by decide) _ _ _ _ _ h2 _
 theorem complete_trace (hpre : CoinFree pre) (hpost : CoinFree post)
    (input : List Bool) (x : Data) (result : List Bool→List Bool) (U A B : ℕ)
    (hp : ∀ bits, advance pre bits ⟨some pre.start,core input [] [],[]⟩ A=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x) [],[]⟩)
    (hq : ∀ bs, bs.length=U → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) x) [],[]⟩ B=
        ⟨none,core [] [] [],result bs⟩) :
    ∃ t : RandomTree (Config (program pre post)),
      Traces (program pre post) (cfg pre post 0 input [] []) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤A+36*U+B+20 ∧
      ∀ f : Config (program pre post)→ℚ, t.expect f=(FairBits.acc U []).expect
        (fun cs => f ⟨none,core [] [] [],result cs⟩) := by
  let z := Data.pair (listTree (fun _ : Unit => Data.nil) (List.replicate U ())) x
  have he : ∀ b, RegisterBits.step (Flow.compile (flow pre post))
      (Flow.edge (flow pre post) (0 : Fin 12) (store z []) []) b=
      cfg pre post 1 (encode z) [] [] := by
    intro b
    change RegisterBits.step _ (edge pre post 0 (encode z++[]) [] []) b=_
    rw [List.append_nil,boundary]
    apply config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  obtain ⟨a,ha,ea⟩ := Flow.quiet_hop_all (flow pre post) (0 : Fin 12) hpre
    (core input [] []) (store z []) [] [] A hp _ he
  change ∀ bits, advance (program pre post) bits (cfg pre post 0 input [] []) a=
    cfg pre post 1 (encode z) [] [] at ea
  obtain ⟨t,ht,hal,hd,he⟩ := sample_trace pre post hpost x result U B hq U [] (by simp)
  refine ⟨wait (a+4) t,?_,by simpa only [all_wait] using hal,?_,?_⟩
  · apply Traces.wait _ ?_ ht
    intro bits
    rw [advance_add,ea]
    exact begin_steps pre post _ [] [] _
  · simp only [depth_wait]
    omega
  · intro f; rw [expect_wait,he]
end MeanPayoff.RandomTable

end

section
namespace MeanPayoff.RegisterBits.Sequence5
open BinaryData.Take (advance_add)
variable (P Q : Program 5)
end MeanPayoff.RegisterBits.Sequence5

end

end OAI
