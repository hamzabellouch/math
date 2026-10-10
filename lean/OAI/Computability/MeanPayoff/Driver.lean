import OAI.Computability.MeanPayoff.SizeBounds

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace Code
variable {α β : Type} [Encoding α] [Encoding β]
noncomputable def select (tag : Code α Count) (cases : List (Code α β)) (fallback : Code α β) : Code α β :=
  match cases with
  | [] => fallback
  | c::cs => Code.branch (tag ≫ₚ empty) c (select (tag ≫ₚ tail) cs fallback)
theorem select_eval (tag : Code α Count) (cases : List (Code α β)) (fallback : Code α β) (x : α) :
    select tag cases fallback x=(cases.getD (tag x).length fallback) x := by
  induction cases generalizing tag with
  | nil => simp [select,List.getD]
  | cons c cs ih =>
    simp only [select,branch_eval,comp_eval,empty_eval,ih]
    cases h : tag x with
    | nil => simp []
    | cons u us => simp [tail_eval,List.getD]
end Code

namespace DetDriver
open DetRaw
abbrev Frame := Count × Input × List W × List W
abbrev State := (Bool × Input × List Bool) × List Frame
abbrev Env := RawBasic.Arena × State

def zeroInput : Input := ((Array.zero,[]), (Array.zero,[]), (Array.zero,[]))
def zeroFrame : Frame := ([],zeroInput,[],[])
def call (x : Input) (ks : List Frame) : State := ((false,x,[]),ks)
def ret (ls : List Bool) (ks : List Frame) : State := ((true,zeroInput,ls),ks)
def frame (tag : ℕ) (x : Input) (kd k : List W) : Frame := (List.replicate tag (),x,kd,k)

noncomputable def state : Code Env State := snd
noncomputable def arena : Code Env RawBasic.Arena := fst
noncomputable def returning : Code Env Bool := state ≫ₚ fst ≫ₚ fst
noncomputable def input : Code Env Input := state ≫ₚ fst ≫ₚ snd ≫ₚ fst
noncomputable def labels : Code Env (List Bool) := state ≫ₚ fst ≫ₚ snd ≫ₚ snd
noncomputable def stack : Code Env (List Frame) := state ≫ₚ snd
noncomputable def top : Code Env Frame := stack ≫ₚ head zeroFrame
noncomputable def rest : Code Env (List Frame) := stack ≫ₚ tail
noncomputable def tag : Code Env Count := top ≫ₚ fst
noncomputable def parent : Code Env Input := top ≫ₚ snd ≫ₚ fst
noncomputable def kd : Code Env (List W) := top ≫ₚ snd ≫ₚ snd ≫ₚ fst
noncomputable def pivot : Code Env (List W) := top ≫ₚ snd ≫ₚ snd ≫ₚ snd
noncomputable def frameCode {α : Type} [Encoding α] (t : ℕ) (x : Code α Input)
    (kd k : Code α (List W)) : Code α Frame := const (List.replicate t ()) ⋏ₚ x ⋏ₚ kd ⋏ₚ k
noncomputable def callCode {α : Type} [Encoding α] (x : Code α Input) (s : Code α (List Frame)) : Code α State :=
  (const false ⋏ₚ x ⋏ₚ const []) ⋏ₚ s
noncomputable def retCode {α : Type} [Encoding α] (ls : Code α (List Bool)) (s : Code α (List Frame)) : Code α State :=
  (const true ⋏ₚ const zeroInput ⋏ₚ ls) ⋏ₚ s
noncomputable def pushCode {α : Type} [Encoding α] (f : Code α Frame) (s : Code α (List Frame)) : Code α (List Frame) :=
  (f ⋏ₚ s) ≫ₚ cons

noncomputable def initialPivot : Code Env (List W) := input ≫ₚ center
noncomputable def enter : Code Env State :=
  Code.branch (input ≫ₚ base) (retCode (input ≫ₚ baseLabels) stack)
    (Code.branch (input ≫ₚ small) (retCode ((arena ⋏ₚ input) ≫ₚ DetRaw.basic) stack)
      (callCode ((input ⋏ₚ initialPivot) ≫ₚ child false)
        (pushCode (frameCode 0 input (const []) initialPivot) stack)))
noncomputable def updated (u : Bool) : Code Env (List W) :=
  (parent ⋏ₚ pivot ⋏ₚ labels) ≫ₚ (if u then up else down)
noncomputable def moving (u : Bool) : Code Env Bool := (updated u ⋏ₚ pivot) ≫ₚ different
noncomputable def again (u : Bool) : Code Env State :=
  callCode ((parent ⋏ₚ updated u) ≫ₚ child u)
    (pushCode (frameCode (if u then 1 else 0) parent kd (updated u)) rest)
noncomputable def downDone : Code Env State :=
  callCode ((parent ⋏ₚ updated false) ≫ₚ child true)
    (pushCode (frameCode 1 parent (updated false) (updated false)) rest)
noncomputable def upDone : Code Env State :=
  callCode ((parent ⋏ₚ updated true) ≫ₚ provisional)
    (pushCode (frameCode 2 parent kd (updated true)) rest)
noncomputable def provisionalDone : Code Env State :=
  callCode ((parent ⋏ₚ labels) ≫ₚ continuation)
    (pushCode (frameCode 3 parent kd pivot) rest)
noncomputable def continuationDone : Code Env State :=
  retCode ((parent ⋏ₚ kd ⋏ₚ pivot ⋏ₚ labels) ≫ₚ finish) rest
noncomputable def resume : Code Env State :=
  select tag [Code.branch (moving false) (again false) downDone,
    Code.branch (moving true) (again true) upDone,provisionalDone,continuationDone] continuationDone
noncomputable def stop : Code Env Bool := (returning ⋏ₚ (stack ≫ₚ empty)) ≫ₚ Code.and
noncomputable def step : Code Env State :=
  Code.branch returning (Code.branch (stack ≫ₚ empty) state resume) enter

@[simp] theorem callCode_eval {α : Type} [Encoding α] (x : Code α Input) (s : Code α (List Frame)) (e : α) :
    callCode x s e=call (x e) (s e) := rfl
@[simp] theorem retCode_eval {α : Type} [Encoding α] (ls : Code α (List Bool)) (s : Code α (List Frame)) (e : α) :
    retCode ls s e=ret (ls e) (s e) := rfl
@[simp] theorem pushCode_eval {α : Type} [Encoding α] (f : Code α Frame) (s : Code α (List Frame)) (e : α) :
    pushCode f s e=f e::s e := rfl
@[simp] theorem frameCode_eval {α : Type} [Encoding α] (t : ℕ) (x : Code α Input)
    (kd k : Code α (List W)) (e : α) : frameCode t x kd k e=frame t (x e) (kd e) (k e) := rfl

@[simp] theorem step_call (ar : RawBasic.Arena) (x : Input) (ks : List Frame) :
    step (ar,call x ks)=
      if base x then ret (baseLabels x) ks
      else if small x then ret (DetRaw.basic (ar,x)) ks
      else call (child false (x,center x)) (frame 0 x [] (center x)::ks) := rfl

@[simp] theorem step_ret_nil (ar : RawBasic.Arena) (ls : List Bool) :
    step (ar,ret ls [])=ret ls [] := rfl

@[simp] theorem step_down (ar : RawBasic.Arena) (x : Input) (ds vs : List W) (ls : List Bool) (ks : List Frame) :
    step (ar,ret ls (frame 0 x ds vs::ks))=
      let us := down (x,vs,ls)
      if different (us,vs) then call (child false (x,us)) (frame 0 x ds us::ks)
      else call (child true (x,us)) (frame 1 x us us::ks) := rfl

@[simp] theorem step_up (ar : RawBasic.Arena) (x : Input) (ds vs : List W) (ls : List Bool) (ks : List Frame) :
    step (ar,ret ls (frame 1 x ds vs::ks))=
      let us := up (x,vs,ls)
      if different (us,vs) then call (child true (x,us)) (frame 1 x ds us::ks)
      else call (provisional (x,us)) (frame 2 x ds us::ks) := rfl

@[simp] theorem step_provisional (ar : RawBasic.Arena) (x : Input) (ds vs : List W) (ls : List Bool) (ks : List Frame) :
    step (ar,ret ls (frame 2 x ds vs::ks))=
      call (continuation (x,ls)) (frame 3 x ds vs::ks) := rfl

@[simp] theorem step_continuation (ar : RawBasic.Arena) (x : Input) (ds vs : List W) (ls : List Bool) (ks : List Frame) :
    step (ar,ret ls (frame 3 x ds vs::ks))=ret (finish (x,ds,vs,ls)) ks := rfl

@[simp] theorem stop_call (ar : RawBasic.Arena) (x : Input) (ks : List Frame) : stop (ar,call x ks)=false := rfl
@[simp] theorem stop_ret (ar : RawBasic.Arena) (ls : List Bool) (ks : List Frame) :
    stop (ar,ret ls ks)=ks.isEmpty := by
  simp [stop,Code.and,returning,state,stack,ret]

end DetDriver
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified.DetDriver
open BinaryData DetRaw

structure FrameSmall (n M : ℕ) (f : Frame) : Prop where
  tag : f.1.length≤n
  input : DetRaw.Small n M f.2.1
  down : Array.Small n M f.2.2.1
  pivot : Array.Small n M f.2.2.2

structure Small (n M K : ℕ) (s : State) : Prop where
  input : DetRaw.Small n M s.1.2.1
  labels : s.1.2.2.length≤n
  depth : s.2.length≤K
  frames : ∀ f∈s.2, FrameSmall n M f

theorem FrameSmall.mono {n M N : ℕ} {f : Frame} (h : FrameSmall n M f) (hM : M≤N) : FrameSmall n N f :=
  ⟨h.tag,h.input.mono hM,h.down.mono hM,h.pivot.mono hM⟩

theorem Small.mono {n M K N J : ℕ} {s : State} (h : Small n M K s) (hM : M≤N) (hK : K≤J) : Small n N J s :=
  ⟨h.input.mono hM,h.labels,h.depth.trans hK,fun f hf => (h.frames f hf).mono hM⟩

theorem zero_small (n M : ℕ) : DetRaw.Small n M zeroInput :=
  ⟨Nat.zero_le _,Array.Small.nil _ _,⟨Nat.zero_le _,Array.Small.nil _ _⟩,⟨Nat.zero_le _,Array.Small.nil _ _⟩⟩

theorem frame_small {n M t : ℕ} {x : Input} {ds vs : List W}
    (ht : t≤n) (hx : DetRaw.Small n M x) (hd : Array.Small n M ds) (hv : Array.Small n M vs) :
    FrameSmall n M (frame t x ds vs) := ⟨by simpa only [frame,List.length_replicate] using ht,hx,hd,hv⟩

theorem call_small {n M K : ℕ} {x : Input} {ks : List Frame}
    (hx : DetRaw.Small n M x) (hk : ks.length≤K) (hf : ∀ f∈ks, FrameSmall n M f) :
    Small n M K (call x ks) := ⟨hx,Nat.zero_le _,hk,hf⟩

theorem ret_small {n M K : ℕ} {ls : List Bool} {ks : List Frame}
    (hl : ls.length≤n) (hk : ks.length≤K) (hf : ∀ f∈ks, FrameSmall n M f) :
    Small n M K (ret ls ks) := ⟨zero_small n M,hl,hk,hf⟩

theorem call_push_small {n M K t : ℕ} {y x : Input} {ds vs : List W} {ks : List Frame}
    (hy : DetRaw.Small n M y) (ht : t≤n) (hx : DetRaw.Small n M x)
    (hd : Array.Small n M ds) (hv : Array.Small n M vs)
    (hk : ks.length≤K) (hf : ∀ f∈ks, FrameSmall n M f) :
    Small n M (K+1) (call y (frame t x ds vs::ks)) := by
  apply call_small hy (by simpa only [List.length_cons] using Nat.add_le_add_right hk 1)
  intro f hf'
  rcases List.mem_cons.mp hf' with rfl | hf'
  · exact frame_small ht hx hd hv
  · exact hf f hf'

@[simp] theorem step_forward (ar : RawBasic.Arena) (x : Input) (ls : List Bool) (ks : List Frame) :
    step (ar,((false,x,ls),ks))=step (ar,call x ks) := rfl

@[simp] theorem step_return_push (ar : RawBasic.Arena) (x : Input) (ls : List Bool) (f : Frame) (ks : List Frame) :
    step (ar,((true,x,ls),f::ks))=step (ar,ret ls (f::ks)) := rfl

@[simp] theorem step_return_large (ar : RawBasic.Arena) (x : Input) (ds vs : List W)
    (ls : List Bool) (ks : List Frame) (t : ℕ) :
    step (ar,ret ls (frame (t+3) x ds vs::ks))=ret (finish (x,ds,vs,ls)) ks := by
  cases t <;> rfl

theorem enter_small {n M K : ℕ} {x : Input} {ks : List Frame} (hn : 3≤n)
    (hx : DetRaw.Small n M x) (hk : ks.length≤K) (hf : ∀ f∈ks, FrameSmall n M f)
    (ar : RawBasic.Arena) : Small n (M+100) (K+1) (step (ar,call x ks)) := by
  have hfs : ∀ f∈ks, FrameSmall n (M+100) f := fun f hf' => (hf f hf').mono (by omega)
  rw [step_call]
  split
  · exact ret_small (baseLabels_length hx) (by omega) hfs
  · split
    · exact ret_small (basic_length hx ar) (by omega) hfs
    · have hc := center_small hx
      have hy := child_small (hx.mono (show M≤M+1 by omega)) hc false
      exact call_push_small (hy.mono (by omega)) (by omega) (hx.mono (by omega))
        (Array.Small.nil _ _) (hc.mono (by omega)) hk hfs

theorem resume_small {n M K : ℕ} {x : Input} {ds vs : List W} {ls : List Bool} {ks : List Frame}
    (hn : 3≤n) (hx : DetRaw.Small n M x) (hd : Array.Small n M ds) (hv : Array.Small n M vs)
    (hl : ls.length≤n) (hk : ks.length≤K) (hf : ∀ f∈ks, FrameSmall n M f)
    (ar : RawBasic.Arena) (t : ℕ) : Small n (M+100) (K+1) (step (ar,ret ls (frame t x ds vs::ks))) := by
  have hfs : ∀ f∈ks, FrameSmall n (M+100) f := fun f hf' => (hf f hf').mono (by omega)
  have hxs := hx.mono (show M≤M+100 by omega)
  have hds := hd.mono (show M≤M+100 by omega)
  have hvs := hv.mono (show M≤M+100 by omega)
  cases t with
  | zero =>
    rw [step_down]
    dsimp only
    have hu := down_small hx hv ls hl
    have hux := hx.mono (show M≤M+40 by omega)
    have hud := (child_small hux hu false).mono (show M+40+40≤M+100 by omega)
    have huu := (child_small hux hu true).mono (show M+40+40≤M+100 by omega)
    split
    · exact call_push_small hud (by omega) hxs hds (hu.mono (by omega)) hk hfs
    · exact call_push_small huu (by omega) hxs (hu.mono (by omega)) (hu.mono (by omega)) hk hfs
  | succ t =>
    cases t with
    | zero =>
      rw [step_up]
      dsimp only
      have hu := up_small hx hv ls hl
      have hux := hx.mono (show M≤M+40 by omega)
      have huu := (child_small hux hu true).mono (show M+40+40≤M+100 by omega)
      have hup := (provisional_small hux hu).mono (show M+40+40≤M+100 by omega)
      split
      · exact call_push_small huu (by omega) hxs hds (hu.mono (by omega)) hk hfs
      · exact call_push_small hup (by omega) hxs hds (hu.mono (by omega)) hk hfs
    | succ t =>
      cases t with
      | zero =>
        rw [step_provisional]
        exact call_push_small ((continuation_small hx ls).mono (by omega)) (by omega) hxs hds hvs hk hfs
      | succ t =>
        rw [show t+1+1+1=t+3 by omega,step_return_large]
        exact ret_small (finish_length hd vs ls) (by omega) hfs

theorem step_small {n M K : ℕ} {s : State} (hn : 3≤n) (h : Small n M K s)
    (ar : RawBasic.Arena) : Small n (M+100) (K+1) (step (ar,s)) := by
  rcases s with ⟨⟨mode,x,ls⟩,ks⟩
  cases mode with
  | false =>
    rw [step_forward]
    exact enter_small hn h.input h.depth h.frames ar
  | true =>
    cases ks with
    | nil => exact h.mono (by omega) (by omega)
    | cons f ks =>
      rw [step_return_push]
      have hh := h.frames f (by simp)
      rcases f with ⟨tag,x,ds,vs⟩
      have ht : tag=List.replicate tag.length () := List.eq_replicate_of_mem (by intro a ha; exact Subsingleton.elim _ _)
      have he : (tag,x,ds,vs)=frame tag.length x ds vs := by simp only [frame,←ht]
      rw [he]
      apply resume_small hn hh.input hh.down hh.pivot h.labels (K:=K) (ar:=ar)
      · have hhdepth : ks.length+1≤K := h.depth
        omega
      · intro f hf
        exact h.frames f (List.mem_cons_of_mem _ hf)

end MeanPayoff.TreeDevice.Certified.DetDriver

namespace MeanPayoff.Label

variable {n : ℕ}
theorem gridPivot_injective (A : Fin n → ℤ) {t : ℤ} (ht : 0<t) :
    Function.Injective (gridPivot A t) := by
  intro g h he
  funext i
  have hu := congrFun he i
  dsimp [gridPivot] at hu
  have hc : (g i).val=(h i).val := by
    have ht0 : t≠0 := ne_of_gt ht
    have hv : (1536+(g i).val:ℤ)=(1536+(h i).val:ℤ) := mul_right_cancel₀ ht0 (add_left_cancel hu)
    exact_mod_cast add_left_cancel hv
  exact Fin.ext hc

theorem downRun_fixed (o : Grid n → Fin n → Bool) (g : Grid n)
    (h : gridDown g (o g)=g) : (downRun o g).val.1=g := by
  unfold downRun
  rw [settle.eq_1,dite_eq_left h]

theorem downRun_next (o : Grid n → Fin n → Bool) (g : Grid n)
    (h : gridDown g (o g)≠g) : (downRun o g).val.1=(downRun o (gridDown g (o g))).val.1 := by
  unfold downRun
  rw [settle.eq_1,dite_eq_right h]

theorem upRun_fixed (o : Grid n → Fin n → Bool) (g : Grid n)
    (h : gridUp g (o g)=g) : (upRun o g).val.1=g := by
  unfold upRun
  rw [settle.eq_1,dite_eq_left h]

theorem upRun_next (o : Grid n → Fin n → Bool) (g : Grid n)
    (h : gridUp g (o g)≠g) : (upRun o g).val.1=(upRun o (gridUp g (o g))).val.1 := by
  unfold upRun
  rw [settle.eq_1,dite_eq_right h]

end MeanPayoff.Label

end OAI
