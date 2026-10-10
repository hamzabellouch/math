import OAI.Computability.MeanPayoff.Comparison

namespace OAI

section

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

def CoinFree {K : ℕ} (P : Program K) : Prop :=
  ∀ q top bit, P.transition q top bit = P.transition q top false

theorem step_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P) (b : Bool) :
    step P c b = step P c false := by
  cases hc : c.control with
  | none => simp [step,hc]
  | some q => simp only [step,hc]; rw [h q _ b]

theorem advance_coinFree {K : ℕ} (P : Program K) (h : CoinFree P) (c : Config P)
    (bits : ℕ → Bool) (n : ℕ) : advance P bits c n = advance P (fun _ => false) c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [advance,ih,step_coinFree P h]

theorem advance_pad {K : ℕ} (P : Program K) (c d : Config P) (bits : ℕ → Bool)
    {n N : ℕ} (hn : n ≤ N) (he : advance P bits c n = d) (hd : d.control = none) :
    advance P bits c N = d := by
  rw [show N = n+(N-n) by omega, advance_add, he, advance_halted P d hd]

theorem Flow.compile_coinFree {K : ℕ} (F : Flow.Program K)
    (hb : ∀ p, CoinFree (F.block p))
    (hn : ∀ p top bit, F.next p top bit = F.next p top false) : CoinFree (Flow.compile F) := by
  intro q top bit
  simp only [Flow.compile]
  cases (Flow.equiv F).symm q with
  | inl z => rcases z with ⟨p,q⟩; dsimp only; rw [hb p q top bit]
  | inr p => dsimp only; rw [hn p top bit]
end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice
open BinaryData RegisterBits
open BinaryData.Take (advance_add)

def store (x : Data) (suffix : List Bool) : Fin 5 → List Bool :=
  ![encode x ++ suffix, [], [], [], []]

def treeSize (x : Data) := (encode x).length

structure Device {α β : Type} (ea : α → Data) (eb : β → Data) (f : α → β) where
  program : RegisterBits.Program 5
  limit : α → ℕ
  quiet : CoinFree program
  correct : ∀ (x : α) (suffix out : List Bool) (bits : ℕ → Bool),
    advance program bits ⟨some program.start,store (ea x) suffix,out⟩ (limit x) =
      ⟨none,store (eb (f x)) suffix,out⟩

def skip : RegisterBits.Program 5 where
  states := 1
  start := 0
  read _ := 0
  transition _ _ _ := none

def identity {α : Type} (ea : α → Data) : Device ea ea id where
  program := skip
  limit _ := 1
  quiet := by intro q top bit; rfl
  correct := by intros; rfl

noncomputable abbrev compFlow {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![F.program,G.program]
  read _ := 0
  next p _ _ := if p = 0 then some ⟨1,.keep,none⟩ else none

noncomputable def compose {α β γ : Type} {ea : α → Data} {eb : β → Data} {ec : γ → Data}
    {f : α → β} {g : β → γ} (F : Device ea eb f) (G : Device eb ec g) : Device ea ec (g ∘ f) where
  program := Flow.compile (compFlow F G)
  limit x := F.limit x + G.limit (f x) + 2
  quiet := Flow.compile_coinFree _ (by intro p; fin_cases p; exact F.quiet; exact G.quiet)
    (by intros; rfl)
  correct x suffix out bits := by
    obtain ⟨s,hs,es⟩ := Flow.hop (compFlow F G) 0 1 (store (ea x) suffix) (store (eb (f x)) suffix) out bits
      (F.limit x) (F.correct x suffix out bits) (by intros; rfl)
    obtain ⟨t,ht,et⟩ := Flow.finish (compFlow F G) 1 (store (eb (f x)) suffix) (store (ec (g (f x))) suffix) out
      (fun j => bits (s+j)) (G.limit (f x)) (G.correct (f x) suffix out _) (by intros; rfl)
    apply advance_pad _ _ _ bits (n := s+t) (by omega) ?_ rfl
    change advance _ bits (Flow.state (compFlow F G) 0 (store (ea x) suffix) out) (s+t) = _
    rw [advance_add,es,et]
    rfl

theorem store_size (x : Data) (suffix : List Bool) :
    storeSize (store x suffix) = treeSize x + suffix.length := by
  simp [storeSize,store,treeSize,Fin.sum_univ_succ]

theorem output_size {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (x : α) :
    treeSize (eb (f x)) ≤ treeSize (ea x) + F.limit x := by
  have h := advance_size F.program ⟨some F.program.start,store (ea x) [],[]⟩ (fun _ => false) (F.limit x)
  rw [F.correct] at h
  simpa only [store_size,List.length_nil,Nat.add_zero] using h

end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits.Flow
open BinaryData.Take (advance_add)

theorem hop_update {K : ℕ} (P : Program K) (p q : Fin P.nodes)
    (s t u : Fin K → List Bool) (out : List Bool) (bits : ℕ → Bool) (N : ℕ) (op : BinaryStack.Op)
    (hm : advance (P.block p) bits ⟨some (P.block p).start,s,out⟩ N = ⟨none,t,out⟩)
    (hn : ∀ bit, P.next p (t (P.read p)).head? bit = some ⟨q,op,none⟩)
    (hu : Function.update t (P.read p) (BinaryStack.applyOp op (t (P.read p))) = u) :
    ∃ d ≤ N+1, advance (compile P) bits (state P p s out) d = state P q u out := by
  obtain ⟨d,hd,he⟩ := macro_runs P p s out bits N (by rw [hm])
  rw [hm] at he
  refine ⟨d+1, by omega, ?_⟩
  simp only [advance,he,step_boundary,hn,hu,Option.toList_none,List.append_nil]

end MeanPayoff.RegisterBits.Flow

namespace MeanPayoff.TreeDevice
open RegisterBits BinaryData
open BinaryData.Take (advance_add)

def core (a b c : List Bool) : Fin 5 → List Bool := ![a,b,c,[],[]]
@[simp] theorem core_zero (a b c : List Bool) : core a b c 0 = a := rfl
noncomputable def moveCode (i j : Fin 3) : RegisterBits.Program 5 := rename Take.program (slots i j)

theorem move01 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 0 1) bits ⟨some (moveCode 0 1).start,core (encode x++xs) ys zs,out⟩
      (6*treeSize x+3) = ⟨none,core xs (encode x++ys) zs,out⟩ := by
  have h := move_tree (0:Fin 3) 1 (by decide) (core (encode x++xs) ys zs) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move02 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 0 2) bits ⟨some (moveCode 0 2).start,core (encode x++xs) ys zs,out⟩
      (6*treeSize x+3) = ⟨none,core xs ys (encode x++zs),out⟩ := by
  have h := move_tree (0:Fin 3) 2 (by decide) (core (encode x++xs) ys zs) out x xs zs
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move10 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 1 0) bits ⟨some (moveCode 1 0).start,core ys (encode x++xs) zs,out⟩
      (6*treeSize x+3) = ⟨none,core (encode x++ys) xs zs,out⟩ := by
  have h := move_tree (1:Fin 3) 0 (by decide) (core ys (encode x++xs) zs) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem move20 (x : Data) (xs ys zs out : List Bool) (bits : ℕ → Bool) :
    advance (moveCode 2 0) bits ⟨some (moveCode 2 0).start,core ys zs (encode x++xs),out⟩
      (6*treeSize x+3) = ⟨none,core (encode x++ys) zs xs,out⟩ := by
  have h := move_tree (2:Fin 3) 0 (by decide) (core ys zs (encode x++xs)) out x xs ys
    rfl rfl rfl rfl bits
  refine h.trans ?_
  apply Take.config_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

@[simp] theorem core_update (xs ys zs : List Bool) (op : BinaryStack.Op) :
    Function.update (core xs ys zs) 0 (BinaryStack.applyOp op xs) =
      core (BinaryStack.applyOp op xs) ys zs := by
  funext i; fin_cases i <;> rfl

def listTree {α : Type} (e : α → Data) : List α → Data
  | [] => .nil
  | x::xs => .pair (e x) (listTree e xs)

@[simp] theorem listTree_nil {α : Type} (e : α → Data) : listTree e [] = .nil := rfl
@[simp] theorem listTree_cons {α : Type} (e : α → Data) (x : α) (xs : List α) :
    listTree e (x::xs) = .pair (e x) (listTree e xs) := rfl

@[simp] theorem encode_listTree_cons {α : Type} (e : α → Data) (x : α) (xs : List α) :
    encode (listTree e (x::xs)) = true :: (encode (e x) ++ encode (listTree e xs)) := rfl

@[simp] theorem treeSize_nil : treeSize Data.nil = 1 := rfl
@[simp] theorem treeSize_pair (x y : Data) : treeSize (.pair x y) = treeSize x+treeSize y+1 := by
  simp [treeSize,BinaryData.encode]

theorem listTree_size {α : Type} (e : α → Data) (xs : List α) :
    treeSize (listTree e xs) = 1 + xs.length + (xs.map (treeSize ∘ e)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Function.comp_def]; omega

end MeanPayoff.TreeDevice

namespace MeanPayoff.RegisterBits
open BinaryData.Take (advance_add)

def Reaches {K : ℕ} (P : Program K) (c d : Config P) (B : ℕ) : Prop :=
  ∀ bits : ℕ → Bool, ∃ t ≤ B, advance P bits c t = d

theorem Reaches.trans {K : ℕ} {P : Program K} {a b c : Config P} {M N : ℕ}
    (h : Reaches P a b M) (g : Reaches P b c N) : Reaches P a c (M+N) := by
  intro bits
  obtain ⟨s,hs,es⟩ := h bits
  obtain ⟨t,ht,et⟩ := g (fun j => bits (s+j))
  refine ⟨s+t, by omega, ?_⟩
  rw [advance_add,es,et]

theorem Reaches.mono {K : ℕ} {P : Program K} {a b : Config P} {M N : ℕ}
    (h : Reaches P a b M) (hm : M ≤ N) : Reaches P a b N := by
  intro bits
  obtain ⟨t,ht,he⟩ := h bits
  exact ⟨t,ht.trans hm,he⟩

theorem Reaches.pad {K : ℕ} {P : Program K} {a b : Config P} {N : ℕ}
    (h : Reaches P a b N) (hb : b.control = none) (bits : ℕ → Bool) : advance P bits a N = b := by
  obtain ⟨t,ht,he⟩ := h bits
  exact advance_pad P a b bits ht he hb
end MeanPayoff.RegisterBits

namespace MeanPayoff.TreeDevice.Map
open RegisterBits BinaryData TreeDevice

noncomputable abbrev flow {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Flow.Program 5 where
  nodes := 12
  start := 0
  block := ![moveCode 0 2, F.program, moveCode 0 1, moveCode 0 2, moveCode 1 0,
    moveCode 2 0, moveCode 0 2, moveCode 0 1, moveCode 0 2, moveCode 1 0, moveCode 2 0, skip]
  read _ := 0
  next p top _ := match p.val with
    | 0 => some ⟨5,.push false,none⟩
    | 1 => some ⟨2,.keep,none⟩
    | 2 => some ⟨3,.keep,none⟩
    | 3 => some ⟨4,.keep,none⟩
    | 4 => some ⟨5,.push true,none⟩
    | 5 => some ⟨if top = some true then 1 else 6,.pop,none⟩
    | 6 => some ⟨10,.push false,none⟩
    | 7 => some ⟨8,.keep,none⟩
    | 8 => some ⟨9,.keep,none⟩
    | 9 => some ⟨10,.push true,none⟩
    | 10 => some ⟨if top = some true then 7 else 11,.pop,none⟩
    | _ => none

noncomputable abbrev program {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) := Flow.compile (flow F)

noncomputable abbrev cfg {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (q : Fin 12) (a b c out : List Bool) : Config (program F) :=
  Flow.state (flow F) q (core a b c) out

def revTime {β : Type} (e : β → Data) : List β → ℕ
  | [] => 12
  | x::xs => 6*treeSize (listTree e (x::xs)) + 12*treeSize (e x) +
      6*treeSize (listTree e xs) + 16 + revTime e xs

theorem reverse_runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs acc : List β) (suffix out : List Bool) :
    Reaches (program F) (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode (listTree eb xs)) out)
      ⟨none,core (encode (listTree eb (xs.reverse++acc))++suffix) [] [],out⟩ (revTime eb xs) := by
  induction xs generalizing acc with
  | nil =>
    have hl : Reaches (program F)
        (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode Data.nil) out)
        (cfg F 11 (encode (listTree eb acc)++suffix) [] [] out) 10 := by
      intro bits
      apply Flow.hop_update (flow F) 10 11 _ _ _ out bits 9 .pop
        (move20 .nil [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
      change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
      simp only [core_zero,core_update]; rfl
    have hf : Reaches (program F) (cfg F 11 (encode (listTree eb acc)++suffix) [] [] out)
        ⟨none,core (encode (listTree eb acc)++suffix) [] [],out⟩ 2 := by
      intro bits
      exact Flow.finish (flow F) 11 _ _ out bits 1 rfl (by intros; rfl)
    exact hl.trans hf
  | cons x xs ih =>
    have h₀ : Reaches (program F)
        (cfg F 10 (encode (listTree eb acc)++suffix) [] (encode (listTree eb (x::xs))) out)
        (cfg F 7 (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out)
        (6*treeSize (listTree eb (x::xs))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 10 7 _ _
        (core (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] []) out bits _ .pop
        (move20 (listTree eb (x::xs)) [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₁ : Reaches (program F)
        (cfg F 7 (encode (eb x)++encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 8 (encode (listTree eb xs)++encode (listTree eb acc)++suffix) (encode (eb x)) [] out)
        (6*treeSize (eb x)+4) := by
      intro bits
      have h := Flow.hop (flow F) 7 8 _ _ out bits _
        (move01 (eb x) (encode (listTree eb xs)++encode (listTree eb acc)++suffix) [] [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₂ : Reaches (program F)
        (cfg F 8 (encode (listTree eb xs)++encode (listTree eb acc)++suffix) (encode (eb x)) [] out)
        (cfg F 9 (encode (listTree eb acc)++suffix) (encode (eb x)) (encode (listTree eb xs)) out)
        (6*treeSize (listTree eb xs)+4) := by
      intro bits
      have h := Flow.hop (flow F) 8 9 _ _ out bits _
        (move02 (listTree eb xs) (encode (listTree eb acc)++suffix) (encode (eb x)) [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₃ : Reaches (program F)
        (cfg F 9 (encode (listTree eb acc)++suffix) (encode (eb x)) (encode (listTree eb xs)) out)
        (cfg F 10 (encode (listTree eb (x::acc))++suffix) [] (encode (listTree eb xs)) out)
        (6*treeSize (eb x)+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 9 10 _ _
        (core (encode (listTree eb (x::acc))++suffix) [] (encode (listTree eb xs))) out bits _ (.push true)
        (move10 (eb x) [] (encode (listTree eb acc)++suffix) (encode (listTree eb xs)) out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h := h₀.trans (h₁.trans (h₂.trans (h₃.trans (ih (x::acc)))))
    have h' := h.mono (show _ ≤ revTime eb (x::xs) by simp only [revTime]; omega)
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using h'

def frontTime {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : List α → ℕ
  | [] => 10
  | x::xs => 6*treeSize (listTree ea (x::xs)) + 12*treeSize (eb (f x)) +
      6*treeSize (listTree ea xs) + F.limit x + 17 + frontTime F xs

theorem forward_runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) (acc : List β) (suffix out : List Bool) :
    Reaches (program F) (cfg F 5 (encode (listTree eb acc)++suffix) [] (encode (listTree ea xs)) out)
      (cfg F 6 (encode (listTree eb ((xs.map f).reverse++acc))++suffix) [] [] out)
       (frontTime F xs) := by
  induction xs generalizing acc with
  | nil =>
    intro bits
    apply Flow.hop_update (flow F) 5 6 _ _ _ out bits 9 .pop
      (move20 .nil [] (encode (listTree eb acc)++suffix) [] out bits)
      (by intro bit; rfl)
    change Function.update (core _ _ _) 0 (BinaryStack.applyOp .pop _) = _
    simp only [core_zero,core_update]; rfl
  | cons x xs ih =>
    have h₀ : Reaches (program F)
        (cfg F 5 (encode (listTree eb acc)++suffix) [] (encode (listTree ea (x::xs))) out)
        (cfg F 1 (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (6*treeSize (listTree ea (x::xs))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 5 1 _ _
        (core (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] []) out bits _ .pop
        (move20 (listTree ea (x::xs)) [] (encode (listTree eb acc)++suffix) [] out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.tail_cons,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have hF : Reaches (program F)
        (cfg F 1 (encode (ea x)++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 2 (encode (eb (f x))++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (F.limit x+1) := by
      intro bits
      have h := Flow.hop (flow F) 1 2 _ _ out bits _
        (F.correct x (encode (listTree ea xs)++encode (listTree eb acc)++suffix) out bits)
        (by intros; rfl)
      simpa only [store,core,cfg,List.append_assoc] using h
    have h₁ : Reaches (program F)
        (cfg F 2 (encode (eb (f x))++encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out)
        (cfg F 3 (encode (listTree ea xs)++encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out)
        (6*treeSize (eb (f x))+4) := by
      intro bits
      have h := Flow.hop (flow F) 2 3 _ _ out bits _
        (move01 (eb (f x)) (encode (listTree ea xs)++encode (listTree eb acc)++suffix) [] [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₂ : Reaches (program F)
        (cfg F 3 (encode (listTree ea xs)++encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out)
        (cfg F 4 (encode (listTree eb acc)++suffix) (encode (eb (f x))) (encode (listTree ea xs)) out)
        (6*treeSize (listTree ea xs)+4) := by
      intro bits
      have h := Flow.hop (flow F) 3 4 _ _ out bits _
        (move02 (listTree ea xs) (encode (listTree eb acc)++suffix) (encode (eb (f x))) [] out bits)
        (by intros; rfl)
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h₃ : Reaches (program F)
        (cfg F 4 (encode (listTree eb acc)++suffix) (encode (eb (f x))) (encode (listTree ea xs)) out)
        (cfg F 5 (encode (listTree eb (f x::acc))++suffix) [] (encode (listTree ea xs)) out)
        (6*treeSize (eb (f x))+4) := by
      intro bits
      have h := Flow.hop_update (flow F) 4 5 _ _
        (core (encode (listTree eb (f x::acc))++suffix) [] (encode (listTree ea xs))) out bits _ (.push true)
        (move10 (eb (f x)) [] (encode (listTree eb acc)++suffix) (encode (listTree ea xs)) out bits)
        (by intro bit; rfl)
        (by
          change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update]
          simp only [listTree_cons,BinaryData.encode,List.cons_append,BinaryStack.applyOp,List.append_assoc])
      simpa only [List.append_nil,List.append_assoc,Nat.add_assoc] using h
    have h := h₀.trans (hF.trans (h₁.trans (h₂.trans (h₃.trans (ih (f x::acc))))))
    have h' := h.mono (show _ ≤ frontTime F (x::xs) by simp only [frontTime]; omega)
    simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h'

def limit {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) :=
  6*treeSize (listTree ea xs)+4+frontTime F xs+
    (6*treeSize (listTree eb (xs.map f).reverse)+4)+revTime eb (xs.map f).reverse

theorem runs {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) (xs : List α) (suffix out : List Bool) :
    Reaches (program F) ⟨some (program F).start,store (listTree ea xs) suffix,out⟩
      ⟨none,store (listTree eb (xs.map f)) suffix,out⟩ (limit F xs) := by
  have h₀ : Reaches (program F) (cfg F 0 (encode (listTree ea xs)++suffix) [] [] out)
      (cfg F 5 (encode Data.nil++suffix) [] (encode (listTree ea xs)) out)
      (6*treeSize (listTree ea xs)+4) := by
    intro bits
    have h := Flow.hop_update (flow F) 0 5 _ _
      (core (encode Data.nil++suffix) [] (encode (listTree ea xs))) out bits _ (.push false)
      (move02 (listTree ea xs) suffix [] [] out bits) (by intros; rfl)
      (by change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update,List.append_nil]; rfl)
    simpa only [List.append_nil,Nat.add_assoc] using h
  have h₁ := forward_runs F xs [] suffix out
  simp only [List.append_nil,listTree_nil] at h₁
  have h₂ : Reaches (program F)
      (cfg F 6 (encode (listTree eb (xs.map f).reverse)++suffix) [] [] out)
      (cfg F 10 (encode Data.nil++suffix) [] (encode (listTree eb (xs.map f).reverse)) out)
      (6*treeSize (listTree eb (xs.map f).reverse)+4) := by
    intro bits
    have h := Flow.hop_update (flow F) 6 10 _ _
      (core (encode Data.nil++suffix) [] (encode (listTree eb (xs.map f).reverse))) out bits _ (.push false)
      (move02 (listTree eb (xs.map f).reverse) suffix [] [] out bits) (by intros; rfl)
      (by change Function.update (core _ _ _) 0 (BinaryStack.applyOp _ _) = _
          simp only [core_zero,core_update,List.append_nil]; rfl)
    simpa only [List.append_nil,Nat.add_assoc] using h
  have h₃ := reverse_runs F (xs.map f).reverse [] suffix out
  simp only [List.reverse_reverse,List.append_nil,listTree_nil] at h₃
  have h := h₀.trans (h₁.trans (h₂.trans h₃))
  exact h.mono (by simp only [limit]; omega)

noncomputable def device {α β : Type} {ea : α → Data} {eb : β → Data} {f : α → β}
    (F : Device ea eb f) : Device (listTree ea) (listTree eb) (List.map f) where
  program := program F
  limit := limit F
  quiet := by
    apply Flow.compile_coinFree
    · intro p
      fin_cases p <;> first | exact F.quiet | (intro q top bit; rfl)
    · intros; rfl
  correct xs suffix out bits := (runs F xs suffix out).pad rfl bits

end MeanPayoff.TreeDevice.Map
end

end OAI
