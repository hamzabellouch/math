import OAI.Computability.SpaceSimulation.Register.Scale
import OAI.Computability.SpaceSimulation.Stack.Edit
import OAI.Computability.SpaceSimulation.Stack.Lift

namespace OAI

/-! Port-wise contracts on uniform families of invocations.
Hidden stacks are also binary; they start and finish empty.
-/

namespace Fifths

namespace Store
variable {L K J : Type}

def extra (K : Type) (s : Store J L) : Store J (L ⊕ K) :=
  ⟨s.ro, Sum.elim s.st (fun _ => [])⟩

@[simp] theorem ok_extra {s : Store J L} {B} : (s.extra K).ok B ↔ s.ok B :=
  ⟨fun o k => o (.inl k), fun o k => match k with
    | .inl k => o k
    | .inr _ => Nat.zero_le _⟩

/-- Conditions for identifying a padded port file. -/
theorem pad_eq (e : K ↪ L) (d : L → List Bool)
    {s : Store J K} {t : Store J L}
    (h : s.ro = t.ro)
    (g : ∀ k, s.st k = t.st (e k))
    (o : ∀ y, (¬ ∃ k, e k = y) → d y = t.st y) :
    s.pad e d = t := by
  classical
  refine Store.ext' h ?_
  intro y
  by_cases hy : ∃ k, e k = y
  · obtain ⟨k,rfl⟩ := hy
    rw [Store.pad_st,g]
  · rw [Store.pad_st' _ _ _ _ hy, o y hy]

end Store

namespace SM
open Function
variable {X J K L U Y : Type}

/-- Enlarge a machine's collection of hidden stacks. -/
noncomputable def more (e : K ↪ U) (M : SM X J (L ⊕ K) Y) : SM X J (L ⊕ U) Y :=
  M.pad ((Embedding.refl L).sumMap e)

theorem exec_more (e : K ↪ U) {M : SM X J (L ⊕ K) Y} {i B y} {s t : Store J L}
    (r : M.Exec i B (s.extra K) (t.extra K) y) :
    (M.more e).Exec i B (s.extra U) (t.extra U) y := by
  classical
  have p (v : Store J L) :
      (v.extra K).pad ((Embedding.refl L).sumMap e) (fun _ => []) = v.extra U := by
    apply Store.pad_eq
    · rfl
    · rintro (l|k) <;> rfl
    · rintro (l|u) h
      · exact (h ⟨.inl l, rfl⟩).elim
      · rfl
  unfold more
  rw [← p s, ← p t]
  exact M.pad_exec _ r (fun _ => Nat.zero_le _)
end SM

/-- Uniform relation on port stacks. Context X,J,L,Y are finite
in uses that witness computation in the main theorem. -/
def Works {X J I L Y : Type} (x : I → Inputs X J) (S : I → ℕ)
    (a b : I → Store J L) (y : I → Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (M : SM X J (L ⊕ K) Y) (c : ℕ),
    ∀ i, M.Exec (x i) (c*(S i+1)) ((a i).extra K) ((b i).extra K) (y i)

/-- Space for the contents of the port file itself (not input positions). -/
def FitsStore {I J L : Type} (S : I → ℕ) (s : I → Store J L) : Prop :=
  ∃ c, ∀ i, (s i).ok (c*(S i+1))

namespace Works
variable {X J I L Y : Type} {x : I → Inputs X J}
  {S A : I → ℕ} {a b : I → Store J L} {y : I → Y}
open Function

theorem source (r : Works x S a b y) : FitsStore S a := by
  obtain ⟨K,h,M,c,r⟩ := r
  exact ⟨c,fun i => Store.ok_extra.mp (r i).startOk⟩

theorem target (r : Works x S a b y) : FitsStore S b := by
  obtain ⟨K,h,M,c,r⟩ := r
  exact ⟨c,fun i => Store.ok_extra.mp (r i).endOk⟩

theorem pull (r : Works x S a b y) {D : Type} (f : D → I) :
    Works (fun i => x (f i)) (fun i => S (f i)) (fun i => a (f i))
      (fun i => b (f i)) (fun i => y (f i)) := by
  obtain ⟨K,h,M,c,r⟩ := r
  exact ⟨K,h,M,c,fun i => r (f i)⟩

theorem up (r : Works x S a b y) (p : Scaled A S) :
    Works x A a b y := by
  obtain ⟨K,h,M,c,r⟩ := r
  obtain ⟨d,p⟩ := p.add (Scaled.const A 1)
  exact ⟨K,h,M,c*d,fun i => (r i).mono <| by
    rw [mul_assoc]; exact Nat.mul_le_mul_left c (p i)⟩

theorem direct (M : SM X J L Y) (c : ℕ)
    (r : ∀ i, M.Exec (x i) (c*(S i+1)) (a i) (b i) (y i)) :
    Works x S a b y := by
  classical
  let e : L ↪ L ⊕ Empty := Embedding.inl
  refine ⟨Empty,inferInstance,M.pad e,c,fun i => ?_⟩
  have h (u : Store J L) : u.pad e (fun _ => []) = u.extra Empty := by
    apply Store.pad_eq
    · rfl
    · intro l; rfl
    · rintro (l | l) g
      · exact (g ⟨l,rfl⟩).elim
      · cases l
  rw [← h, ← h]
  exact M.pad_exec e (r i) (fun _ => Nat.zero_le _)

theorem addPorts {U : Type} (r : Works x S a b y) (e : L ↪ U)
    (v w : I → Store J U) (p : FitsStore S v)
    (p₁ : ∀ i, (a i).ro = (v i).ro)
    (p₂ : ∀ i, (b i).ro = (w i).ro)
    (q₁ : ∀ i k, (a i).st k = (v i).st (e k))
    (q₂ : ∀ i k, (b i).st k = (w i).st (e k))
    (o : ∀ i l, (¬∃ k, e k = l) → (v i).st l = (w i).st l) :
    Works x S v w y := by
  classical
  obtain ⟨K,h,M,c,r⟩ := r
  obtain ⟨d,p⟩ := p
  let e' : L ⊕ K ↪ U ⊕ K := e.sumMap (Embedding.refl K)
  refine ⟨K,h,M.pad e',c+d,fun i => ?_⟩
  let a' := ((v i).extra K).st
  have g₁ : ((a i).extra K).pad e' a' = (v i).extra K := by
    apply Store.pad_eq
    · exact p₁ i
    · rintro (l|k)
      · exact q₁ i _
      · rfl
    · intros; rfl
  have g₂ : ((b i).extra K).pad e' a' = (w i).extra K := by
    apply Store.pad_eq
    · exact p₂ i
    · rintro (l|k)
      · exact q₂ i _
      · rfl
    · rintro (u|k) g
      · apply o
        rintro ⟨l, rfl⟩
        exact g ⟨.inl l,rfl⟩
      · rfl
  rw [← g₁,← g₂]
  exact M.pad_exec _ ((r i).mono (by rw [add_mul]; omega)) <|
    (Store.ok_extra.mpr ((p i).mono (by rw [add_mul]; omega)))

/-- Hide port stacks used in scratch fashion. -/
theorem hide (U : Type) [Fintype U]
    (r : Works x S (fun i => (a i).extra U) (fun i => (b i).extra U) y) :
    Works x S a b y := by
  classical
  obtain ⟨K,h,M,c,r⟩ := r
  have := h
  let e := (Equiv.sumAssoc L U K).toEmbedding
  refine ⟨U ⊕ K,inferInstance,M.pad e,c,fun i => ?_⟩
  have H (s : Store J L) :
      ((s.extra U).extra K).pad e (fun _ => []) = s.extra (U ⊕ K) := by
    apply Store.pad_eq
    · rfl
    · rintro ((l|u)|k) <;> rfl
    · intro l g
      exact (g ((Equiv.sumAssoc L U K).surjective l)).elim
  rw [← H,← H]
  exact M.pad_exec _ (r i) (fun _ => Nat.zero_le _)

theorem seq {s : I → Store J L} (r : Works x S a b (fun _ => ()))
    (p : Works x S b s y) :
    Works x S a s y := by
  classical
  obtain ⟨K,h,M,c,r⟩ := r
  obtain ⟨U,g,N,d,p⟩ := p
  have := h; have := g
  let m := M.more (Embedding.inl (α := K) (β := U))
  let n := N.more (Embedding.inr (α := K) (β := U))
  refine ⟨K⊕U,inferInstance,m.seq n,c+d,fun i => ?_⟩
  exact SM.exec_seq
    (SM.exec_more _ ((r i).mono (by rw [add_mul]; omega)))
    (SM.exec_more _ ((p i).mono (by rw [add_mul]; omega)))

section BoolBranch
variable {B : I → Bool}
theorem branch {s : I → Store J L} (r : Works x S a b B)
    (yes : Works (fun i : {i // B i = true} => x i) (fun i => S i)
      (fun i => b i) (fun i => s i) (fun i => y i))
    (no : Works (fun i : {i // B i = false} => x i) (fun i => S i)
      (fun i => b i) (fun i => s i) (fun i => y i)) :
    Works x S a s y := by
  classical
  obtain ⟨K,h,M,c,r⟩ := r
  obtain ⟨U,g,N,d,p⟩ := yes
  obtain ⟨V,l,O,f,q⟩ := no
  have := h; have := g; have := l
  let W := K ⊕ U ⊕ V
  let eM : K ↪ W := Embedding.inl
  let eD : U ⊕ V ↪ W := Embedding.inr
  let eN : U ↪ W := Embedding.inl.trans eD
  let eO : V ↪ W := Embedding.inr.trans eD
  refine ⟨W,inferInstance,
    (M.more eM).bind (fun b => if b then N.more eN else O.more eO),
    c+d+f,fun i => ?_⟩
  rw [add_mul,add_mul]
  refine SM.exec_bind _ _ (SM.exec_more eM ((r i).mono (by omega))) ?_
  cases e : B i with
  | false =>
    exact SM.exec_more eO ((q ⟨i,e⟩).mono (by dsimp; omega))
  | true =>
    exact SM.exec_more eN ((p ⟨i,e⟩).mono (by dsimp; omega))
end BoolBranch

end Works
end Fifths

end OAI
