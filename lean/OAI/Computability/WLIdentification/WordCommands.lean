import OAI.Computability.WLIdentification.FiniteRefinement

namespace OAI

namespace WLIdentification

namespace StackModel
namespace Command
variable {K : Type} [DecidableEq K]

abbrev read (k : K) : Command K (Option Bool) := .pop k (fun _ b => b)
abbrev emit (k : K) : Command K (Option Bool) := .push k (fun b => b.getD false)

def drain (k : K) (body : Command K (Option Bool)) : Command K (Option Bool) :=
  .seq (read k) (.while Option.isSome (.seq body (read k)))

def clear (k : K) : Command K (Option Bool) := drain k .skip

def move (a b : K) : Command K (Option Bool) := drain a (emit b)

/-- Tail traversal is an actual structured loop, not a host-language iteration. -/
theorem drain_exec (k : K) (body : Command K (Option Bool))
    (S : K → Word) (s : Option Bool) (f : Bool → (K → Word) → (K → Word)) (c : ℕ)
    (hbody : ∀ b T, ∃ t, Exec body (some b) T t (f b T) c)
    (hpres : ∀ b T, f b T k = T k) :
    ∃ n ≤ (c + 2) * (S k).length + 2,
      Exec (drain k body) s S none
        ((S k).reverse.foldl (fun T b => f b (Function.update T k (T k).dropLast))
          S) n := by
  generalize hw : S k = w
  induction w using List.reverseRecOn generalizing S s with
  | nil =>
    have hu : Function.update S k [] = S := by
      funext x
      by_cases hx : x = k <;> simp [hx, hw]
    refine ⟨2, by simp, ?_⟩
    simp only [List.reverse_nil, List.foldl_nil]
    have hp : Exec (read k) s S none S 1 := by
      simpa only [read, hw, List.getLast?_nil, List.dropLast_nil, hu] using
        (Exec.pop k (fun _ b => b) s S)
    exact .seq hp (.while_false _ _ _ _ rfl)
  | append_singleton w b ih =>
    let T := Function.update S k w
    have hT : T k = w := by simp [T]
    obtain ⟨t, hb⟩ := hbody b T
    have hU : f b T k = w := (hpres _ _).trans hT
    obtain ⟨n, hn, he⟩ := ih (f b T) t hU
    dsimp only [drain] at he
    cases he with
    | seq hr hwhile =>
      cases hr
      rename_i nr
      have hp : Exec (read k) s S (some b) T 1 := by
        simpa only [read, hw, List.getLast?_append, List.getLast?_singleton,
          Option.some_or, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] using
          (Exec.pop k (fun _ b => b) s S)
      refine ⟨nr + c + 3, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton] at *
        nlinarith
      · have hh := Exec.seq hp (Exec.while_true (by rfl) (Exec.seq hb
            (Exec.pop k (fun _ b => b) t (f b T))) hwhile)
        convert hh using 1 <;> try omega
        all_goals try simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.foldl_cons, hw, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, T]
        all_goals rfl

def pushMany (ks : List K) : Command K (Option Bool) :=
  ks.foldr (fun k c => .seq (emit k) c) .skip

def appendMany (ks : List K) (b : Bool) (S : K → Word) : K → Word :=
  fun k => if k ∈ ks then S k ++ [b] else S k

theorem pushMany_exec (ks : List K) (hks : ks.Nodup) (b : Bool) (S : K → Word) :
    Exec (pushMany ks) (some b) S (some b) (appendMany ks b S) (ks.length + 1) := by
  induction ks generalizing S with
  | nil =>
    have h : appendMany [] b S = S := by funext k; simp [appendMany]
    simpa only [pushMany, List.foldr_nil, List.length_nil, Nat.zero_add, h] using Exec.skip (some b) S
  | cons k ks ih =>
    have hi := ih (List.nodup_cons.mp hks).2 (Function.update S k (S k ++ [b]))
    have he := Exec.seq (Exec.push k (fun x : Option Bool => x.getD false) (some b) S) hi
    have hstate : appendMany ks b (Function.update S k (S k ++ [b])) =
        appendMany (k :: ks) b S := by
      funext x
      by_cases hx : x = k
      · subst x
        simp [appendMany, (List.nodup_cons.mp hks).1]
      · simp [appendMany, hx]
    simpa only [pushMany, List.foldr_cons, List.length_cons, Nat.add_assoc, hstate] using he

def fanEffect (a : K) (ks : List K) (S : K → Word) : K → Word :=
  fun k => if k = a then [] else if k ∈ ks then S k ++ (S a).reverse else S k

theorem fan_fold (a : K) (ks : List K) (ha : a ∉ ks) (S : K → Word) :
    (S a).reverse.foldl (fun T b => appendMany ks b (Function.update T a (T a).dropLast)) S =
      fanEffect a ks S := by
  generalize hw : S a = w
  induction w using List.reverseRecOn generalizing S with
  | nil =>
    simp only [List.reverse_nil, List.foldl_nil]
    funext x
    by_cases hx : x = a <;> simp [fanEffect, hx, hw]
  | append_singleton w b ih =>
    let T := appendMany ks b (Function.update S a w)
    have hT : T a = w := by simp [T, appendMany, ha]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons,
      hw, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    change w.reverse.foldl _ T = _
    rw [ih T hT]
    funext x
    by_cases hx : x = a
    · simp [fanEffect, hx]
    · by_cases hk : x ∈ ks <;>
        simp [fanEffect, hx, T, appendMany, hw, ha, hk, List.reverse_append, List.append_assoc]

theorem fan_exec (a : K) (ks : List K) (hks : ks.Nodup) (ha : a ∉ ks)
    (s : Option Bool) (S : K → Word) :
    ∃ n ≤ (ks.length + 3) * (S a).length + 2,
      Exec (drain a (pushMany ks)) s S none (fanEffect a ks S) n := by
  obtain ⟨n, hn, he⟩ := drain_exec a (pushMany ks) S s (appendMany ks) (ks.length + 1)
    (fun b T => ⟨some b, pushMany_exec ks hks b T⟩)
    (by intro b T; simp [appendMany, ha])
  refine ⟨n, by omega, ?_⟩
  rwa [fan_fold a ks ha S] at he

theorem clear_exec (a : K) (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 3 * (S a).length + 2,
      Exec (clear a) s S none (Function.update S a []) n := by
  have hf : fanEffect a [] S = Function.update S a [] := by
    funext k; by_cases h : k = a <;> simp [fanEffect, h]
  simpa only [clear, pushMany, List.foldr_nil, List.length_nil, Nat.zero_add, hf] using
    fan_exec a [] (by simp) (by simp) s S

theorem move_exec (a b : K) (hab : a ≠ b) (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 4 * (S a).length + 2,
      Exec (drain a (pushMany [b])) s S none
        (Function.update (Function.update S a []) b (S b ++ (S a).reverse)) n := by
  have hf : fanEffect a [b] S = Function.update (Function.update S a []) b
      (S b ++ (S a).reverse) := by
    funext k
    by_cases hb : k = b
    · simp [fanEffect, hb, hab.symm]
    · by_cases ha : k = a <;> simp [fanEffect, ha, hb, hab]
  simpa only [List.length_singleton, hf] using fan_exec a [b] (by simp) (by simp [hab]) s S

/-- Copy a complete word, preserving its order and the source, using one private work stack. -/
def copy (a b tmp : K) : Command K (Option Bool) :=
  .seq (clear b) (.seq (clear tmp) (.seq (drain a (pushMany [tmp]))
    (drain tmp (pushMany [a,b]))))

theorem copy_exec (a b tmp : K) (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp)
    (s : Option Bool) (S : K → Word) :
    ∃ n ≤ 3 * (S b).length + 3 * (S tmp).length + 9 * (S a).length + 8,
      Exec (copy a b tmp) s S none (Function.update (Function.update S b (S a)) tmp []) n := by
  obtain ⟨n₁, hn₁, he₁⟩ := clear_exec b s S
  let S₁ := Function.update S b []
  obtain ⟨n₂, hn₂, he₂⟩ := clear_exec tmp none S₁
  let S₂ := Function.update S₁ tmp []
  obtain ⟨n₃, hn₃, he₃⟩ := move_exec a tmp hat none S₂
  let S₃ := Function.update (Function.update S₂ a []) tmp (S₂ tmp ++ (S₂ a).reverse)
  obtain ⟨n₄, hn₄, he₄⟩ := fan_exec tmp [a,b] (by simp [hab]) (by simp [hat.symm,hbt.symm]) none S₃
  have hf : fanEffect tmp [a,b] S₃ = Function.update (Function.update S b (S a)) tmp [] := by
    funext k
    by_cases ht : k = tmp
    · simp [fanEffect, ht]
    · by_cases ha : k = a
      · subst k
        simp [fanEffect, hat, S₃, S₂, S₁, hab]
      · by_cases hb : k = b
        · subst k
          simp [fanEffect, hbt, hab.symm, S₃, S₂, S₁, hat, hab]
        · simp [fanEffect, ht, ha, hb, S₃, S₂, S₁]
  refine ⟨n₄ + n₃ + n₂ + n₁, ?_, ?_⟩
  · simp only [S₁, S₂, S₃, Function.update_self, Function.update_of_ne hat,
      Function.update_of_ne hab, Function.update_of_ne hbt.symm, List.nil_append,
      List.length_reverse, List.length_cons, List.length_nil] at hn₂ hn₃ hn₄
    omega
  · exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (hf ▸ he₄)))

end Command
end StackModel
namespace StackModel.Command
variable {K L R : Type}

def rename (e : K → L) : Command K R → Command L R
  | .skip => .skip
  | .push k f => .push (e k) f
  | .pop k f => .pop (e k) f
  | .modify f => .modify f
  | .seq c d => .seq (rename e c) (rename e d)
  | .branch t c d => .branch t (rename e c) (rename e d)
  | .while t c => .while t (rename e c)

@[simp] theorem rename_rename {N : Type} (e : K → L) (f : L → N) (c : Command K R) :
    rename f (rename e c) = rename (f ∘ e) c := by
  induction c <;> simp_all [rename]

variable [DecidableEq K] [DecidableEq L]

/-- Renaming uses only the named stacks; arbitrary ambient data are framed. -/
theorem Exec.rename {c : Command K R} {s S t T n} (h : Exec c s S t T n)
    (e : K ↪ L) (W : L → Word) (hW : W ∘ e = S) :
    ∃ U, Exec (c.rename e) s W t U n ∧ U ∘ e = T ∧
      ∀ l, (∀ k, e k ≠ l) → U l = W l := by
  induction h generalizing W with
  | skip s S => exact ⟨W, .skip _ _, hW, by intros; rfl⟩
  | modify f s S => exact ⟨W, .modify _ _ _, hW, by intros; rfl⟩
  | push k f s S =>
    let U := Function.update W (e k) (W (e k) ++ [f s])
    refine ⟨U, .push _ _ _ _, ?_, ?_⟩
    · have hval : W (e k) = S k := congrFun hW k
      simp only [U, Function.update_comp_eq_of_injective W e.injective, hW, hval]
    · intro l hl
      exact Function.update_of_ne (hl k).symm _ _
  | pop k f s S =>
    let U := Function.update W (e k) (W (e k)).dropLast
    have hval : W (e k) = S k := congrFun hW k
    refine ⟨U, ?_, ?_, ?_⟩
    · simpa only [Command.rename, U, ← hval] using Exec.pop (e k) f s W
    · simp only [U, Function.update_comp_eq_of_injective W e.injective, hW, hval]
    · intro l hl
      exact Function.update_of_ne (hl k).symm _ _
  | seq hc hd ihc ihd =>
    obtain ⟨V, hV, heV, hfV⟩ := ihc W hW
    obtain ⟨U, hU, heU, hfU⟩ := ihd V heV
    exact ⟨U, .seq hV hU, heU, fun l hl => (hfU l hl).trans (hfV l hl)⟩
  | branch_true ht hc ih =>
    obtain ⟨U, hU, heU, hfU⟩ := ih W hW
    exact ⟨U, .branch_true ht hU, heU, hfU⟩
  | branch_false ht hc ih =>
    obtain ⟨U, hU, heU, hfU⟩ := ih W hW
    exact ⟨U, .branch_false ht hU, heU, hfU⟩
  | while_false test c s S ht => exact ⟨W, .while_false _ _ _ _ ht, hW, by intros; rfl⟩
  | while_true ht hc hd ihc ihd =>
    obtain ⟨V, hV, heV, hfV⟩ := ihc W hW
    obtain ⟨U, hU, heU, hfU⟩ := ihd V heV
    exact ⟨U, .while_true ht hV hU, heU, fun l hl => (hfU l hl).trans (hfV l hl)⟩

variable {A B : Type} [DecidableEq A] [DecidableEq B]

def embedLeft : K ⊕ A ↪ K ⊕ (A ⊕ B) where
  toFun := Sum.map id Sum.inl
  inj' := by
    intro x y h
    cases x <;> cases y
    · simpa using h
    · cases h
    · cases h
    · simpa using h

def embedRight : K ⊕ B ↪ K ⊕ (A ⊕ B) where
  toFun := Sum.map id Sum.inr
  inj' := by
    intro x y h
    cases x <;> cases y
    · simpa using h
    · cases h
    · cases h
    · simpa using h

theorem Exec.left {c : Command (K ⊕ A) R} {s t S T X Y n}
    (h : Exec c s (Sum.elim S X) t (Sum.elim T Y) n) (Z : B → Word) :
    Exec (c.rename (embedLeft : K ⊕ A ↪ K ⊕ (A ⊕ B))) s (Sum.elim S (Sum.elim X Z))
      t (Sum.elim T (Sum.elim Y Z)) n := by
  obtain ⟨U, hU, he, hf⟩ := h.rename embedLeft (Sum.elim S (Sum.elim X Z)) (by
    funext x; cases x <;> rfl)
  have hu : U = Sum.elim T (Sum.elim Y Z) := by
    funext x
    cases x with
    | inl k => exact congrFun he (.inl k)
    | inr x => cases x with
      | inl a => exact congrFun he (.inr a)
      | inr b => exact hf _ (by intro x; cases x <;> intro h <;> cases h)
  exact hu ▸ hU

theorem Exec.right {c : Command (K ⊕ B) R} {s t S T X Y n}
    (h : Exec c s (Sum.elim S X) t (Sum.elim T Y) n) (Z : A → Word) :
    Exec (c.rename (embedRight : K ⊕ B ↪ K ⊕ (A ⊕ B))) s (Sum.elim S (Sum.elim Z X))
      t (Sum.elim T (Sum.elim Z Y)) n := by
  obtain ⟨U, hU, he, hf⟩ := h.rename embedRight (Sum.elim S (Sum.elim Z X)) (by
    funext x; cases x <;> rfl)
  have hu : U = Sum.elim T (Sum.elim Z Y) := by
    funext x
    cases x with
    | inl k => exact congrFun he (.inl k)
    | inr x => cases x with
      | inl a => exact hf _ (by intro x; cases x <;> intro h <;> cases h)
      | inr b => exact congrFun he (.inr b)
  exact hu ▸ hU

/-- A finite chain of loop states has the counted actual execution. -/
theorem while_steps (test : R → Bool) (c : Command K R) (n cost : ℕ)
    (s : ℕ → R) (S : ℕ → K → Word)
    (hs : ∀ i < n, test (s i) = true) (hn : test (s n) = false)
    (hstep : ∀ i < n, ∃ t ≤ cost, Exec c (s i) (S i) (s (i+1)) (S (i+1)) t) :
    ∃ t ≤ (cost + 1) * n + 1, Exec (.while test c) (s 0) (S 0) (s n) (S n) t := by
  induction n generalizing s S with
  | zero => exact ⟨1, by omega, .while_false _ _ _ _ hn⟩
  | succ n ih =>
    obtain ⟨a, ha, hea⟩ := hstep 0 (by omega)
    obtain ⟨b, hb, heb⟩ := ih (fun i => s (i+1)) (fun i => S (i+1))
      (by intro i hi; exact hs _ (by omega)) hn (by intro i hi; exact hstep _ (by omega))
    exact ⟨b + a + 1, by nlinarith, .while_true (hs 0 (by omega)) hea heb⟩

end StackModel.Command

end WLIdentification

end OAI
