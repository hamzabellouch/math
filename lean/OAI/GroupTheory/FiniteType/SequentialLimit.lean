import Mathlib
import OAI.GroupTheory.FiniteType.SingularSubdivisionIterate

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SequentialLimit

structure End (A : Type*) where
  toFun : A → A

instance endFunLike (A : Type*) : FunLike (End A) A A where
  coe := End.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; cases h; rfl

variable {X Y : Type*}

def transition (s : X → X) (i j : ℕ) (_ : i ≤ j) : End X := ⟨s^[j - i]⟩

@[simp] lemma transition_apply (s : X → X) (i j : ℕ) (h : i ≤ j) (x : X) :
    transition s i j h x = s^[j-i] x := rfl

instance directed (s : X → X) :
    DirectedSystem (fun _ : ℕ => X) (transition s · · ·) where
  map_self {i} x := by simp only [transition_apply, Nat.sub_self, Function.iterate_zero, id_eq]
  map_map {k j i} hij hjk x := by
    simp only [transition_apply]
    rw [← Function.iterate_add_apply]
    congr 1
    omega

abbrev Limit (s : X → X) := DirectLimit (fun _ : ℕ => X) (transition s)

abbrev of (s : X → X) (i : ℕ) (x : X) : Limit s := Quotient.mk _ ⟨i, x⟩

lemma of_advance (s : X → X) (i j : ℕ) (h : i ≤ j) (x : X) :
    of s i x = of s j (s^[j-i] x) := DirectLimit.eq_of_le (f := transition s) ⟨i,x⟩ j h

@[simp] lemma of_succ (s : X → X) (i : ℕ) (x : X) :
    of s (i + 1) (s x) = of s i x := by
  simp only [of_advance s i (i+1) (Nat.le_succ i) x, Nat.add_sub_cancel_left,
    Function.iterate_one]

lemma of_injective (s : X → X) (hs : Function.Injective s) (i : ℕ) :
    Function.Injective (of s i) :=
  DirectLimit.mk_injective (transition s) (fun _ _ _ => hs.iterate _) i

lemma exists_rep (s : X → X) (x : Limit s) : ∃ i y, x = of s i y :=
  DirectLimit.exists_eq_mk _ x

@[elab_as_elim] lemma induction {s : X → X} {P : Limit s → Prop}
    (h : ∀ i x, P (of s i x)) (x : Limit s) : P x := DirectLimit.induction _ h x

lemma iterate_compat (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) (n : ℕ) (x : X) :
    t^[n] (f x) = f (s^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', ih] using hf (s^[n] x)

def map (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) : Limit s → Limit t :=
  DirectLimit.map _ _ (fun _ => f) (fun _ _ _ x => iterate_compat s t f hf _ x)

@[simp] lemma map_of (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) (i : ℕ) (x : X) :
    map s t f hf (of s i x) = of t i (f x) := rfl

def shift (s : X → X) : Equiv.Perm (Limit s) where
  toFun := DirectLimit.lift _ (fun i x => of s (i+1) x) (by
    intro i j h x
    simpa only [Nat.add_sub_add_right, transition_apply] using
      of_advance s (i+1) (j+1) (Nat.succ_le_succ h) x)
  invFun := map s s s (fun _ => rfl)
  left_inv := by
    intro x
    induction x using SequentialLimit.induction with | h i x =>
      exact of_succ s i x
  right_inv := by
    intro x
    induction x using SequentialLimit.induction with | h i x =>
      exact of_succ s i x

@[simp] lemma shift_of (s : X → X) (i : ℕ) (x : X) :
    shift s (of s i x) = of s (i+1) x := rfl

@[simp] lemma shift_symm_of (s : X → X) (i : ℕ) (x : X) :
    (shift s).symm (of s i x) = of s i (s x) := rfl

lemma shift_pow_of (s : X → X) (n i : ℕ) (x : X) :
    (shift s ^ n) (of s i x) = of s (i+n) x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, ih, shift_of, Nat.add_assoc]

lemma tuple_rep (s : X → X) {α : Type*} [Fintype α] (v : α → Limit s) :
    ∃ (i : ℕ) (w : α → X), ∀ a, v a = of s i (w a) := by
  classical
  choose i x hx using fun a => exists_rep s (v a)
  let k := Finset.univ.sup i
  have hik (a : α) : i a ≤ k := Finset.le_sup (f := i) (Finset.mem_univ a)
  exact ⟨k, fun a => s^[k-i a] (x a), fun a => (hx a).trans (of_advance s _ _ (hik a) _)⟩

lemma pair_rep (s : X → X) (t : Y → Y) (x : Limit s) (y : Limit t) :
    ∃ (i : ℕ) (a : X) (b : Y), x = of s i a ∧ y = of t i b := by
  obtain ⟨i,a,rfl⟩ := exists_rep s x
  obtain ⟨j,b,rfl⟩ := exists_rep t y
  exact ⟨max i j, s^[max i j-i] a, t^[max i j-j] b,
    of_advance s _ _ (le_max_left _ _) _, of_advance t _ _ (le_max_right _ _) _⟩

instance limitCountable (s : X → X) [Countable X] : Countable (Limit s) :=
  inferInstanceAs (Countable (Quotient (DirectLimit.setoid (transition s))))

lemma limit_infinite (s : X → X) [Infinite X] (hs : Function.Injective s) :
    Infinite (Limit s) := Infinite.of_injective (of s 0) (of_injective s hs 0)

def stage (s : X → X) (i : ℕ) : Set (Limit s) := Set.range (of s i)

lemma stage_mono (s : X → X) {i j : ℕ} (hij : i ≤ j) :
    stage s i ⊆ stage s j := by
  rintro _ ⟨x,rfl⟩
  exact ⟨s^[j-i] x, (of_advance s i j hij x).symm⟩

lemma stage_strict (s : X → X) (hs : Function.Injective s)
    (hn : ¬Function.Surjective s) (i : ℕ) : stage s i ⊂ stage s (i+1) := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨stage_mono s (Nat.le_succ i), ?_⟩
  intro h
  apply hn
  intro x
  have hx : of s (i+1) x ∈ stage s i := by
    rw [h]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hx
  refine ⟨y, of_injective s hs (i+1) ?_⟩
  simpa only [of_succ] using hy

lemma shift_stage (s : X → X) (i : ℕ) :
    shift s '' stage s i = stage s (i+1) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,rfl⟩,rfl⟩
    exact ⟨y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact ⟨of s i y, ⟨y,rfl⟩, rfl⟩

end SequentialLimit

namespace SequentialAction

open SequentialLimit

variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

def transitionHom (i j : ℕ) (h : i ≤ j) : U →* U where
  toFun := transition f i j h
  map_one' := by
    change (f : U → U)^[j-i] 1 = 1
    generalize j-i = n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_one]
  map_mul' x y := by
    change (f : U → U)^[j-i] (x*y) = (f : U → U)^[j-i] x * (f : U → U)^[j-i] y
    generalize j-i = n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

instance homDirected : DirectedSystem (fun _ : ℕ => U) (transitionHom f · · ·) :=
  SequentialLimit.directed f

instance limitGroup : Group (Limit f) :=
  inferInstanceAs (Group (DirectLimit (fun _ : ℕ => U) (transitionHom f)))

def ofGroup (i : ℕ) : U →* Limit f where
  toFun := of f i
  map_one' := (DirectLimit.one_def (f := transitionHom f) i).symm
  map_mul' x y := (DirectLimit.mul_def (G := fun _ : ℕ => U) (f := transitionHom f) i x y).symm

include heq in
lemma iterate_equivariant (n : ℕ) (g : U) (x : X) :
    s^[n] (g • x) = (f : U → U)^[n] g • s^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, heq]

def act : Limit f → Limit s → Limit s :=
  DirectLimit.map₂ (transition f) (transition s) (transition s)
    (fun _ => (· • ·)) (by
      intro i j _ g x
      simpa only [transition_apply] using iterate_equivariant f s heq (j-i) g x)

@[simp] lemma act_of (i : ℕ) (g : U) (x : X) :
    act f s heq (of f i g) (of s i x) = of s i (g • x) :=
  DirectLimit.map₂_def ..

@[instance_reducible] def limitAction : MulAction (Limit f) (Limit s) where
  smul := act f s heq
  one_smul x := by
    induction x using SequentialLimit.induction with | h i x =>
      change act f s heq 1 (of s i x) = _
      have hone : (1 : Limit f) = of f i 1 := DirectLimit.one_def (f := transitionHom f) i
      rw [hone, act_of, one_smul]
  mul_smul g h x := by
    obtain ⟨i, g, h, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (transition f) g h
    obtain ⟨j, x, rfl⟩ := exists_rep s x
    let k := max i j
    change act f s heq (of f i g * of f i h) (of s j x) =
      act f s heq (of f i g) (act f s heq (of f i h) (of s j x))
    rw [of_advance f i k (le_max_left _ _) g, of_advance f i k (le_max_left _ _) h,
      of_advance s j k (le_max_right _ _) x]
    have hmul (g h : U) : of f k g * of f k h = of f k (g*h) :=
      DirectLimit.mul_def (G := fun _ : ℕ => U) (f := transitionHom f) k g h
    rw [hmul, act_of, act_of, act_of, mul_smul]

@[simp] lemma of_smul (i : ℕ) (g : U) (x : X) :
    letI := limitAction f s heq
    of f i g • of s i x = of s i (g • x) := act_of ..

@[simp] lemma of_mul (i : ℕ) (g h : U) :
    of f i (g*h) = of f i g * of f i h := (ofGroup f i).map_mul g h

@[simp] lemma of_one (i : ℕ) : of f i 1 = 1 := (ofGroup f i).map_one

lemma act_injective [FaithfulSMul U X] (hs : Function.Injective s)
    {g h : Limit f} (hact : ∀ x, act f s heq g x = act f s heq h x) : g = h := by
  obtain ⟨i,g,h,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition f) g h
  change of f i g = of f i h
  congr 1
  apply eq_of_smul_eq_smul (α := X)
  intro x
  apply of_injective s hs i
  simpa only [act_of] using hact (of s i x)

def shiftGroup : MulAut (Limit f) where
  toEquiv := shift f
  map_mul' g h := by
    obtain ⟨i,g,h,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition f) g h
    change shift f (of f i g * of f i h) = shift f (of f i g) * shift f (of f i h)
    rw [← of_mul]
    change of f (i+1) (g*h) = of f (i+1) g * of f (i+1) h
    exact of_mul f _ _ _

@[simp] lemma shiftGroup_of (i : ℕ) (g : U) :
    shiftGroup f (of f i g) = of f (i+1) g := rfl

lemma shift_equivariant (g : Limit f) (x : Limit s) :
    shift s (act f s heq g x) = act f s heq (shiftGroup f g) (shift s x) := by
  obtain ⟨i,g,x,rfl,rfl⟩ := pair_rep f s g x
  simp only [act_of, shift_of, shiftGroup_of]

def HasImageTupleTransitivity : Prop :=
  ∀ (n : ℕ) (x y : Fin n → X), Function.Injective x → Function.Injective y →
    ∃ g : U, ∀ a, g • s (x a) = s (y a)

lemma limit_tuple_transitivity (ht : HasImageTupleTransitivity (U := U) s)
    (n : ℕ) (v w : Fin n → Limit s) (hv : Function.Injective v)
    (hw : Function.Injective w) : ∃ g : Limit f, ∀ a, act f s heq g (v a) = w a := by
  obtain ⟨i,z,hz⟩ := tuple_rep s (Sum.elim v w)
  let x : Fin n → X := fun a => z (.inl a)
  let y : Fin n → X := fun a => z (.inr a)
  have hx (a : Fin n) : v a = of s i (x a) := hz (.inl a)
  have hy (a : Fin n) : w a = of s i (y a) := hz (.inr a)
  have hxi : Function.Injective x := by
    intro a b hab
    apply hv
    rw [hx a, hx b, hab]
  have hyi : Function.Injective y := by
    intro a b hab
    apply hw
    rw [hy a, hy b, hab]
  obtain ⟨g,hg⟩ := ht n x y hxi hyi
  refine ⟨of f (i+1) g, fun a => ?_⟩
  rw [hx, hy, ← of_succ s i (x a), ← of_succ s i (y a), act_of, hg]

end SequentialAction

end

end OAI
