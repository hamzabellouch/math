import OAI.Analysis.FreeEntropy.NoiseTensor

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

def atomMul (a b : Atom B G) : Atom B G := (a.1 ++ b.1, a.2 * b.2)

def concatAux (a : Atom B G) : List (N × Atom B G) → Word B N G → Word B N G
  | [], v => (atomMul a v.1, v.2)
  | (i,b) :: t, v => push a i (concatAux b t v)

def concat (w v : Word B N G) : Word B N G := concatAux w.1 w.2 v

@[simp] theorem concat_nil (a : Atom B G) (v : Word B N G) :
    concat (a, ([] : List (N × Atom B G))) v = (atomMul a v.1, v.2) := rfl

@[simp] theorem concat_push (a : Atom B G) (i : N) (w v : Word B N G) :
    concat (push a i w) v = push a i (concat w v) := rfl

@[simp] theorem concat_empty_left (v : Word B N G) : concat empty v = v := by
  rcases v with ⟨⟨l,g⟩,t⟩
  simp [concat, concatAux, empty, atomMul]

@[simp] theorem concat_empty_right (w : Word B N G) : concat w empty = w := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp [concat, concatAux, empty, atomMul]
  | cons p t ih =>
    rcases p with ⟨i,b⟩
    change push a i (concat (b,t) empty) = _
    rw [ih]
    rfl

 theorem concat_tail_length (w v : Word B N G) :
    (concat w v).2.length = w.2.length + v.2.length := by
  rcases w with ⟨a,t⟩
  induction t generalizing a with
  | nil => simp [concat, concatAux]
  | cons p t ih =>
    rcases p with ⟨i,b⟩
    change (push a i (concat (b,t) v)).2.length = _
    simp only [push, List.length_cons, ih]
    omega

 theorem atomMul_right_injective (b : Atom B G) : Function.Injective (fun a => atomMul a b) := by
  rintro ⟨v,g⟩ ⟨w,h⟩ he
  simpa [atomMul] using he

 theorem concat_right_injective (v : Word B N G) : Function.Injective (fun w => concat w v) := by
  rintro ⟨a,t⟩ ⟨b,s⟩ h
  have hl : t.length = s.length := by
    have hh := congrArg (fun w : Word B N G => w.2.length) h
    simp only [concat_tail_length] at hh
    omega
  induction t generalizing a b s with
  | nil =>
    have hs : s = [] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
    subst s
    have he : atomMul a v.1 = atomMul b v.1 := congrArg Prod.fst h
    exact congrArg (fun a => (a, ([] : List (N × Atom B G)))) (atomMul_right_injective _ he)
  | cons p t ih =>
    cases s with
    | nil => simp at hl
    | cons q s =>
      rcases p with ⟨i,c⟩
      rcases q with ⟨j,d⟩
      have he : a = b ∧ i = j ∧ concat (c,t) v = concat (d,s) v := by
        have he := h
        simp only [concat, concatAux, push, Prod.mk.injEq, List.cons.injEq, and_assoc] at he
        exact ⟨he.1, he.2.1, Prod.ext he.2.2.1 he.2.2.2⟩
      rcases he with ⟨rfl,rfl,he⟩
      have hh := ih c d s he (by simpa using hl)
      cases hh
      rfl

 theorem leftB_concat (i : B) (w v : Word B N G) :
    leftB i (concat w v) = concat (leftB i w) v := by
  rcases w with ⟨⟨l,g⟩,t⟩
  cases t <;> rfl

 theorem leftN_concat (i : N) (w v : Word B N G) :
    leftN i (concat w v) = concat (leftN i w) v := rfl

 theorem leftG_concat (g : G) (w v : Word B N G) :
    leftG g (concat w v) = concat (leftG g w) v := by
  rcases w with ⟨⟨l,h⟩,t⟩
  cases t with
  | nil => simp [concat, concatAux, atomMul, leftG, mul_assoc]
  | cons a t => rfl

 theorem concat_noiseWord_cons (i : N) (w : List N) (v : Word B N G) :
    concat (noiseWord (i :: w)) v = leftN i (concat (noiseWord w) v) := rfl

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

def suffixEmbedding (v : Word B N G) : Space B N G →L[ℂ] Space B N G :=
  LabelHilbert.lift (fun w => concat w v) (concat_right_injective v)

@[simp] theorem suffixEmbedding_single (v w : Word B N G) (z : ℂ) :
    suffixEmbedding v (lp.single 2 w z) = lp.single 2 (concat w v) z :=
  LabelHilbert.lift_single _ _ _ _

@[simp] theorem suffixEmbedding_basis (v w : Word B N G) :
    suffixEmbedding v (basis w) = basis (concat w v) := suffixEmbedding_single v w 1

 theorem creationB_suffix (i : B) (v : Word B N G) :
    Commute (creationB i) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftB_concat i w v

 theorem creationN_suffix (i : N) (v : Word B N G) :
    Commute (creationN i) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftN_concat i w v

 theorem unitaryG_suffix (g : G) (v : Word B N G) :
    Commute (unitaryG g) (suffixEmbedding v) := by
  apply LabelHilbert.lift_commute
  intro w
  exact leftG_concat g w v

def StartsNoise (i : N) (w : Word B N G) : Prop :=
  ∃ v, w = leftN i v

def Supported (J : Set N) (w : Word B N G) : Prop :=
  ∀ p ∈ w.2, p.1 ∈ J

def StartsBackground (J : Set N) (w : Word B N G) : Prop :=
  w.1 ≠ ([],1) ∨ ∃ i ∈ J, StartsNoise i w

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_empty [DecidableEq B] [DecidableEq N] [DecidableEq G] (J : Set N) : Supported J (empty : Word B N G) := by
  simp [Supported, empty]

omit [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftB [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w) (i : B) :
    Supported J (leftB i w) := hw

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftG [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w) (g : G) :
    Supported J (leftG g w) := hw

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem supported_leftN [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G} (hw : Supported J w)
    {i : N} (hi : i ∈ J) : Supported J (leftN i w) := by
  simpa [Supported, leftN, push] using And.intro hi hw

omit [DecidableEq N] in
theorem supported_ne_empty_starts [DecidableEq N] {J : Set N} {w : Word B N G}
    (hw : Supported J w) (hne : w ≠ empty) : StartsBackground J w := by
  by_cases ha : w.1 = ([],1)
  · rcases w with ⟨a,t⟩
    cases ha
    cases t with
    | nil => exact False.elim (hne rfl)
    | cons p t =>
      rcases p with ⟨i,a⟩
      exact Or.inr ⟨i, hw (i,a) (by simp), (a,t), rfl⟩
  · exact Or.inl ha

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsBackground_concat [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : StartsBackground J w) {i : N} {v : Word B N G} (hv : StartsNoise i v) :
    StartsBackground J (concat w v) := by
  obtain ⟨v,rfl⟩ := hv
  rcases hw with (ha | ⟨j,hj,u,rfl⟩)
  · left
    rcases w with ⟨a,t⟩
    cases t with
    | nil => simpa [concat, concatAux, atomMul, leftN, push] using ha
    | cons p t => exact ha
  · exact Or.inr ⟨j,hj,concat u (leftN i v),rfl⟩

omit [DecidableEq B] [DecidableEq N] [DecidableEq G] in
theorem startsBackground_not_noise [DecidableEq B] [DecidableEq N] [DecidableEq G] {J : Set N} {w : Word B N G}
    (hw : StartsBackground J w) {i : N} (hi : i ∉ J) : ¬ StartsNoise i w := by
  rintro ⟨v,rfl⟩
  rcases hw with (hw | ⟨j,hj,u,he⟩)
  · exact hw rfl
  · have : i = j := by simpa [leftN, push, Prod.mk.injEq] using congrArg (fun w => w.2.head?.map Prod.fst) he
    exact hi (this ▸ hj)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
