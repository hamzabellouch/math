import OAI.Computability.MeanPayoff.Decoding

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

def consume {α : Type} : RandomTree α → (ℕ → Bool) → ℕ → α × ℕ
  | .leaf a, _, pos => (a, pos)
  | .coin l r, bits, pos => if bits pos then consume r bits (pos + 1)
    else consume l bits (pos + 1)

@[simp] theorem consume_bind {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (bits : ℕ → Bool) (pos : ℕ) :
    (t.bind f).consume bits pos =
      let p := t.consume bits pos
      (f p.1).consume bits p.2 := by
  induction t generalizing pos with
  | leaf a => rfl
  | coin l r il ir => simp only [bind, consume]; split <;> simp_all

@[simp] theorem consume_map {α β : Type} (t : RandomTree α) (f : α → β)
    (bits : ℕ → Bool) (pos : ℕ) :
    (t.map f).consume bits pos = (f (t.consume bits pos).1, (t.consume bits pos).2) := by
  simp only [map, consume_bind, consume]

theorem consume_path {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    pos ≤ (t.consume bits pos).2 ∧
      Path t (t.consume bits pos).1 ((t.consume bits pos).2 - pos) := by
  induction t generalizing pos with
  | leaf a => exact ⟨le_rfl, by simp only [consume, Nat.sub_self]; exact .leaf a⟩
  | coin l r il ir =>
    simp only [consume]
    split
    · obtain ⟨hp, hh⟩ := ir (pos + 1)
      exact ⟨by omega, by convert Path.right (l := l) hh using 1 ; omega⟩
    · obtain ⟨hp, hh⟩ := il (pos + 1)
      exact ⟨by omega, by convert Path.left (r := r) hh using 1 ; omega⟩

theorem consume_read {α : Type} (t : RandomTree α) (bits : ℕ → Bool) (pos : ℕ) :
    (t.consume bits pos).1 = t.read (fun k => bits (pos + k)) := by
  induction t generalizing pos with
  | leaf a => rfl
  | coin l r il ir =>
    simp only [consume, read, Nat.add_zero]
    split
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ir (pos + 1)
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using il (pos + 1)

end RandomTree

abbrev Online (α : Type) := (ℕ → Bool) → ℕ → (α × ℕ) × ℕ

namespace Online

def pure {α : Type} (a : α) : Online α := fun _ pos => ((a, 0), pos)
def map {α β : Type} (f : α → β) (t : Online α) : Online β := fun bits pos =>
  let p := t bits pos
  ((f p.1.1, p.1.2), p.2)
def bind {α β : Type} (t : Online α) (f : α → Online β) : Online β := fun bits pos =>
  let p := t bits pos
  let q := f p.1.1 bits p.2
  ((q.1.1, p.1.2 + q.1.2), q.2)
def charge {α : Type} (c : ℕ) (t : Online α) : Online α := fun bits pos =>
  let p := t bits pos
  ((p.1.1, c + p.1.2), p.2)

def uniformBelow : ℕ → Online ℕ
  | 0 => pure 0
  | k + 1 => fun bits pos =>
    let p := uniformBelow k bits (pos + 1)
    ((if bits pos then p.1.1 + 2 ^ k else p.1.1, 0), p.2)

def trials {α : Type} (t : Online α) : ℕ → Online (List α)
  | 0 => pure []
  | J + 1 => t.bind fun a => (trials t J).map (a :: ·)

def traverse {α β : Type} (f : α → Online β) : List α → Online (List β)
  | [] => pure []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

end Online

namespace Counted

def online {α : Type} (t : Counted α) : Online α := t.tree.consume

@[simp] theorem online_pure {α : Type} (a : α) : (Counted.pure a).online = Online.pure a := rfl
@[simp] theorem online_map {α β : Type} (t : Counted α) (f : α → β) :
    (t.map f).online = Online.map f t.online := by
  funext bits pos
  simp only [online, map, RandomTree.consume_map, Online.map]
@[simp] theorem online_bind {α β : Type} (t : Counted α) (f : α → Counted β) :
    (t.bind f).online = Online.bind t.online (fun a => (f a).online) := by
  funext bits pos
  simp only [online, bind, RandomTree.consume_bind, RandomTree.consume_map, Online.bind]
@[simp] theorem online_charge {α : Type} (c : ℕ) (t : Counted α) :
    (t.charge c).online = Online.charge c t.online := by
  funext bits pos
  simp only [online, charge, RandomTree.consume_map, Online.charge]

@[simp] theorem online_uniform (k : ℕ) :
    (Counted.lift (RandomTree.uniformBelow k)).online = Online.uniformBelow k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext bits pos
    have h := congrFun (congrFun ih bits) (pos + 1)
    simp only [online, lift, RandomTree.consume_map] at h
    simp only [online, lift, RandomTree.uniformBelow, RandomTree.consume_map, RandomTree.consume,
      Online.uniformBelow]
    split <;> rw [← h]

@[simp] theorem online_trials {α : Type} (t : Counted α) (J : ℕ) :
    (t.trials J).online = Online.trials t.online J := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [trials, Online.trials, online_bind, online_map, ih]

@[simp] theorem online_traverse {α β : Type} (f : α → Counted β) (as : List α) :
    (Counted.traverse f as).online = Online.traverse (fun a => (f a).online) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [traverse, Online.traverse, online_bind, online_map, ih]

end Counted


def SolveBox.repeatedOnline {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : Online (BoxVector I)) (J : ℕ) : Online (BoxVector I) :=
  (Online.trials t J).map I.medianBox

namespace OnlineAlgorithm

abbrev LowerSolver {n Bmax : ℕ} (P : Budgets n) :=
  (Q : Budgets n) → parameterRank Q.parameter < parameterRank P.parameter →
    (I : SolveBox n Bmax) → Online (BoxVector I)

def centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) : Online (BoxVector I) :=
  let K := I.narrowCentered hB q.val
  (K.repeatedOnline (lower P.reduceK (P.reduceK_rank hR) K) (globalJ n Bmax)).bind fun r₁ =>
  (K.repeatedOnline (lower P.reduceM (P.reduceM_rank hR) K) (globalJ n Bmax)).map fun r₂ =>
    I.averageClipped r₁.val r₂.val

def centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    ℕ → BoxVector I → Online (List (BoxVector I))
  | 0, q => Online.pure [q]
  | t + 1, q =>
    (centerUpdate P hR lower I hB q).bind fun q' =>
    (centerSteps P hR lower I hB t q').map (q :: ·)

def orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (qs : List (BoxVector I)) (child : BoxVector I → Online (Orientation P)) :
    Online (Orientation P) :=
  let H := PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  let N := NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  if hH : 1 / 2 < P.measure H then
    Online.pure ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else if hN : 1 / 2 < P.measure N then
    Online.pure ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else
    (Online.uniformBelow (sampleExponent Bmax)).bind fun j =>
      (child (qs.getD j I.midpoint)).map fun O =>
        ⟨O.chooseY, O.exceptions ++ [⟨H, le_of_not_gt hH⟩, ⟨N, le_of_not_gt hN⟩]⟩

def orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    Online (Orientation P) :=
  if hB : I.width ≤ 128 * globalS Bmax then
    Online.pure (orientBase G P I)
  else
    let hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind fun qs =>
      orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val))
termination_by I.width
decreasing_by exact I.E_smaller

def orientPlus {n : ℕ} {P : Budgets n} (t : Online (Orientation P)) (J : ℕ) :
    Online (Orientation P) :=
  (Online.trials t J).map combineOrientations

def tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : Online (InnerBox I) :=
  (I.repeatedOnline (lower P.reduceK (P.reduceK_rank hR) I) (globalJ n Bmax)).bind fun r₁ =>
  if _h₁ : ∃ i, (I.delta : ℤ) ≤ r₁.val i - I.a i then
    let K := I.withFloor r₁
    (tighten P hR lower K hB).map fun T =>
      ⟨T.box, T.width_eq, r₁.property.1.trans T.floor_le, T.ceiling_le⟩
  else
    (I.repeatedOnline (lower P.reduceM (P.reduceM_rank hR) I) (globalJ n Bmax)).bind fun r₂ =>
    if _h₂ : ∃ i, (I.delta : ℤ) ≤ I.b i - r₂.val i then
      let K := I.withCeiling r₂
      (tighten P hR lower K hB).map fun T =>
        ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r₂.property.2⟩
    else Online.pure ⟨I, rfl, le_refl _, le_refl _⟩
termination_by volume I.b I.a
decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := _h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := _h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

def finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : Online (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : Online (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    Online (BoxVector I) :=
  if O.chooseY then
    (Online.traverse (fun H : SmallSet P =>
      I.repeatedOnline (lower (P.reweightM H.val)
        (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    up.map fun p => rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p)
  else
    (Online.traverse (fun H : SmallSet P =>
      I.repeatedOnline (lower (P.reweightK H.val)
        (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    lo.map fun p => rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p)

def solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) : Online (BoxVector I) :=
  Online.charge 1 <|
  if hB : I.width ≤ 128 * globalS Bmax then Online.pure (I.exactVector G)
  else
    (tighten P hR lower I (lt_of_not_ge hB)).bind fun T =>
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by rw [T.width_eq]; omega
    let c := K.C
    have hc : 0 < c := K.C_positive
    have hcsmall : c < K.width := K.C_smaller hK
    (orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind fun O =>
    (finishChoice G P hR lower K hK O
      (solveWidth G P hR lower (K.capHigh c hc hcsmall.le))
      (solveWidth G P hR lower (K.capLow c hc hcsmall.le))).map T.include
termination_by I.width
decreasing_by
  all_goals
    change c < I.width
    rw [← T.width_eq]
    exact hcsmall

def solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    Online (BoxVector I) :=
  if hR : P.parameter < 1 then Online.charge 1 (Online.pure (I.smallVector P))
  else solveWidth G P (le_of_not_gt hR) (fun Q _ K => solve G Q K) I
termination_by parameterRank P.parameter

end OnlineAlgorithm
end MeanPayoff
end

end OAI
