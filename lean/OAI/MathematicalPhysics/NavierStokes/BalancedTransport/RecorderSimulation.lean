import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.BoxCoding

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

theorem inverse_base_pos : 0 < (base Q Γ : ℝ)⁻¹ :=
  inv_pos.mpr (Nat.cast_pos.mpr base_pos)

theorem inverse_base_le_one : (base Q Γ : ℝ)⁻¹ ≤ 1 := by
  have h : (1 : ℝ) ≤ base Q Γ := by exact_mod_cast base_pos (Q := Q) (Γ := Γ)
  exact inv_le_one_of_one_le₀ h

theorem digit_unit_bound (a : Letter Q Γ) :
    (base Q Γ : ℝ)⁻¹ * ((digit a : ℝ) + 1) ≤ 1 := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_one (Nat.cast_pos.mpr base_pos)).mpr (digit_upper a).le

def Configuration.stacks (c : Configuration Q Γ) : Fin 3 → Stream' (Letter Q Γ) :=
  ![c.left, c.right, c.history]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]
variable [DecidableEq Q]

def Configuration.code (M : Machine Q Γ) (c : Configuration Q Γ) : Space :=
  Coding.codedPoint digit (Coding.origin (placement M c.control)) c.stacks

def Instruction.fullMap (M : Machine Q Γ) (inst : Instruction Q Γ) : Space → Space :=
  Coding.boxMap (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
    (Coding.origin (placement M inst.sourceControl))
    (Coding.origin (placement M inst.targetControl)) inst.sourcePrefixes inst.targetPrefixes

theorem Instruction.fullMap_code (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    inst.fullMap M ((inst.source t).code M) = (inst.target t).code M := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  have ht : (inst.target t).stacks = fun i => inst.targetPrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  unfold fullMap Configuration.code
  rw [hs, ht]
  exact Coding.boxMap_codedPoint (Nat.ne_of_gt base_pos) _ _ _ _ _ _

theorem Instruction.source_code_mem (M : Machine Q Γ) (inst : Instruction Q Γ)
    (t : Tails Q Γ) :
    (inst.source t).code M ∈
      inst.sourceBox (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ)) (placement M) := by
  let tails : Fin 3 → Stream' (Letter Q Γ) := ![t.left, t.right, t.history]
  have hs : (inst.source t).stacks = fun i => inst.sourcePrefixes i ++ₛ tails i := by
    funext i
    fin_cases i <;> rfl
  change Coding.codedPoint digit _ (inst.source t).stacks ∈ _
  rw [hs]
  exact Coding.codedPoint_mem_box _ _ _ _

theorem compiled_boxes_disjoint [DecidableEq Γ] (M : Machine Q Γ) :
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) ∧
    ((table M : Set (Row Q Γ)).Pairwise fun a b =>
      Disjoint ((a.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))
      ((b.instruction M).targetBox (base Q Γ : ℝ)⁻¹
        (fun c => (digit c : ℝ)) (placement M))) := by
  constructor
  · intro a ha b hb hab
    exact source_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M)
      ((mem_table M a).mp ha) ((mem_table M b).mp hb) hab
  · intro a _ b _ hab
    exact target_boxes_disjoint M inverse_base_pos _ (fun a => (digit_pos a).le)
      digit_unit_bound digit_gap (placement M) (placement_injective M) hab

omit [DecidableEq Q] in

theorem prefix_halfWidth (w : List (Letter Q Γ)) :
    0 < (base Q Γ : ℝ)⁻¹ ^ w.length / 2 ∧
    (base Q Γ : ℝ)⁻¹ ^ w.length / 2 ≤ 1 / 2 := by
  have hp := pow_pos (inverse_base_pos (Q := Q) (Γ := Γ)) w.length
  have hle := pow_le_one₀ (inverse_base_pos (Q := Q) (Γ := Γ)).le
    (inverse_base_le_one (Q := Q) (Γ := Γ)) (n := w.length)
  constructor <;> linarith

theorem nonhalt_box_guard (M : Machine Q Γ) (s : Control Q) (hs : s ≠ .ready M.halt)
    (u : Fin 3 → List (Letter Q Γ)) {x : Space}
    (hx : x ∈ Coding.box (base Q Γ : ℝ)⁻¹ (fun a => (digit a : ℝ))
      (Coding.origin (placement M s)) u) : 4 ≤ x 0 := by
  have hl := (Coding.interval_subset_unit inverse_base_pos _ (fun a => (digit_pos a).le)
    digit_unit_bound (u 0) (hx 0)).1
  have hp : (1 : ℝ) ≤ placement M s := by exact_mod_cast placement_positive M s hs
  simp only [Coding.origin, Matrix.cons_val_zero] at hl
  linarith

omit [Fintype Q] [Fintype Γ] [DecidableEq Q] in

theorem Row.sourceControl_ne_halt (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) :
    (a.instruction M).sourceControl ≠ .ready M.halt := by
  cases a <;> simp_all [Row.valid, Row.instruction]

theorem source_box_guard (M : Machine Q Γ) (a : Row Q Γ) (ha : a.valid M) {x : Space}
    (hx : x ∈ (a.instruction M).sourceBox (base Q Γ : ℝ)⁻¹
      (fun c => (digit c : ℝ)) (placement M)) : 4 ≤ x 0 :=
  nonhalt_box_guard M _ (a.sourceControl_ne_halt M ha) _ hx

theorem code_mem_observer_iff (M : Machine Q Γ) (c : Configuration Q Γ) :
    c.code M ∈ observer ↔ c.control = .ready M.halt := by
  have hi : ∀ i : Fin 3, Coding.stream digit (c.stacks i) ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    exact Coding.stream_mem_interior base_pos digit digit_pos digit_upper _
  constructor
  · intro h
    by_contra hc
    have hp : (1 : ℝ) ≤ placement M c.control := by
      exact_mod_cast placement_positive M c.control hc
    have hi₀ := hi 0
    have hh : c.code M 0 < 2 := (h 0 (Set.mem_univ _)).2
    simp only [Configuration.code, Coding.codedPoint, Coding.origin, Matrix.cons_val_zero] at hh
    linarith [hi₀.1]
  · intro hc i _
    have ho : Coding.origin (placement M c.control) i = 0 := by
      rw [hc, placement_halt]
      fin_cases i <;> simp [Coding.origin]
    change -1 < Coding.origin (placement M c.control) i + Coding.stream digit (c.stacks i) ∧
      Coding.origin (placement M c.control) i + Coding.stream digit (c.stacks i) < 2
    rw [ho, zero_add]
    constructor <;> linarith [(hi i).1, (hi i).2]

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

structure Checkpoint (Q Γ : Type*) where
  state : Q
  left : Stream' Γ
  current : Γ
  right : List Γ
  history : Stream' (Letter Q Γ)

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control

def expand (M : Machine Q Γ) (c : Checkpoint Q Γ) : Configuration Q Γ :=
  ⟨ready c.state, Stream'.map work c.left,
    work c.current :: (c.right.map work ++ₛ (boundary :: Stream'.const (work M.blank))),
    c.history⟩

def next (M : Machine Q Γ) (c : Checkpoint Q Γ) : Checkpoint Q Γ :=
  let v := M.transition c.state c.current
  match v.move with
  | .stay => ⟨v.state, c.left, v.write, c.right, record (.stay c.state c.current) :: c.history⟩
  | .left => ⟨v.state, c.left.tail, c.left.head, v.write :: c.right,
      record (.left c.state c.current c.left.head) :: c.history⟩
  | .right =>
      match c.right with
      | [] => ⟨v.state, v.write :: c.left, M.blank, [],
          record (.extend c.state c.current) :: c.history⟩
      | List.cons a w => ⟨v.state, v.write :: c.left, a, w,
          record (.right c.state c.current a) :: c.history⟩

def WorkStep (M : Machine Q Γ) (c d : Checkpoint Q Γ) : Prop :=
  c.state ≠ M.halt ∧ d = c.next M

theorem next_exec (M : Machine Q Γ) (c : Checkpoint Q Γ) (hc : c.state ≠ M.halt) :
    Exec M (2 * (c.right.length + 1) + 2) (c.expand M) ((c.next M).expand M) := by
  cases hm : (M.transition c.state c.current).move with
  | stay =>
      simpa [next, hm, expand] using
        checkpoint_stay M c.state hc c.current hm c.right (Stream'.map work c.left) c.history
  | left =>
      have h := checkpoint_left M c.state hc c.current c.left.head hm c.right
        (Stream'.map work c.left.tail) c.history
      have hl : (work c.left.head :: Stream'.map work c.left.tail : Stream' (Letter Q Γ)) =
          Stream'.map work c.left := by
        funext n
        cases n <;> rfl
      simpa only [next, hm, expand, List.map_cons, Stream'.appendStream', hl] using h
  | right =>
      cases hw : c.right with
      | nil =>
          simpa [next, hm, expand, hw, Stream'.map_cons] using
            checkpoint_extend M c.state hc c.current hm (Stream'.map work c.left) c.history
      | cons a w =>
          simpa [next, hm, expand, hw, Stream'.map_cons, Stream'.appendStream', Nat.add_assoc] using
            checkpoint_right M c.state hc c.current a hm w (Stream'.map work c.left) c.history

theorem work_execution (M : Machine Q Γ) {c d : Checkpoint Q Γ}
    (h : Relation.ReflTransGen (WorkStep M) c d) :
    ∃ n, Exec M n (c.expand M) (d.expand M) := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | @tail d e hd hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨hnh, rfl⟩ := hstep
      exact ⟨_, hn.trans (next_exec M d hnh)⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}
open Stream' Letter Control

theorem no_step_from_halt (M : Machine Q Γ) {c d : Configuration Q Γ}
    (hc : c.control = .ready M.halt) : ¬Step M c d := by
  rintro ⟨r, hr, t, rfl, _⟩
  exact r.sourceControl_ne_halt M hr hc

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder.Exec
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ] {M : Machine Q Γ}

theorem cancel_to_terminal {n m : ℕ} {c d e : Configuration Q Γ}
    (h : Exec M n c d) (g : Exec M m c e) (hd : ∀ f, ¬Step M d f) :
    ∃ k, n = m + k ∧ Exec M k e d := by
  induction g generalizing n with
  | refl => exact ⟨n, by omega, h⟩
  | @cons m c b e hcb hbe ih =>
      cases h with
      | refl => exact False.elim (hd b hcb)
      | @cons n c a d hca had =>
          have he := step_deterministic M hca hcb
          subst a
          obtain ⟨k, hk, he⟩ := ih had
          exact ⟨k, by omega, he⟩

end BalancedTransport.Recorder.Exec
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
variable [DecidableEq Q] [DecidableEq Γ]

theorem halt_reflection (M : Machine Q Γ) {n : ℕ} {c : Checkpoint Q Γ}
    {d : Configuration Q Γ} (h : Exec M n (c.expand M) d)
    (hd : d.control = .ready M.halt) :
    ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  induction n using Nat.strong_induction_on generalizing c d with
  | h n ih =>
      by_cases hc : c.state = M.halt
      · exact ⟨c, .refl, hc⟩
      · obtain ⟨k, hk, hkd⟩ := h.cancel_to_terminal (next_exec M c hc)
          (fun f => no_step_from_halt M hd)
        have hkn : k < n := by omega
        obtain ⟨e, he, hehalt⟩ := ih k hkn hkd hd
        exact ⟨e, (Relation.ReflTransGen.single (show WorkStep M c (c.next M) from
          ⟨hc, rfl⟩)).trans he, hehalt⟩

theorem halting_iff (M : Machine Q Γ) (c : Checkpoint Q Γ) :
    (∃ n d, Exec M n (c.expand M) d ∧ d.control = .ready M.halt) ↔
      ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  constructor
  · rintro ⟨n, d, h, hd⟩
    exact halt_reflection M h hd
  · rintro ⟨e, h, he⟩
    obtain ⟨n, hn⟩ := work_execution M h
    exact ⟨n, e.expand M, hn, by simpa [expand] using he⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def rationalWord {B : ℕ} (digit : S → Fin B) : List S → ℚ
  | [] => 0
  | a :: w => (B : ℚ)⁻¹ * ((digit a : ℚ) + rationalWord digit w)

theorem rationalWord_cast {B : ℕ} (digit : S → Fin B) (w : List S) :
    (rationalWord digit w : ℝ) = word (B : ℝ)⁻¹ (fun a => (digit a : ℝ)) w := by
  induction w with
  | nil => simp [rationalWord]
  | cons a w ih => simp [rationalWord, word, ih]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

theorem stream_const {B : ℕ} (hB : 1 < B) (digit : S → Fin B) (a : S) :
    stream digit (Stream'.const a) = (digit a : ℝ) / ((B : ℝ) - 1) := by
  have hs : (a :: Stream'.const a : Stream' S) = Stream'.const a := by
    funext n
    cases n <;> rfl
  have he := stream_cons digit a (Stream'.const a)
  rw [hs, mul_comm, ← div_eq_mul_inv] at he
  have hB' : (1 : ℝ) < B := by exact_mod_cast hB
  have hn : (B : ℝ) ≠ 0 := by linarith
  have hsub : (B : ℝ) - 1 ≠ 0 := by linarith
  apply (eq_div_iff hsub).mpr
  have he' := (eq_div_iff hn).mp he
  nlinarith only [he']

def rationalTailCode {B : ℕ} (digit : S → Fin B) (w : List S) (a : S) : ℚ :=
  rationalWord digit w + (B : ℚ)⁻¹ ^ w.length * ((digit a : ℚ) / ((B : ℚ) - 1))

theorem rationalTailCode_cast {B : ℕ} (hB : 1 < B) (digit : S → Fin B)
    (w : List S) (a : S) :
    (rationalTailCode digit w a : ℝ) = stream digit (w ++ₛ Stream'.const a) := by
  rw [stream_append, stream_const hB]
  simp [rationalTailCode, prefixPoint, rationalWord_cast]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter

def initial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Checkpoint Q Γ :=
  ⟨q₀, Stream'.const M.blank, w.headD M.blank, w.tail, Stream'.const (work M.blank)⟩

theorem initial_work_block (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    (initial M q₀ w).current :: (initial M q₀ w).right =
      if w = [] then [M.blank] else w := by
  cases w <;> simp [initial]

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter
variable [Fintype Q] [Fintype Γ] [DecidableEq Q]

omit [DecidableEq Q] in

theorem base_gt_one : 1 < base Q Γ := by
  have hh : 0 < Fintype.card (Letter Q Γ) := Fintype.card_pos_iff.mpr ⟨.boundary⟩
  dsimp [base]
  omega

def rationalInitial (M : Machine Q Γ) (q₀ : Q) (w : List Γ) : Fin 3 → ℚ :=
  let b := Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) [] (work M.blank : Letter Q Γ)
  let v : List (Letter Q Γ) := work (w.headD M.blank) :: (w.tail.map work ++ [boundary])
  ![4 * (placement M (.ready q₀) : ℚ) + b,
    Coding.rationalTailCode (digit (Q := Q) (Γ := Γ)) v (work M.blank), b]

theorem rationalInitial_cast (M : Machine Q Γ) (q₀ : Q) (w : List Γ) :
    rationalSpace (rationalInitial M q₀ w) = ((initial M q₀ w).expand M).code M := by
  have hb := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit [] (work M.blank : Letter Q Γ)
  have hr := Coding.rationalTailCode_cast (base_gt_one (Q := Q) (Γ := Γ))
    digit (work (w.headD M.blank) :: (w.tail.map work ++ [boundary]))
    (work M.blank : Letter Q Γ)
  have hr' : (Coding.rationalTailCode (digit (Q := Q) (Γ := Γ))
      (work (w.headD M.blank) :: (w.tail.map work ++ [boundary])) (work M.blank) : ℝ) =
      Coding.stream (digit (Q := Q) (Γ := Γ)) (work (w.headD M.blank) ::
        (w.tail.map work ++ₛ (boundary :: Stream'.const (work M.blank)))) := by
    simpa only [Stream'.appendStream', Stream'.append_append_stream] using hr
  simp only [Stream'.nil_append_stream] at hb
  funext i
  fin_cases i
  · simp [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial, Stream'.map_const, hb]
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hr'
  · simpa [rationalSpace, rationalInitial, Configuration.code, Configuration.stacks,
      Coding.codedPoint, Coding.origin, expand, initial] using hb

end BalancedTransport.Recorder.Checkpoint
end

end OAI
