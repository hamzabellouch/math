import OAI.Algebra.FormulaHitting.BitArithmetic
import OAI.Algebra.FormulaHitting.ProgramCost

namespace OAI

namespace NCHitting.BitRefinement

open BitModel

theorem width_pos (a : ℕ) : 0 < width a := by unfold width; omega

theorem width_mono {a b : ℕ} (h : a ≤ b) : width a ≤ width b :=
  Nat.add_le_add_right (Nat.size_le_size h) 1

theorem width_add_le (a b : ℕ) : width (a+b) ≤ width a + width b := by
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : 2^a.size ≤ 2^(a.size+b.size) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hpb : 2^b.size ≤ 2^(a.size+b.size) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hp : a+b < 2^(a.size+b.size+1) := by rw [pow_succ]; omega
  have hs := Nat.size_le.mpr hp
  unfold width
  omega

theorem addCost_ge_widths (a b : ℕ) : width a + width b ≤ addCost a b := by
  unfold addCost
  omega

theorem mulCost_ge_widths (a b : ℕ) : width a + width b ≤ mulCost a b := by
  have ha := width_pos a
  have hb := width_pos b
  unfold mulCost
  nlinarith

theorem powerRun_count_le (base k : ℕ) : k+2 ≤ (powerRun base k).cost := by
  induction k with
  | zero => simp [powerRun, width]
  | succ k ih => simp only [powerRun]; omega

theorem powerRun_width_le (base k : ℕ) :
    width (base^k) ≤ (powerRun base k).cost := by
  induction k with
  | zero => simp [powerRun, width]
  | succ k ih =>
    have hw := BitModel.width_mul_le (base^k) base
    have hc := mulCost_ge_widths (base^k) base
    simp only [powerRun, powerRun_value, pow_succ]
    omega

theorem listBits_mem_le {a : ℕ} {env : List ℕ} (h : a ∈ env) :
    width a ≤ listBits env := by
  induction env with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [listBits]
    · have hi := ih h
      change width a ≤ width x + listBits xs
      omega

theorem expr_width_le (env : List ℕ) (e : Expr) :
    width (e.run env).value ≤ (e.run env).cost + listBits env := by
  cases e with
  | literal a => simp only [Expr.run]; omega
  | read i =>
    cases h : env[i]? with
    | none => simp only [Expr.run, h, Option.getD_none, width, Nat.size_zero]; omega
    | some a =>
      have hw := listBits_mem_le (List.mem_of_getElem? h)
      simp only [Expr.run, h, Option.getD_some]
      omega
  | add a b =>
    have hw := width_add_le (a.run env).value (b.run env).value
    have hc := addCost_ge_widths (a.run env).value (b.run env).value
    simp only [Expr.run]
    omega
  | sub a b =>
    have hw := width_mono (Nat.sub_le (a.run env).value (b.run env).value)
    have hc := addCost_ge_widths (a.run env).value (b.run env).value
    simp only [Expr.run]
    omega
  | mul a b =>
    have hw := BitModel.width_mul_le (a.run env).value (b.run env).value
    have hc := mulCost_ge_widths (a.run env).value (b.run env).value
    simp only [Expr.run]
    omega
  | power a b =>
    have hw := powerRun_width_le (a.run env).value (b.run env).value
    simpa only [Expr.run, powerRun_value] using hw.trans
      (by omega : (powerRun (a.run env).value (b.run env).value).cost ≤
        (a.run env).cost + (b.run env).cost +
          (powerRun (a.run env).value (b.run env).value).cost + 1 + listBits env)
  | less a b =>
    simp only [Expr.run]
    split <;> simp [width, compareCost] <;> omega
  | equal a b =>
    simp only [Expr.run]
    split <;> simp [width, compareCost] <;> omega
  | odd a =>
    have h : (a.run env).value % 2 ≤ 1 := by omega
    have hw := width_mono h
    simp only [Expr.run]
    have : width 1 = 2 := rfl
    omega

inductive Step where
  | writeNat : ℕ → Step
  | read : List ℕ → ℕ → Step
  | add : ℕ → ℕ → Step
  | sub : ℕ → ℕ → Step
  | mul : ℕ → ℕ → Step
  | less : ℕ → ℕ → Step
  | equal : ℕ → ℕ → Step
  | odd : ℕ → Step
  | emit : RationalCode → Step
  | copy : List RationalCode → Step
  | input : List ℕ → Step
  | control : Step
  deriving DecidableEq

def Step.tariff : Step → ℕ
  | .writeNat n => width n
  | .read env i => width i + listBits (env.take (i+1)) + 1
  | .add a b | .sub a b => addCost a b
  | .mul a b => mulCost a b
  | .less a b | .equal a b => compareCost a b
  | .odd _ => 2
  | .emit e => e.bits + 2
  | .copy es => outputBits es
  | .input env => listBits env
  | .control => 1

def Step.steps : Step → ℕ
  | .add a b => (BitArithmetic.addNat a b).steps
  | .sub a b => (BitArithmetic.subNat a b).steps
  | .mul a b => (BitArithmetic.mulNat a b).steps
  | .less a b => (BitArithmetic.lessNat a b).steps
  | .equal a b => (BitArithmetic.equalNat a b).steps
  | s => s.tariff

theorem self_le_square (a : ℕ) : a ≤ a^2 := by
  cases a with
  | zero => simp
  | succ a => nlinarith

theorem Step.steps_le (s : Step) : s.steps ≤ s.tariff^2 := by
  cases s with
  | add a b => exact BitArithmetic.addNat_steps a b
  | sub a b => exact BitArithmetic.subNat_steps a b
  | mul a b => exact BitArithmetic.mulNat_steps a b
  | less a b => exact BitArithmetic.lessNat_steps a b
  | equal a b => exact BitArithmetic.equalNat_steps a b
  | _ => exact self_le_square _

abbrev Trace := List Step
def Trace.steps (t : Trace) : ℕ := (t.map Step.steps).sum

def powerTrace (base : ℕ) : ℕ → Trace
  | 0 => [.equal 0 0, .control, .writeNat 1]
  | k+1 => [.equal (k+1) 0, .control, .sub (k+1) 1] ++ powerTrace base k ++
      [.mul (base^k) base]

def exprTrace (env : List ℕ) : Expr → Trace
  | .literal n => [.writeNat n, .control]
  | .read i => [.read env i]
  | .add a b => exprTrace env a ++ exprTrace env b ++
      [.add (a.run env).value (b.run env).value, .control]
  | .sub a b => exprTrace env a ++ exprTrace env b ++
      [.sub (a.run env).value (b.run env).value, .control]
  | .mul a b => exprTrace env a ++ exprTrace env b ++
      [.mul (a.run env).value (b.run env).value, .control]
  | .less a b => exprTrace env a ++ exprTrace env b ++
      [.less (a.run env).value (b.run env).value, .control]
  | .equal a b => exprTrace env a ++ exprTrace env b ++
      [.equal (a.run env).value (b.run env).value, .control]
  | .power a b => exprTrace env a ++ exprTrace env b ++
      powerTrace (a.run env).value (b.run env).value ++ [.control]
  | .odd a => exprTrace env a ++ [.odd (a.run env).value]

def programTrace (env : List ℕ) : Program → Trace
  | .skip => [.control]
  | .emit s a b => exprTrace env s ++ exprTrace env a ++ exprTrace env b ++
      [.emit ⟨decide ((s.run env).value % 2 = 1), (a.run env).value, (b.run env).value⟩]
  | .sequence p q => programTrace env p ++ programTrace env q ++
      [.copy (p.run env).output, .control]
  | .branch e p q => exprTrace env e ++ [.equal (e.run env).value 0, .control] ++
      (if (e.run env).value = 0 then programTrace env q else programTrace env p)
  | .loop e p => exprTrace env e ++
      ((List.range (e.run env).value).flatMap fun i =>
        [.equal i (e.run env).value, .writeNat i] ++ programTrace (i::env) p ++
          [.add i 1, .copy (p.run (i::env)).output, .control]) ++
      [.equal (e.run env).value (e.run env).value, .control]

inductive PowerExecution (base : ℕ) : ℕ → ℕ → Trace → Prop where
  | zero : PowerExecution base 0 1 [.equal 0 0, .control, .writeNat 1]
  | succ {k v t} (h : PowerExecution base k v t)
      (hc : (BitArithmetic.equalNat (k+1) 0).bit = false)
      (hd : (BitArithmetic.subNat (k+1) 1).bits = k.bits) :
      PowerExecution base (k+1) (BitArithmetic.value (BitArithmetic.mulNat v base).bits)
        ([.equal (k+1) 0, .control, .sub (k+1) 1] ++ t ++ [.mul v base])

inductive ExprExecution (env : List ℕ) : Expr → ℕ → Trace → Prop where
  | literal (n) : ExprExecution env (.literal n) n [.writeNat n, .control]
  | read (i) : ExprExecution env (.read i) (env[i]?.getD 0) [.read env i]
  | add {a b x y tx ty} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty) :
      ExprExecution env (.add a b) (BitArithmetic.value (BitArithmetic.addNat x y).bits)
        (tx ++ ty ++ [.add x y, .control])
  | sub {a b x y tx ty} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty) :
      ExprExecution env (.sub a b) (BitArithmetic.value (BitArithmetic.subNat x y).bits)
        (tx ++ ty ++ [.sub x y, .control])
  | mul {a b x y tx ty} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty) :
      ExprExecution env (.mul a b) (BitArithmetic.value (BitArithmetic.mulNat x y).bits)
        (tx ++ ty ++ [.mul x y, .control])
  | less {a b x y tx ty} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty) :
      ExprExecution env (.less a b) (BitArithmetic.lessNat x y).bit.toNat
        (tx ++ ty ++ [.less x y, .control])
  | equal {a b x y tx ty} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty) :
      ExprExecution env (.equal a b) (BitArithmetic.equalNat x y).bit.toNat
        (tx ++ ty ++ [.equal x y, .control])
  | power {a b x y v tx ty tp} (ha : ExprExecution env a x tx) (hb : ExprExecution env b y ty)
      (hp : PowerExecution x y v tp) :
      ExprExecution env (.power a b) v (tx ++ ty ++ tp ++ [.control])
  | odd {a x tx} (ha : ExprExecution env a x tx) :
      ExprExecution env (.odd a) (BitArithmetic.oddNat x).bit.toNat (tx ++ [.odd x])

inductive ProgramExecution : List ℕ → Program → List RationalCode → Trace → Prop where
  | skip (env) : ProgramExecution env .skip [] [.control]
  | emit {env s a b x y z tx ty tz}
      (hs : ExprExecution env s x tx) (ha : ExprExecution env a y ty)
      (hb : ExprExecution env b z tz) :
      ProgramExecution env (.emit s a b) [⟨(BitArithmetic.oddNat x).bit,y,z⟩]
        (tx ++ ty ++ tz ++ [.emit ⟨(BitArithmetic.oddNat x).bit,y,z⟩])
  | sequence {env p q x y tx ty}
      (hp : ProgramExecution env p x tx) (hq : ProgramExecution env q y ty) :
      ProgramExecution env (.sequence p q) (x++y) (tx++ty++[.copy x,.control])
  | branch {env e p q x tx output tp}
      (he : ExprExecution env e x tx)
      (hp : ProgramExecution env (if x=0 then q else p) output tp)
      (hc : (BitArithmetic.equalNat x 0).bit = decide (x=0)) :
      ProgramExecution env (.branch e p q) output (tx++[.equal x 0,.control]++tp)
  | loop {env e p b te} (he : ExprExecution env e b te)
      (outputs : ℕ → List RationalCode) (traces : ℕ → Trace)
      (hbody : ∀ i < b, ProgramExecution (i::env) p (outputs i) (traces i))
      (htest : ∀ i < b, (BitArithmetic.equalNat i b).bit = false)
      (hstep : ∀ i < b, (BitArithmetic.addNat i 1).bits = (i+1).bits)
      (hfinal : (BitArithmetic.equalNat b b).bit = true) :
      ProgramExecution env (.loop e p) ((List.range b).flatMap outputs)
        (te ++ ((List.range b).flatMap fun i =>
          [.equal i b,.writeNat i] ++ traces i ++ [.add i 1,.copy (outputs i),.control]) ++
          [.equal b b,.control])

def Exec (p : Program) (inputs : List ℕ) (output : List RationalCode) (steps : ℕ) : Prop :=
  ∃ t, ProgramExecution inputs p output t ∧ steps = Trace.steps (.input inputs :: t)

theorem powerTrace_correct (base k : ℕ) : PowerExecution base k (base^k) (powerTrace base k) := by
  induction k with
  | zero => exact PowerExecution.zero
  | succ k ih =>
    simpa [powerTrace, BitArithmetic.mulNat_value, BitArithmetic.value_bits, pow_succ] using
      PowerExecution.succ ih (by simp [BitArithmetic.equalNat_value])
        (by simp [BitArithmetic.subNat_value])

theorem exprTrace_correct (env : List ℕ) (e : Expr) :
    ExprExecution env e (e.run env).value (exprTrace env e) := by
  induction e with
  | literal n => exact ExprExecution.literal n
  | read i => exact ExprExecution.read i
  | add a b ha hb =>
    simpa [exprTrace, Expr.run, BitArithmetic.addNat_value, BitArithmetic.value_bits] using ExprExecution.add ha hb
  | sub a b ha hb =>
    simpa [exprTrace, Expr.run, BitArithmetic.subNat_value, BitArithmetic.value_bits] using ExprExecution.sub ha hb
  | mul a b ha hb =>
    simpa [exprTrace, Expr.run, BitArithmetic.mulNat_value, BitArithmetic.value_bits] using ExprExecution.mul ha hb
  | less a b ha hb =>
    by_cases h : (a.run env).value < (b.run env).value <;>
      simpa [exprTrace, Expr.run, BitArithmetic.lessNat_value, h] using ExprExecution.less ha hb
  | equal a b ha hb =>
    by_cases h : (a.run env).value = (b.run env).value <;>
      simpa [exprTrace, Expr.run, BitArithmetic.equalNat_value, h] using ExprExecution.equal ha hb
  | power a b ha hb =>
    simpa [exprTrace, Expr.run] using ExprExecution.power ha hb
      (powerTrace_correct (a.run env).value (b.run env).value)
  | odd a ha => simpa [exprTrace, Expr.run, BitArithmetic.oddNat_value] using ExprExecution.odd ha

theorem programTrace_correct (env : List ℕ) (p : Program) :
    ProgramExecution env p (p.run env).output (programTrace env p) := by
  induction p generalizing env with
  | skip => exact ProgramExecution.skip env
  | emit s a b =>
    simpa only [programTrace, Program.run, BitArithmetic.oddNat_eq] using
      (ProgramExecution.emit (exprTrace_correct env s)
        (exprTrace_correct env a) (exprTrace_correct env b))
  | sequence p q hp hq => exact ProgramExecution.sequence (hp env) (hq env)
  | branch e p q hp hq =>
    have hchoice : ProgramExecution env (if (e.run env).value=0 then q else p)
        (if (e.run env).value=0 then (q.run env).output else (p.run env).output)
        (if (e.run env).value=0 then programTrace env q else programTrace env p) := by
      split <;> [exact hq env; exact hp env]
    simpa only [Program.run, programTrace, apply_ite] using
      ProgramExecution.branch (exprTrace_correct env e) hchoice
        (BitArithmetic.equalNat_value _ _)
  | loop e p hp =>
    simpa only [Program.run, programTrace, List.flatMap_map] using
      ProgramExecution.loop (exprTrace_correct env e)
        (fun i => (p.run (i::env)).output) (fun i => programTrace (i::env) p)
        (fun i _ => hp (i::env))
        (by intro i hi; simp [BitArithmetic.equalNat_value, Nat.ne_of_lt hi])
        (by intro i _; exact BitArithmetic.addNat_value i 1)
        (by simp [BitArithmetic.equalNat_value])

structure Bounded (t : Trace) (cost cap : ℕ) : Prop where
  length_le : t.length ≤ 2*cost
  tariff_le : ∀ s ∈ t, s.tariff ≤ cap

theorem Bounded.mono {t : Trace} {c b c' b' : ℕ} (h : Bounded t c b)
    (hc : c ≤ c') (hb : b ≤ b') : Bounded t c' b' :=
  ⟨h.length_le.trans (Nat.mul_le_mul_left 2 hc), fun s hs => (h.tariff_le s hs).trans hb⟩

theorem Bounded.append {t u : Trace} {c d b : ℕ}
    (ht : Bounded t c b) (hu : Bounded u d b) : Bounded (t++u) (c+d) b := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_append]
    have h1 := ht.length_le
    have h2 := hu.length_le
    omega
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact ht.tariff_le s h
    · exact hu.tariff_le s h

theorem bounded_flatMap {α : Type*} (xs : List α) (f : α → Trace) (c : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ xs, Bounded (f x) (c x) B) :
    Bounded (xs.flatMap f) ((xs.map c).sum) B := by
  induction xs with
  | nil => exact ⟨by simp, by simp⟩
  | cons x xs ih =>
    exact (h x (by simp)).append (ih (fun y hy => h y (by simp [hy])))

theorem bounded_pair (s : Step) (c B : ℕ) (hs : s.tariff ≤ B) (hB : 1 ≤ B) :
    Bounded [s,.control] (c+1) B := by
  refine ⟨by simp, ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact hs
  · exact hB

theorem bounded_single (s : Step) (c B : ℕ) (hc : 0 < c) (hs : s.tariff ≤ B) :
    Bounded [s] c B := by
  refine ⟨by simp; omega, ?_⟩
  intro t ht
  have ht' : t = s := by simpa using ht
  subst t
  exact hs

theorem expr_cost_pos (env : List ℕ) (e : Expr) : 0 < (e.run env).cost := by
  cases e <;> simp only [Expr.run] <;> omega

theorem program_cost_pos (env : List ℕ) (p : Program) : 0 < (p.run env).cost := by
  cases p <;> simp only [Program.run] <;> omega

theorem powerTrace_bounded (base k : ℕ) :
    Bounded (powerTrace base k) (powerRun base k).cost (16*(powerRun base k).cost) := by
  induction k with
  | zero =>
    constructor
    · simp [powerTrace, powerRun, width]
    · intro s hs
      simp only [powerTrace, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> simp [Step.tariff, powerRun, compareCost, width]
  | succ k ih =>
    have hc := powerRun_count_le base (k+1)
    have hw := BitModel.width_le_of_le (le_refl (k+1))
    have hold : (powerRun base k).cost ≤ (powerRun base (k+1)).cost := by simp [powerRun]; omega
    have hmul : mulCost (base^k) base ≤ (powerRun base (k+1)).cost := by
      simp only [powerRun, powerRun_value]; omega
    constructor
    · have hl := ih.length_le
      have hm := mulCost_ge_widths (base^k) base
      have hp := width_pos base
      simp only [powerTrace, List.length_append, List.length_cons, List.length_nil,
        powerRun, powerRun_value]
      omega
    · intro s hs
      simp only [powerTrace, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with ((rfl | rfl | rfl) | hs) | rfl
      · simp only [Step.tariff, compareCost]
        have : width 0 = 1 := rfl
        omega
      · simp only [Step.tariff]; omega
      · simp only [Step.tariff, addCost]
        have : width 1 = 2 := rfl
        omega
      · exact (ih.tariff_le s hs).trans (by omega)
      · exact hmul.trans (by omega)

theorem binary_bounded (ta tb : Trace) (ca cb charge r : ℕ) (op : Step)
    (ha : Bounded ta ca (16*(ca+r))) (hb : Bounded tb cb (16*(cb+r)))
    (hop : op.tariff ≤ charge) :
    Bounded (ta++tb++[op,.control]) (ca+cb+charge+1) (16*(ca+cb+charge+1+r)) := by
  have h1 := ha.mono (le_refl _) (by omega : 16*(ca+r) ≤ 16*(ca+cb+charge+1+r))
  have h2 := hb.mono (le_refl _) (by omega : 16*(cb+r) ≤ 16*(ca+cb+charge+1+r))
  have h3 := bounded_pair op charge (16*(ca+cb+charge+1+r)) (by omega) (by omega)
  simpa only [Nat.add_assoc] using (h1.append h2).append h3

theorem exprTrace_bounded (env : List ℕ) (e : Expr) :
    Bounded (exprTrace env e) (e.run env).cost (16*((e.run env).cost+listBits env)) := by
  induction e with
  | literal n =>
    change Bounded _ (width n+1) (16*(width n+1+listBits env))
    exact bounded_pair (.writeNat n) (width n) _ (by simp [Step.tariff]; omega) (by omega)
  | read i =>
    apply bounded_single _ _ _ (expr_cost_pos env (.read i))
    change (Expr.read i |>.run env).cost ≤ _
    omega
  | add a b ha hb => exact binary_bounded _ _ _ _ _ _ _ ha hb (le_refl _)
  | sub a b ha hb => exact binary_bounded _ _ _ _ _ _ _ ha hb (le_refl _)
  | mul a b ha hb => exact binary_bounded _ _ _ _ _ _ _ ha hb (le_refl _)
  | less a b ha hb => exact binary_bounded _ _ _ _ _ _ _ ha hb (le_refl _)
  | equal a b ha hb => exact binary_bounded _ _ _ _ _ _ _ ha hb (le_refl _)
  | power a b ha hb =>
    let ca := (a.run env).cost
    let cb := (b.run env).cost
    let cp := (powerRun (a.run env).value (b.run env).value).cost
    let B := 16*(ca+cb+cp+1+listBits env)
    have h1 : Bounded (exprTrace env a) ca B := ha.mono (le_refl _) (by dsimp [B,ca,cb,cp]; omega)
    have h2 : Bounded (exprTrace env b) cb B := hb.mono (le_refl _) (by dsimp [B,ca,cb,cp]; omega)
    have h3 : Bounded (powerTrace (a.run env).value (b.run env).value) cp B :=
      (powerTrace_bounded _ _).mono (le_refl _) (by dsimp [B,ca,cb,cp]; omega)
    have h4 : Bounded [.control] 1 B := bounded_single _ _ _ (by decide) (by dsimp [Step.tariff,B]; omega)
    exact ((h1.append h2).append h3).append h4
  | odd a ha =>
    have h1 := ha.mono (le_refl _) (by omega :
      16*((a.run env).cost+listBits env) ≤ 16*((a.run env).cost+2+listBits env))
    have h2 : Bounded [.odd (a.run env).value] 2 (16*((a.run env).cost+2+listBits env)) :=
      bounded_single _ _ _ (by decide) (by simp only [Step.tariff]; omega)
    exact h1.append h2

theorem sum_map_mem_le {α : Type*} (xs : List α) (f : α → ℕ) {x : α} (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.map_cons, List.sum_cons]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx
      omega

def iterationCost (env : List ℕ) (p : Program) (i : ℕ) : ℕ :=
  (p.run (i::env)).cost + (width i + addCost i 1 + 1) + outputBits (p.run (i::env)).output

theorem loop_cost (env : List ℕ) (e : Expr) (p : Program) :
    ((Program.loop e p).run env).cost = (e.run env).cost + 1 +
      ((List.range (e.run env).value).map (iterationCost env p)).sum := by
  simp only [Program.run, List.map_map, Function.comp_def]
  rfl

theorem programTrace_bounded (env : List ℕ) (p : Program) :
    Bounded (programTrace env p) (p.run env).cost (16*((p.run env).cost+listBits env)) := by
  induction p generalizing env with
  | skip =>
    apply bounded_single _ _ _ (by simp [Program.run])
    change 1 ≤ 16*(1+listBits env)
    omega
  | emit s a b =>
    let cs := (s.run env).cost
    let ca := (a.run env).cost
    let cb := (b.run env).cost
    let entry : RationalCode := ⟨decide ((s.run env).value%2=1), (a.run env).value, (b.run env).value⟩
    let B := 16*(cs+ca+cb+entry.bits+2+listBits env)
    have hs : Bounded (exprTrace env s) cs B := (exprTrace_bounded env s).mono (le_refl _)
      (by dsimp [B,cs,ca,cb]; omega)
    have ha : Bounded (exprTrace env a) ca B := (exprTrace_bounded env a).mono (le_refl _)
      (by dsimp [B,cs,ca,cb]; omega)
    have hb : Bounded (exprTrace env b) cb B := (exprTrace_bounded env b).mono (le_refl _)
      (by dsimp [B,cs,ca,cb]; omega)
    have he : Bounded [.emit entry] (entry.bits+2) B := bounded_single _ _ _ (by omega)
      (by dsimp [Step.tariff,B]; omega)
    simpa [programTrace, Program.run, cs, ca, cb, entry, B, Nat.add_assoc] using
      ((hs.append ha).append hb).append he
  | sequence p q hp hq =>
    let cp := (p.run env).cost
    let cq := (q.run env).cost
    let co := outputBits (p.run env).output
    let B := 16*(cp+cq+co+1+listBits env)
    have h1 : Bounded (programTrace env p) cp B := (hp env).mono (le_refl _)
      (by dsimp [B,cp,cq,co]; omega)
    have h2 : Bounded (programTrace env q) cq B := (hq env).mono (le_refl _)
      (by dsimp [B,cp,cq,co]; omega)
    have h3 : Bounded [.copy (p.run env).output,.control] (co+1) B := bounded_pair _ _ _
      (by dsimp [B,cp,cq,co,Step.tariff]; omega) (by dsimp [B]; omega)
    simpa [programTrace, Program.run, cp, cq, co, B, Nat.add_assoc] using (h1.append h2).append h3
  | branch e p q hp hq =>
    let selected := if (e.run env).value=0 then q else p
    have hi : Bounded (programTrace env selected) (selected.run env).cost
        (16*((selected.run env).cost+listBits env)) := by
      dsimp [selected]
      split <;> [exact hq env; exact hp env]
    let ce := (e.run env).cost
    let cp := (selected.run env).cost
    let B := 16*(ce+cp+1+listBits env)
    have he := exprTrace_bounded env e
    have hw := expr_width_le env e
    have hprefix : Bounded (exprTrace env e ++ [.equal (e.run env).value 0,.control])
        (ce+1) B := by
      constructor
      · have hl := he.length_le
        simp only [List.length_append, List.length_cons, List.length_nil]
        dsimp [ce]
        omega
      · intro s hs
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with hs | rfl | rfl
        · exact (he.tariff_le s hs).trans (by dsimp [B,ce,cp]; omega)
        · dsimp [Step.tariff,compareCost,B,ce,cp]
          have : width 0 = 1 := rfl
          omega
        · dsimp [Step.tariff,B]; omega
    have hbody : Bounded (programTrace env selected) cp B := hi.mono (le_refl _)
      (by dsimp [B,ce,cp]; omega)
    have hboth := hprefix.append hbody
    by_cases h : (e.run env).value=0 <;>
      simpa [programTrace,Program.run,selected,h,B,ce,cp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hboth
  | loop e p hp =>
    let b := (e.run env).value
    let ce := (e.run env).cost
    let S := ((List.range b).map (iterationCost env p)).sum
    let C := ce+1+S
    let B := 16*(C+listBits env)
    have hC : ((Program.loop e p).run env).cost = C := loop_cost env e p
    have hCpos : 0 < C := by dsimp [C]; omega
    have hw := expr_width_le env e
    have hiter : ∀ i ∈ List.range b,
        Bounded ([.equal i b,.writeNat i] ++ programTrace (i::env) p ++
          [.add i 1,.copy (p.run (i::env)).output,.control]) (iterationCost env p i) B := by
      intro i hi
      have hic : iterationCost env p i ≤ S := sum_map_mem_le (List.range b) (iterationCost env p) hi
      have hil : i < b := List.mem_range.mp hi
      have hwi : width i ≤ width b := width_mono (Nat.le_of_lt hil)
      have hbody := hp (i::env)
      constructor
      · have hl := hbody.length_le
        have hpw := width_pos i
        simp only [List.length_append,List.length_cons,List.length_nil]
        dsimp [iterationCost,addCost]
        have : width 1 = 2 := rfl
        omega
      · intro s hs
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with ((rfl | rfl) | hs) | rfl | rfl | rfl
        · dsimp [Step.tariff,compareCost,B,C,ce,b]
          dsimp [b] at hwi
          omega
        · dsimp [Step.tariff,B,C]
          dsimp [iterationCost] at hic
          omega
        · have hh := hbody.tariff_le s hs
          change s.tariff ≤ 16*(C+listBits env)
          change s.tariff ≤ 16*((p.run (i::env)).cost+(width i+listBits env)) at hh
          dsimp [iterationCost] at hic
          dsimp [C]
          omega
        · dsimp [Step.tariff,B,C]
          dsimp [iterationCost] at hic
          omega
        · dsimp [Step.tariff,B,C]
          dsimp [iterationCost] at hic
          omega
        · dsimp [Step.tariff,B]
          omega
    have hflat := bounded_flatMap (List.range b)
      (fun i => [.equal i b,.writeNat i] ++ programTrace (i::env) p ++
        [.add i 1,.copy (p.run (i::env)).output,.control]) (iterationCost env p) B hiter
    have hbound : Bounded (exprTrace env e) ce B := (exprTrace_bounded env e).mono (le_refl _)
      (by dsimp [B,C,ce]; omega)
    have hlast : Bounded [.equal b b,.control] 1 B := by
      apply bounded_pair (.equal b b) 0 B
      · dsimp [Step.tariff,compareCost,B,C,b,ce]
        omega
      · dsimp [B]
        omega
    rw [hC]
    simpa [programTrace,C,B,ce,S,b,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (hbound.append hflat).append hlast

def executionSteps (p : Program) (inputs : List ℕ) : ℕ :=
  Trace.steps (.input inputs :: programTrace inputs p)

theorem executionSteps_exec (p : Program) (inputs : List ℕ) :
    Exec p inputs (BitModel.execute p inputs).output (executionSteps p inputs) :=
  ⟨programTrace inputs p, programTrace_correct inputs p, rfl⟩

theorem executionSteps_le (p : Program) (inputs : List ℕ) :
    executionSteps p inputs ≤ 1024 * (BitModel.execute p inputs).cost^3 := by
  let t := Step.input inputs :: programTrace inputs p
  let C := (BitModel.execute p inputs).cost
  have hp := programTrace_bounded inputs p
  have hpos := program_cost_pos inputs p
  have hl : t.length ≤ 3*C := by
    have h := hp.length_le
    dsimp [t,C,BitModel.execute]
    omega
  have ht : ∀ s ∈ t, s.steps ≤ (16*C)^2 := by
    intro s hs
    apply (Step.steps_le s).trans
    apply Nat.pow_le_pow_left
    simp only [t,List.mem_cons] at hs
    rcases hs with rfl | hs
    · change listBits inputs ≤ 16*C
      dsimp [C,BitModel.execute]
      omega
    · simpa [C,BitModel.execute,Nat.add_comm] using hp.tariff_le s hs
  change Trace.steps t ≤ 1024*C^3
  calc
    Trace.steps t ≤ t.length*(16*C)^2 :=
      BitModel.sum_map_le_length_mul t Step.steps ((16*C)^2) ht
    _ ≤ (3*C)*(16*C)^2 := Nat.mul_le_mul_right _ hl
    _ ≤ 1024*C^3 := by ring_nf; omega

theorem execute_refines (p : Program) (inputs : List ℕ) :
    ∃ steps, Exec p inputs (BitModel.execute p inputs).output steps ∧
      steps ≤ 1024 * (BitModel.execute p inputs).cost^3 :=
  ⟨executionSteps p inputs, executionSteps_exec p inputs, executionSteps_le p inputs⟩

end NCHitting.BitRefinement

end OAI
