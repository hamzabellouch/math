import Mathlib

namespace OAI

/-!
Generalized-circuit smoothing, perturbation stability and rational meshes.

Gate satisfaction is conditional on a real fixed assignment, and mesh existence
approximates a given cube point. Applying Brouwer and combining these lemmas to
establish simultaneous totality remain unproved. `QuasilinearPCPStatement` is a
goal proposition: the uniform quasilinear reduction, soundness, deterministic
algorithm realization and complexity bounds also remain unproved.
-/

namespace PCPforPPAD

abbrev BitString := List Bool
abbrev UnitRat := {a : ℚ // 0 ≤ a ∧ a ≤ 1}

def encodeNat (n : ℕ) : BitString :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : BitString :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeList {α : Type*} (f : α → BitString) (l : List α) : BitString :=
  encodeNat l.length ++ l.flatMap f

inductive BooleanGate (V : Type)
  | and : V → V → BooleanGate V
  | or : V → V → BooleanGate V
  | not : V → BooleanGate V
  deriving DecidableEq

def BooleanGate.eval {V : Type} (v : V → Bool) : BooleanGate V → Bool
  | .and a b => v a && v b
  | .or a b => v a || v b
  | .not a => !v a

def BooleanGate.encode {n : ℕ} : BooleanGate (Fin n) → BitString
  | .and a b => [false, false] ++ encodeNat a.val ++ encodeNat b.val
  | .or a b => [false, true] ++ encodeNat a.val ++ encodeNat b.val
  | .not a => [true, false] ++ encodeNat a.val

structure BooleanCircuit (n : ℕ) where
  gateCount : ℕ
  gate : (i : Fin gateCount) → BooleanGate (Fin (n + i.val))
  output : Fin n → Fin (n + gateCount)

def BooleanCircuit.wireValue {n : ℕ} (C : BooleanCircuit n) (x : Fin n → Bool)
    (k : ℕ) : Bool :=
  if hi : k < n then x ⟨k, hi⟩
  else if hg : k - n < C.gateCount then
    (C.gate ⟨k - n, hg⟩).eval (fun i => C.wireValue x i.val)
  else false
termination_by k
decreasing_by
  have hi := i.isLt
  simp only at hi
  omega

def BooleanCircuit.eval {n : ℕ} (C : BooleanCircuit n) (x : Fin n → Bool) :
    Fin n → Bool :=
  fun i => C.wireValue x (C.output i).val

def BooleanCircuit.encode {n : ℕ} (C : BooleanCircuit n) : BitString :=
  encodeNat n ++ encodeList encodeNat (List.range n) ++
    encodeList (fun i : Fin C.gateCount =>
      encodeNat (n + i.val) ++ (C.gate i).encode) (List.finRange C.gateCount) ++
    encodeList (fun i : Fin n => encodeNat (C.output i).val) (List.finRange n)

structure EndOfLine where
  n : ℕ
  n_pos : 0 < n
  S : BooleanCircuit n
  P : BooleanCircuit n
  pred_zero : P.eval (fun _ => false) = (fun _ => false)
  succ_zero : S.eval (fun _ => false) ≠ (fun _ => false)
  pred_succ_zero : P.eval (S.eval (fun _ => false)) = (fun _ => false)

def EndOfLine.IsSolution (I : EndOfLine) (v : Fin I.n → Bool) : Prop :=
  v ≠ (fun _ => false) ∧
    (I.P.eval (I.S.eval v) ≠ v ∨ I.S.eval (I.P.eval v) ≠ v)

def EndOfLine.encode (I : EndOfLine) : BitString := I.S.encode ++ I.P.encode

def EndOfLine.length (I : EndOfLine) : ℕ := I.encode.length

inductive Gate (V : Type)
  | constant : UnitRat → V → Gate V
  | scale : UnitRat → V → V → Gate V
  | copy : V → V → Gate V
  | add : V → V → V → Gate V
  | subtract : V → V → V → Gate V
  | less : V → V → V → Gate V
  | or : V → V → V → Gate V
  | and : V → V → V → Gate V
  | not : V → V → Gate V
  deriving DecidableEq

def Gate.output {V : Type} : Gate V → V
  | .constant _ z | .scale _ _ z | .copy _ z | .add _ _ z |
    .subtract _ _ z | .less _ _ z | .or _ _ z | .and _ _ z | .not _ z => z

def Gate.Satisfied {V : Type} (ε : ℝ) (x : V → ℝ) : Gate V → Prop
  | .constant α z => |x z - (α.val : ℝ)| ≤ ε
  | .scale α a z => |x z - (α.val : ℝ) * x a| ≤ ε
  | .copy a z => |x z - x a| ≤ ε
  | .add a b z => |x z - min (x a + x b) 1| ≤ ε
  | .subtract a b z => |x z - max (x a - x b) 0| ≤ ε
  | .less a b z =>
      (x a < x b - ε → 1 - ε ≤ x z) ∧ (x b + ε < x a → x z ≤ ε)
  | .or a b z =>
      (1 - ε ≤ x a ∨ 1 - ε ≤ x b → 1 - ε ≤ x z) ∧
        (x a ≤ ε ∧ x b ≤ ε → x z ≤ ε)
  | .and a b z =>
      (1 - ε ≤ x a ∧ 1 - ε ≤ x b → 1 - ε ≤ x z) ∧
        (x a ≤ ε ∨ x b ≤ ε → x z ≤ ε)
  | .not a z => (x a ≤ ε → 1 - ε ≤ x z) ∧ (1 - ε ≤ x a → x z ≤ ε)

structure GeneralizedCircuit where
  nodeCount : ℕ
  gateCount : ℕ
  gates_nonempty : 0 < gateCount
  gate : Fin gateCount → Gate (Fin nodeCount)
  unique_output : Function.Injective (fun i => (gate i).output)

def Gate.encode {n : ℕ} : Gate (Fin n) → BitString
  | .constant α z => encodeNat 0 ++ encodeNat z.val ++ encodeRat α.val
  | .scale α a z => encodeNat 1 ++ encodeNat z.val ++ encodeNat a.val ++ encodeRat α.val
  | .copy a z => encodeNat 2 ++ encodeNat z.val ++ encodeNat a.val
  | .add a b z => encodeNat 3 ++ encodeNat z.val ++ encodeNat a.val ++ encodeNat b.val
  | .subtract a b z => encodeNat 4 ++ encodeNat z.val ++ encodeNat a.val ++ encodeNat b.val
  | .less a b z => encodeNat 5 ++ encodeNat z.val ++ encodeNat a.val ++ encodeNat b.val
  | .or a b z => encodeNat 6 ++ encodeNat z.val ++ encodeNat a.val ++ encodeNat b.val
  | .and a b z => encodeNat 7 ++ encodeNat z.val ++ encodeNat a.val ++ encodeNat b.val
  | .not a z => encodeNat 8 ++ encodeNat z.val ++ encodeNat a.val

def GeneralizedCircuit.encode (G : GeneralizedCircuit) : BitString :=
  encodeList encodeNat (List.range G.nodeCount) ++
    encodeList Gate.encode (List.ofFn G.gate)

def GeneralizedCircuit.length (G : GeneralizedCircuit) : ℕ := G.encode.length

abbrev RationalAssignment (G : GeneralizedCircuit) := Fin G.nodeCount → UnitRat

def RationalAssignment.toReal {G : GeneralizedCircuit} (x : RationalAssignment G) :
    Fin G.nodeCount → ℝ := fun v => ((x v).val : ℝ)

def RationalAssignment.encode {G : GeneralizedCircuit} (x : RationalAssignment G) : BitString :=
  encodeList (fun r : UnitRat => encodeRat r.val) (List.ofFn x)

def RationalAssignment.length {G : GeneralizedCircuit} (x : RationalAssignment G) : ℕ :=
  x.encode.length

noncomputable def failedGates (ε : ℚ) (G : GeneralizedCircuit) (x : RationalAssignment G) :
    Finset (Fin G.gateCount) := by
  classical
  exact Finset.univ.filter (fun i => ¬ (G.gate i).Satisfied (ε : ℝ) x.toReal)

def Acceptable (ε δ : ℚ) (p : Polynomial ℕ) (G : GeneralizedCircuit)
    (x : RationalAssignment G) : Prop :=
  x.length ≤ p.eval G.length ∧
    ((failedGates ε G x).card : ℚ) ≤ δ * (G.gateCount : ℚ)

structure Algorithm where
  states : ℕ
  transition : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

abbrev Algorithm.Config (A : Algorithm) :=
  Turing.TM0.Cfg (Option Bool) (Fin (A.states + 1))

def Algorithm.runSteps (A : Algorithm) : ℕ → A.Config → Option A.Config
  | 0, c => some c
  | t + 1, c => (Turing.TM0.step A.transition c).bind (A.runSteps t)

def Algorithm.RunsWithin (A : Algorithm) (input output : BitString) (bound : ℕ) : Prop :=
  ∃ t ≤ bound, ∃ c : A.Config,
    A.runSteps t (Turing.TM0.init (input.map some)) = some c ∧
    Turing.TM0.step A.transition c = none ∧
    c.Tape.right₀ = Turing.ListBlank.mk (output.map some)

def logFactor (N : ℕ) : ℕ := Nat.clog 2 (N + 2)

def QuasilinearPCPStatement : Prop :=
  ∃ (ε δ : ℚ) (A b : ℕ) (p timeR timeD : Polynomial ℕ) (R D : Algorithm),
    (0 < ε ∧ ε < 1 / 10) ∧ (0 < δ ∧ δ < 1) ∧ 0 < A ∧
    (∀ G : GeneralizedCircuit, ∃ x : RationalAssignment G, Acceptable ε δ p G x) ∧
    (∀ I : EndOfLine, ∃ G : GeneralizedCircuit,
      G.length ≤ A * I.length * (logFactor I.length) ^ b ∧
      R.RunsWithin I.encode G.encode (timeR.eval I.length) ∧
      ∀ x : RationalAssignment G, Acceptable ε δ p G x →
        ∃ v : Fin I.n → Bool, I.IsSolution v ∧
          D.RunsWithin (I.encode ++ x.encode) (List.ofFn v)
            (timeD.eval (I.length + x.length)))

end PCPforPPAD

namespace PCPforPPAD

@[simp] theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = 2 * n.bits.length + 1 := by
  simp [encodeNat]
  omega

theorem encodeNat_length_pos (n : ℕ) : 0 < (encodeNat n).length := by
  rw [encodeNat_length]
  omega

theorem BooleanCircuit.encode_length_pos {n : ℕ} (C : BooleanCircuit n) :
    0 < C.encode.length := by
  have h := encodeNat_length_pos n
  simp only [BooleanCircuit.encode, List.length_append]
  omega

theorem EndOfLine.length_ge_two (I : EndOfLine) : 2 ≤ I.length := by
  have hS := I.S.encode_length_pos
  have hP := I.P.encode_length_pos
  simp only [EndOfLine.length, EndOfLine.encode, List.length_append]
  omega

theorem exists_other_endpoint {α : Type*} [Finite α] (S P : α → α) (z : α)
    (hP : P z = z) (hS : S z ≠ z) (hPS : P (S z) = z) :
    ∃ v, v ≠ z ∧ P (S v) ≠ v := by
  classical
  by_contra h
  have hinv : Function.LeftInverse P S := by
    intro v
    by_cases hv : v = z
    · simpa [hv] using hPS
    · by_contra hne
      exact h ⟨v, hv, hne⟩
  obtain ⟨v, hv⟩ := (Finite.surjective_of_injective hinv.injective) z
  have hvz : v = z := by
    calc
      v = P (S v) := (hinv v).symm
      _ = z := by rw [hv, hP]
  exact hS (hvz ▸ hv)

theorem EndOfLine.exists_solution (I : EndOfLine) : ∃ v, I.IsSolution v := by
  obtain ⟨v, hv, hps⟩ := exists_other_endpoint I.S.eval I.P.eval (fun _ => false)
    I.pred_zero I.succ_zero I.pred_succ_zero
  exact ⟨v, hv, Or.inl hps⟩

theorem acceptable_iff_floor_budget (ε δ : ℚ) (hδ : 0 ≤ δ) (p : Polynomial ℕ)
    (G : GeneralizedCircuit) (x : RationalAssignment G) :
    Acceptable ε δ p G x ↔
      x.length ≤ p.eval G.length ∧ (failedGates ε G x).card ≤ ⌊δ * G.gateCount⌋₊ := by
  rw [Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg _))]
  rfl

def clip01 (t : ℝ) : ℝ := max 0 (min t 1)

lemma clip01_nonneg (t : ℝ) : 0 ≤ clip01 t := le_max_left _ _

lemma clip01_le_one (t : ℝ) : clip01 t ≤ 1 := by
  exact max_le (by norm_num) (min_le_right _ _)

lemma clip01_eq_zero {t : ℝ} (h : t ≤ 0) : clip01 t = 0 := by
  exact max_eq_left ((min_le_left _ _).trans h)

lemma clip01_eq_one {t : ℝ} (h : 1 ≤ t) : clip01 t = 1 := by
  simp [clip01, min_eq_right h]

noncomputable def booleanSignal (ε t : ℝ) : ℝ := clip01 ((t - 2 * ε) / (1 - 4 * ε))

lemma booleanSignal_low {ε t : ℝ} (hε : ε < 1 / 10) (ht : t ≤ 2 * ε) :
    booleanSignal ε t = 0 := by
  apply clip01_eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

lemma booleanSignal_high {ε t : ℝ} (hε : ε < 1 / 10) (ht : 1 - 2 * ε ≤ t) :
    booleanSignal ε t = 1 := by
  apply clip01_eq_one
  rw [le_div_iff₀ (show 0 < 1 - 4 * ε by linarith)]
  linarith

lemma booleanSignal_nonneg (ε t : ℝ) : 0 ≤ booleanSignal ε t := clip01_nonneg _

lemma booleanSignal_le_one (ε t : ℝ) : booleanSignal ε t ≤ 1 := clip01_le_one _

noncomputable def lessSignal (ε a b : ℝ) : ℝ := clip01 ((b - a) / ε + 1 / 2)

lemma lessSignal_low {ε a b : ℝ} (hε : 0 < ε) (hgap : b - a ≤ -ε / 2) :
    lessSignal ε a b = 0 := by
  apply clip01_eq_zero
  have h : (b - a) / ε ≤ -(1 / 2 : ℝ) := by
    rw [div_le_iff₀ hε]
    linarith
  linarith

lemma lessSignal_high {ε a b : ℝ} (hε : 0 < ε) (hgap : ε / 2 ≤ b - a) :
    lessSignal ε a b = 1 := by
  apply clip01_eq_one
  have h : (1 / 2 : ℝ) ≤ (b - a) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  linarith

noncomputable def Gate.smoothedValue {V : Type} (ε : ℝ) (x : V → ℝ) : Gate V → ℝ
  | .constant α _ => (α.val : ℝ)
  | .scale α a _ => (α.val : ℝ) * x a
  | .copy a _ => x a
  | .add a b _ => min (x a + x b) 1
  | .subtract a b _ => max (x a - x b) 0
  | .less a b _ => lessSignal ε (x a) (x b)
  | .or a b _ => max (booleanSignal ε (x a)) (booleanSignal ε (x b))
  | .and a b _ => min (booleanSignal ε (x a)) (booleanSignal ε (x b))
  | .not a _ => 1 - booleanSignal ε (x a)

lemma low_input_before_perturbation {ε a a' : ℝ} (hε : 0 < ε)
    (hclose : |a' - a| ≤ ε / 40) (ha' : a' ≤ ε) : a ≤ 2 * ε := by
  have := (abs_le.mp hclose).1
  linarith

lemma high_input_before_perturbation {ε a a' : ℝ} (hε : 0 < ε)
    (hclose : |a' - a| ≤ ε / 40) (ha' : 1 - ε ≤ a') : 1 - 2 * ε ≤ a := by
  have := (abs_le.mp hclose).2
  linarith

lemma low_output_after_perturbation {ε z z' : ℝ} (hε : 0 < ε)
    (hclose : |z' - z| ≤ ε / 40) (hz : z = 0) : z' ≤ ε := by
  have := (abs_le.mp hclose).2
  linarith

lemma high_output_after_perturbation {ε z z' : ℝ} (hε : 0 < ε)
    (hclose : |z' - z| ≤ ε / 40) (hz : z = 1) : 1 - ε ≤ z' := by
  have := (abs_le.mp hclose).1
  linarith

lemma abs_sum_perturbation {a b a' b' η : ℝ}
    (ha : |a' - a| ≤ η) (hb : |b' - b| ≤ η) :
    |(a + b) - (a' + b')| ≤ η + η := by
  calc
    |(a + b) - (a' + b')| = |(a - a') + (b - b')| := by ring_nf
    _ ≤ |a - a'| + |b - b'| := abs_add_le _ _
    _ ≤ η + η := add_le_add (by simpa [abs_sub_comm] using ha)
      (by simpa [abs_sub_comm] using hb)

lemma abs_difference_perturbation {a b a' b' η : ℝ}
    (ha : |a' - a| ≤ η) (hb : |b' - b| ≤ η) :
    |(a - b) - (a' - b')| ≤ η + η := by
  calc
    |(a - b) - (a' - b')| = |(a - a') - (b - b')| := by ring_nf
    _ ≤ |a - a'| + |b - b'| := abs_sub _ _
    _ ≤ η + η := add_le_add (by simpa [abs_sub_comm] using ha)
      (by simpa [abs_sub_comm] using hb)

theorem Gate.satisfied_of_perturbation {V : Type} (g : Gate V) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 10) (x y : V → ℝ)
    (hclose : ∀ v, |y v - x v| ≤ ε / 40)
    (hfixed : x g.output = g.smoothedValue ε x) : g.Satisfied ε y := by
  cases g with
  | constant α z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    change |y z - (α.val : ℝ)| ≤ ε
    calc
      _ = |y z - x z| := by rw [hfixed]
      _ ≤ ε / 40 := hclose z
      _ ≤ ε := by linarith
  | scale α a z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    change |y z - (α.val : ℝ) * y a| ≤ ε
    have hα0 : (0 : ℝ) ≤ (α.val : ℝ) := by exact_mod_cast α.property.1
    have hα1 : (α.val : ℝ) ≤ (1 : ℝ) := by exact_mod_cast α.property.2
    have hop : |(α.val : ℝ) * x a - (α.val : ℝ) * y a| ≤ ε / 40 := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hα0, abs_sub_comm]
      calc
        _ ≤ 1 * (ε / 40) :=
          mul_le_mul hα1 (hclose a) (abs_nonneg _) (by norm_num)
        _ = ε / 40 := one_mul _
    calc
      _ ≤ |y z - (α.val : ℝ) * x a| +
          |(α.val : ℝ) * x a - (α.val : ℝ) * y a| := abs_sub_le _ _ _
      _ ≤ ε / 40 + ε / 40 := add_le_add (by rw [← hfixed]; exact hclose z) hop
      _ ≤ ε := by linarith
  | copy a z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    change |y z - y a| ≤ ε
    calc
      _ ≤ |y z - x a| + |x a - y a| := abs_sub_le _ _ _
      _ ≤ ε / 40 + ε / 40 := add_le_add
        (by rw [← hfixed]; exact hclose z) (by simpa [abs_sub_comm] using hclose a)
      _ ≤ ε := by linarith
  | add a b z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    change |y z - min (y a + y b) 1| ≤ ε
    have hop : |min (x a + x b) 1 - min (y a + y b) 1| ≤ ε / 40 + ε / 40 := by
      apply (abs_min_sub_min_le_max (x a + x b) 1 (y a + y b) 1).trans
      exact max_le (abs_sum_perturbation (hclose a) (hclose b)) (by simp; linarith)
    calc
      _ ≤ |y z - min (x a + x b) 1| +
          |min (x a + x b) 1 - min (y a + y b) 1| := abs_sub_le _ _ _
      _ ≤ ε / 40 + (ε / 40 + ε / 40) := add_le_add
        (by rw [← hfixed]; exact hclose z) hop
      _ ≤ ε := by linarith
  | subtract a b z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    change |y z - max (y a - y b) 0| ≤ ε
    have hop : |max (x a - x b) 0 - max (y a - y b) 0| ≤ ε / 40 + ε / 40 := by
      exact (abs_max_sub_max_le_abs _ _ _).trans
        (abs_difference_perturbation (hclose a) (hclose b))
    calc
      _ ≤ |y z - max (x a - x b) 0| +
          |max (x a - x b) 0 - max (y a - y b) 0| := abs_sub_le _ _ _
      _ ≤ ε / 40 + (ε / 40 + ε / 40) := add_le_add
        (by rw [← hfixed]; exact hclose z) hop
      _ ≤ ε := by linarith
  | less a b z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    have ha := abs_le.mp (hclose a)
    have hb := abs_le.mp (hclose b)
    constructor
    · intro h
      apply high_output_after_perturbation hε (hclose z)
      rw [hfixed]
      apply lessSignal_high hε
      linarith
    · intro h
      apply low_output_after_perturbation hε (hclose z)
      rw [hfixed]
      apply lessSignal_low hε
      linarith
  | or a b z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    constructor
    · intro h
      apply high_output_after_perturbation hε (hclose z)
      rw [hfixed]
      rcases h with h | h
      · rw [booleanSignal_high hε' (high_input_before_perturbation hε (hclose a) h)]
        exact max_eq_left (booleanSignal_le_one _ _)
      · rw [booleanSignal_high hε' (high_input_before_perturbation hε (hclose b) h)]
        exact max_eq_right (booleanSignal_le_one _ _)
    · rintro ⟨ha, hb⟩
      apply low_output_after_perturbation hε (hclose z)
      rw [hfixed,
        booleanSignal_low hε' (low_input_before_perturbation hε (hclose a) ha),
        booleanSignal_low hε' (low_input_before_perturbation hε (hclose b) hb), max_self]
  | and a b z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    constructor
    · rintro ⟨ha, hb⟩
      apply high_output_after_perturbation hε (hclose z)
      rw [hfixed,
        booleanSignal_high hε' (high_input_before_perturbation hε (hclose a) ha),
        booleanSignal_high hε' (high_input_before_perturbation hε (hclose b) hb), min_self]
    · intro h
      apply low_output_after_perturbation hε (hclose z)
      rw [hfixed]
      rcases h with h | h
      · rw [booleanSignal_low hε' (low_input_before_perturbation hε (hclose a) h)]
        exact min_eq_left (booleanSignal_nonneg _ _)
      · rw [booleanSignal_low hε' (low_input_before_perturbation hε (hclose b) h)]
        exact min_eq_right (booleanSignal_nonneg _ _)
  | not a z =>
    dsimp [Gate.output, Gate.smoothedValue] at hfixed
    constructor
    · intro h
      apply high_output_after_perturbation hε (hclose z)
      rw [hfixed, booleanSignal_low hε' (low_input_before_perturbation hε (hclose a) h)]
      norm_num
    · intro h
      apply low_output_after_perturbation hε (hclose z)
      rw [hfixed, booleanSignal_high hε' (high_input_before_perturbation hε (hclose a) h)]
      norm_num

theorem all_gates_satisfied_of_perturbation (G : GeneralizedCircuit) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 10) (x y : Fin G.nodeCount → ℝ)
    (hclose : ∀ v, |y v - x v| ≤ ε / 40)
    (hfixed : ∀ i, x (G.gate i).output = (G.gate i).smoothedValue ε x) :
    ∀ i, (G.gate i).Satisfied ε y := by
  intro i
  exact (G.gate i).satisfied_of_perturbation hε hε' x y hclose (hfixed i)

theorem Gate.continuous_smoothedValue {V : Type} (g : Gate V) (ε : ℝ) :
    Continuous (fun x : V → ℝ => g.smoothedValue ε x) := by
  cases g <;> dsimp [Gate.smoothedValue, booleanSignal, lessSignal, clip01] <;> fun_prop

theorem Gate.smoothedValue_in_unit {V : Type} (g : Gate V) (ε : ℝ) (x : V → ℝ)
    (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1) :
    0 ≤ g.smoothedValue ε x ∧ g.smoothedValue ε x ≤ 1 := by
  cases g with
  | constant α z =>
    change (0 : ℝ) ≤ (α.val : ℝ) ∧ (α.val : ℝ) ≤ 1
    exact ⟨by exact_mod_cast α.property.1, by exact_mod_cast α.property.2⟩
  | scale α a z =>
    have hα : (0 : ℝ) ≤ (α.val : ℝ) ∧ (α.val : ℝ) ≤ 1 :=
      ⟨by exact_mod_cast α.property.1, by exact_mod_cast α.property.2⟩
    exact ⟨mul_nonneg hα.1 (hx a).1,
      (mul_le_mul hα.2 (hx a).2 (hx a).1 (by norm_num)).trans (by norm_num)⟩
  | copy a z => exact hx a
  | add a b z =>
    exact ⟨le_min (add_nonneg (hx a).1 (hx b).1) (by norm_num), min_le_right _ _⟩
  | subtract a b z =>
    exact ⟨le_max_right _ _, max_le (by have := hx a; have := hx b; linarith)
      (by norm_num)⟩
  | less a b z => exact ⟨clip01_nonneg _, clip01_le_one _⟩
  | or a b z =>
    exact ⟨(booleanSignal_nonneg ε (x a)).trans (le_max_left _ _),
      max_le (booleanSignal_le_one _ _) (booleanSignal_le_one _ _)⟩
  | and a b z =>
    exact ⟨le_min (booleanSignal_nonneg _ _) (booleanSignal_nonneg _ _),
      (min_le_left _ _).trans (booleanSignal_le_one _ _)⟩
  | not a z =>
    have := booleanSignal_nonneg ε (x a)
    have := booleanSignal_le_one ε (x a)
    dsimp [Gate.smoothedValue]
    constructor <;> linarith

noncomputable def GeneralizedCircuit.cubeMap (G : GeneralizedCircuit) (ε : ℝ)
    (x : Fin G.nodeCount → ℝ) (v : Fin G.nodeCount) : ℝ := by
  classical
  exact if h : ∃ i, (G.gate i).output = v then
    (G.gate h.choose).smoothedValue ε x else 0

theorem GeneralizedCircuit.cubeMap_at_output (G : GeneralizedCircuit) (ε : ℝ)
    (x : Fin G.nodeCount → ℝ) (i : Fin G.gateCount) :
    G.cubeMap ε x (G.gate i).output = (G.gate i).smoothedValue ε x := by
  classical
  have h : ∃ j, (G.gate j).output = (G.gate i).output := ⟨i, rfl⟩
  simp only [GeneralizedCircuit.cubeMap, dite_eq_left h]
  rw [G.unique_output h.choose_spec]

theorem GeneralizedCircuit.continuous_cubeMap (G : GeneralizedCircuit) (ε : ℝ) :
    Continuous (G.cubeMap ε) := by
  classical
  apply continuous_pi
  intro v
  by_cases h : ∃ i, (G.gate i).output = v
  · simpa only [GeneralizedCircuit.cubeMap, dite_eq_left h] using
      (G.gate h.choose).continuous_smoothedValue ε
  · simpa only [GeneralizedCircuit.cubeMap, dite_eq_right h] using
      (continuous_const : Continuous (fun _ : Fin G.nodeCount → ℝ => (0 : ℝ)))

theorem GeneralizedCircuit.cubeMap_in_unit (G : GeneralizedCircuit) (ε : ℝ)
    (x : Fin G.nodeCount → ℝ) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1) :
    ∀ v, 0 ≤ G.cubeMap ε x v ∧ G.cubeMap ε x v ≤ 1 := by
  classical
  intro v
  by_cases h : ∃ i, (G.gate i).output = v
  · simpa only [GeneralizedCircuit.cubeMap, dite_eq_left h] using
      (G.gate h.choose).smoothedValue_in_unit ε x hx
  · simp [GeneralizedCircuit.cubeMap, h]

theorem encodeNat_length_le (n : ℕ) : (encodeNat n).length ≤ 2 * n + 1 := by
  have hn : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  rw [encodeNat_length]
  omega

theorem encodeList_length_le {α : Type*} (f : α → BitString) (l : List α) (K : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ K) :
    (encodeList f l).length ≤ (K + 2) * l.length + 1 := by
  have hflat : (l.flatMap f).length ≤ K * l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha : (f a).length ≤ K := h a (by simp)
      have hl := ih (fun b hb => h b (by simp [hb]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith
  have hhead := encodeNat_length_le l.length
  simp only [encodeList, List.length_append]
  nlinarith

theorem encodeList_length_ge {α : Type*} (f : α → BitString) (l : List α)
    (h : ∀ a ∈ l, 0 < (f a).length) : l.length ≤ (encodeList f l).length := by
  have hflat : l.length ≤ (l.flatMap f).length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha : 0 < (f a).length := h a (by simp)
      have hl := ih (fun b hb => h b (by simp [hb]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  simp only [encodeList, List.length_append]
  omega

theorem GeneralizedCircuit.nodeCount_le_length (G : GeneralizedCircuit) :
    G.nodeCount ≤ G.length := by
  have h := encodeList_length_ge encodeNat (List.range G.nodeCount)
    (fun n _ => encodeNat_length_pos n)
  simp only [List.length_range] at h
  simp only [GeneralizedCircuit.length, GeneralizedCircuit.encode, List.length_append]
  omega

def meshEntryBound (q : ℕ) : ℕ :=
  (Finset.range (q + 1)).sup (fun k => (encodeRat ((k : ℚ) / (q : ℚ))).length)

noncomputable def meshWitnessPolynomial (q : ℕ) : Polynomial ℕ :=
  Polynomial.C (meshEntryBound q + 2) * Polynomial.X + 1

theorem mesh_entry_length_le (q k : ℕ) (hk : k ≤ q) :
    (encodeRat ((k : ℚ) / (q : ℚ))).length ≤ meshEntryBound q := by
  exact Finset.le_sup (s := Finset.range (q + 1)) (b := k)
    (f := fun k => (encodeRat ((k : ℚ) / (q : ℚ))).length)
    (Finset.mem_range.mpr (by omega))

theorem RationalAssignment.mesh_length_le (G : GeneralizedCircuit) (q : ℕ)
    (x : RationalAssignment G)
    (hx : ∀ v, ∃ k : ℕ, k ≤ q ∧ (x v).val = (k : ℚ) / (q : ℚ)) :
    x.length ≤ (meshWitnessPolynomial q).eval G.length := by
  have hclen := encodeList_length_le (fun r : UnitRat => encodeRat r.val)
    (List.ofFn x) (meshEntryBound q) (by
      intro r hr
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨k, hk, hval⟩ := hx v
      simpa only [hval] using mesh_entry_length_le q k hk)
  change (encodeList (fun r : UnitRat => encodeRat r.val) (List.ofFn x)).length ≤ _
  simp only [List.length_ofFn] at hclen
  simp only [meshWitnessPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  exact hclen.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ G.nodeCount_le_length) 1)

theorem exists_mesh_numerator (q : ℕ) (hq : 0 < q) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ k : ℕ, k ≤ q ∧ |(k : ℝ) / (q : ℝ) - t| ≤ 1 / (2 * (q : ℝ)) := by
  let m : ℤ := round ((q : ℝ) * t)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hm0 : 0 ≤ m := by
    have h : round (0 : ℝ) ≤ round ((q : ℝ) * t) := by
      rw [round_eq, round_eq]
      apply Int.floor_mono
      nlinarith
    simpa only [round_zero] using h
  have hmq : m ≤ (q : ℤ) := by
    have h : round ((q : ℝ) * t) ≤ round (q : ℝ) := by
      rw [round_eq, round_eq]
      apply Int.floor_mono
      nlinarith
    simpa only [round_natCast] using h
  refine ⟨m.toNat, Int.toNat_le.mpr hmq, ?_⟩
  have hmR : (m.toNat : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm0
  have hd : (m.toNat : ℝ) / (q : ℝ) - t =
      ((m : ℝ) - (q : ℝ) * t) / (q : ℝ) := by
    rw [hmR]
    field_simp
  rw [hd, abs_div, abs_of_pos hqR, abs_sub_comm]
  calc
    _ ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right
      (abs_sub_round ((q : ℝ) * t)) hqR.le
    _ = 1 / (2 * (q : ℝ)) := by ring

def meshDenominator (ε : ℚ) : ℕ := ⌈20 / ε⌉₊

theorem meshDenominator_pos {ε : ℚ} (hε : 0 < ε) : 0 < meshDenominator ε := by
  exact Nat.one_le_ceil_iff.mpr (div_pos (by norm_num) hε)

theorem mesh_error_le {ε : ℚ} (hε : 0 < ε) :
    1 / (2 * (meshDenominator ε : ℝ)) ≤ (ε : ℝ) / 40 := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hqR : (0 : ℝ) < (meshDenominator ε : ℝ) := by
    exact_mod_cast meshDenominator_pos hε
  have hceil : (20 : ℝ) / (ε : ℝ) ≤ (meshDenominator ε : ℝ) := by
    exact_mod_cast (Nat.le_ceil (20 / ε))
  have hprod := (div_le_iff₀ hεR).mp hceil
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hqR)]
  nlinarith

theorem exists_mesh_assignment (G : GeneralizedCircuit) (q : ℕ) (hq : 0 < q)
    (x : Fin G.nodeCount → ℝ) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ 1) :
    ∃ y : RationalAssignment G,
      (∀ v, ∃ k : ℕ, k ≤ q ∧ (y v).val = (k : ℚ) / (q : ℚ)) ∧
      (∀ v, |y.toReal v - x v| ≤ 1 / (2 * (q : ℝ))) ∧
      y.length ≤ (meshWitnessPolynomial q).eval G.length := by
  classical
  choose k hk hclose using fun v => exists_mesh_numerator q hq (x v) (hx v)
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  let y : RationalAssignment G := fun v =>
    ⟨(k v : ℚ) / (q : ℚ), div_nonneg (Nat.cast_nonneg _) hqQ.le,
      (div_le_one hqQ).mpr (by exact_mod_cast hk v)⟩
  have hy : ∀ v, ∃ j : ℕ, j ≤ q ∧ (y v).val = (j : ℚ) / (q : ℚ) :=
    fun v => ⟨k v, hk v, rfl⟩
  refine ⟨y, hy, ?_, RationalAssignment.mesh_length_le G q y hy⟩
  intro v
  simpa only [RationalAssignment.toReal, y, Rat.cast_div, Rat.cast_natCast] using hclose v

end PCPforPPAD

end OAI
