import Mathlib

namespace OAI

/-! Deterministic logarithmic-space machines and their probabilistic-class inclusions. -/

namespace ExactDerandomization

abbrev Word := List Bool
abbrev Language := Set Word
abbrev CoinTape := ℕ → Bool

inductive Direction where
  | left | stay | right
  deriving DecidableEq

inductive InputSymbol where
  | leftMarker | bit (b : Bool) | rightMarker
  deriving DecidableEq

def Direction.move (d : Direction) (z : ℤ) : ℤ :=
  match d with
  | .left => z - 1
  | .stay => z
  | .right => z + 1

def Direction.moveInput (d : Direction) {n : ℕ} (i : Fin (n + 2)) : Fin (n + 2) :=
  match d with
  | .left => ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  | .stay => i
  | .right => ⟨min (i.val + 1) (n + 1), by omega⟩

def readInput (x : Word) (i : Fin (x.length + 2)) : InputSymbol :=
  if i.val = 0 then .leftMarker else
    match x[i.val - 1]? with
    | some b => .bit b
    | none => .rightMarker

structure Action (q w h : ℕ) where
  nextState : Fin (q + 1)
  write : Fin w → Bool
  workMove : Fin w → Direction
  inputMove : Fin h → Direction

structure Machine (q w h : ℕ) where
  initialState : Fin (q + 1)
  output : Fin (q + 1) → Option Bool
  transition : Fin (q + 1) → (Fin h → InputSymbol) → (Fin w → Bool) → Bool →
    Action q w h

structure Configuration (q w h n : ℕ) where
  state : Fin (q + 1)
  inputPos : Fin h → Fin (n + 2)
  workPos : Fin w → ℤ
  work : Fin w → ℤ → Bool

namespace Machine

variable {q w h : ℕ}

def initial (M : Machine q w h) (n : ℕ) : Configuration q w h n where
  state := M.initialState
  inputPos := fun _ => ⟨0, by omega⟩
  workPos := fun _ => 0
  work := fun _ _ => false

def step (M : Machine q w h) (x : Word) (b : Bool)
    (c : Configuration q w h x.length) : Configuration q w h x.length :=
  match M.output c.state with
  | some _ => c
  | none =>
    let a := M.transition c.state (fun j => readInput x (c.inputPos j))
      (fun k => c.work k (c.workPos k)) b
    { state := a.nextState
      inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
      workPos := fun k => (a.workMove k).move (c.workPos k)
      work := fun k => Function.update (c.work k) (c.workPos k) (a.write k) }

def run (M : Machine q w h) (x : Word) (coins : CoinTape) :
    ℕ → Configuration q w h x.length
  | 0 => M.initial x.length
  | t + 1 => M.step x (coins t) (M.run x coins t)

def spaceThrough (M : Machine q w h) (x : Word) (coins : CoinTape) (t : ℕ) : ℕ :=
  ∑ k : Fin w, ((Finset.range (t + 1)).image
    (fun s => (M.run x coins s).workPos k)).card

def LogSpace (M : Machine q w h) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ (x : Word) (coins : CoinTape) (t : ℕ),
    M.spaceThrough x coins t ≤ c * Nat.clog 2 (x.length + 2)

def Deterministic (M : Machine q w h) : Prop :=
  ∀ s i v, M.transition s i v false = M.transition s i v true

def HaltsBy (M : Machine q w h) (x : Word) (t : ℕ) : Prop :=
  ∀ coins : CoinTape, ∃ b : Bool, M.output (M.run x coins t).state = some b

def Decides (M : Machine q w h) (A : Language) : Prop :=
  ∀ x : Word, ∃ (t : ℕ) (b : Bool),
    (b = true ↔ x ∈ A) ∧ ∀ coins : CoinTape,
      M.output (M.run x coins t).state = some b

def extendCoins {t : ℕ} (bits : Fin t → Bool) : CoinTape :=
  fun s => if hs : s < t then bits ⟨s, hs⟩ else false

def acceptanceProbability (M : Machine q w h) (x : Word) (t : ℕ) : ℚ :=
  ((Finset.univ.filter (fun bits : Fin t → Bool =>
    M.output (M.run x (extendCoins bits) t).state = some true)).card : ℚ) /
    (2 : ℚ) ^ t

end Machine

def polynomialClock (c k n : ℕ) : ℕ := c * (n + 2) ^ k

def L : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.Deterministic ∧ M.LogSpace ∧ M.Decides A}

def RL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (1 / 2 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) = 0)}

def BPL : Set Language :=
  {A | ∃ (q w h : ℕ) (M : Machine q w h),
    M.LogSpace ∧ ∃ (c k : ℕ), 0 < c ∧ ∀ x : Word,
      M.HaltsBy x (polynomialClock c k x.length) ∧
      (x ∈ A → (2 / 3 : ℚ) ≤ M.acceptanceProbability x
        (polynomialClock c k x.length)) ∧
      (x ∉ A → M.acceptanceProbability x (polynomialClock c k x.length) ≤ (1 / 3 : ℚ))}

namespace Machine

variable {q w h : ℕ} {M : Machine q w h}

@[simp] theorem run_zero (x : Word) (coins : CoinTape) :
    M.run x coins 0 = M.initial x.length := rfl

@[simp] theorem run_succ (x : Word) (coins : CoinTape) (t : ℕ) :
    M.run x coins (t + 1) = M.step x (coins t) (M.run x coins t) := rfl

theorem run_eq_of_prefix (x : Word) {coins₁ coins₂ : CoinTape} {t : ℕ}
    (hprefix : ∀ s < t, coins₁ s = coins₂ s) :
    M.run x coins₁ t = M.run x coins₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, run_succ, hprefix t (Nat.lt_succ_self t),
      ih (fun s hs => hprefix s (Nat.lt_succ_of_lt hs))]

@[simp] theorem extendCoins_apply {t : ℕ} (bits : Fin t → Bool) (s : Fin t) :
    extendCoins bits s.val = bits s := by
  simp [extendCoins, s.isLt]

theorem step_eq_self_of_output {x : Word} {c : Configuration q w h x.length}
    {decision : Bool} (hout : M.output c.state = some decision) (coin : Bool) :
    M.step x coin c = c := by
  simp [step, hout]

theorem run_add_of_output {x : Word} {coins : CoinTape} {t : ℕ} {b : Bool}
    (hout : M.output (M.run x coins t).state = some b) (d : ℕ) :
    M.run x coins (t + d) = M.run x coins t := by
  induction d with
  | zero => simp only [Nat.add_zero]
  | succ d ih =>
    rw [Nat.add_succ, run_succ, ih]
    exact step_eq_self_of_output hout _

theorem run_later_of_output {x : Word} {coins : CoinTape} {t u : ℕ} {b : Bool}
    (hout : M.output (M.run x coins t).state = some b) (htu : t ≤ u) :
    M.run x coins u = M.run x coins t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  exact run_add_of_output hout d

theorem halted_outputs_eq {x : Word} {coins : CoinTape} {t u : ℕ} {b b' : Bool}
    (ht : M.output (M.run x coins t).state = some b)
    (hu : M.output (M.run x coins u).state = some b') : b = b' := by
  rcases le_total t u with htu | hut
  · rw [run_later_of_output ht htu] at hu
    exact Option.some.inj (ht.symm.trans hu)
  · rw [run_later_of_output hu hut] at ht
    exact Option.some.inj (ht.symm.trans hu)

theorem HaltsBy.mono {x : Word} {t u : ℕ} (ht : M.HaltsBy x t) (htu : t ≤ u) :
    M.HaltsBy x u := by
  intro coins
  obtain ⟨b, hb⟩ := ht coins
  exact ⟨b, by rw [run_later_of_output hb htu]; exact hb⟩

theorem step_eq_of_deterministic (hdet : M.Deterministic) (x : Word)
    (c : Configuration q w h x.length) (b₁ b₂ : Bool) :
    M.step x b₁ c = M.step x b₂ c := by
  unfold Deterministic at hdet
  cases b₁ <;> cases b₂ <;> simp only [step, hdet]

theorem run_eq_of_deterministic (hdet : M.Deterministic) (x : Word)
    (coins₁ coins₂ : CoinTape) (t : ℕ) :
    M.run x coins₁ t = M.run x coins₂ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, run_succ, ih]
    exact step_eq_of_deterministic hdet x _ _ _

@[simp] theorem spaceThrough_zero (x : Word) (coins : CoinTape) :
    M.spaceThrough x coins 0 = w := by
  simp [spaceThrough]

theorem spaceThrough_mono (x : Word) (coins : CoinTape) :
    Monotone (M.spaceThrough x coins) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro k _
  apply Finset.card_le_card
  exact Finset.image_subset_image (Finset.range_mono (Nat.add_le_add_right hst 1))

theorem acceptanceProbability_nonneg (x : Word) (t : ℕ) :
    0 ≤ M.acceptanceProbability x t := by
  unfold acceptanceProbability
  positivity

theorem acceptanceProbability_le_one (x : Word) (t : ℕ) :
    M.acceptanceProbability x t ≤ 1 := by
  unfold acceptanceProbability
  apply (div_le_one (by positivity : (0 : ℚ) < 2 ^ t)).2
  have hc : (Finset.univ.filter (fun bits : Fin t → Bool =>
      M.output (M.run x (extendCoins bits) t).state = some true)).card ≤ 2 ^ t := by
    simpa using Finset.card_le_card (Finset.filter_subset
      (fun bits : Fin t → Bool => M.output (M.run x (extendCoins bits) t).state = some true)
      Finset.univ)
  exact_mod_cast hc

theorem acceptanceProbability_eq_of_output {x : Word} {t : ℕ} {b : Bool}
    (hout : ∀ coins : CoinTape, M.output (M.run x coins t).state = some b) :
    M.acceptanceProbability x t = if b then 1 else 0 := by
  cases b <;> simp [acceptanceProbability, hout]

theorem Decides.output_at_halt {A : Language} (hdec : M.Decides A)
    {x : Word} {t : ℕ} (hhalt : M.HaltsBy x t) :
    ∃ b : Bool, (b = true ↔ x ∈ A) ∧
      ∀ coins : CoinTape, M.output (M.run x coins t).state = some b := by
  obtain ⟨u, b, hb, hx⟩ := hdec x
  refine ⟨b, hb, ?_⟩
  intro coins
  obtain ⟨b', hb'⟩ := hhalt coins
  have heq : b' = b := halted_outputs_eq hb' (hx coins)
  simpa [heq] using hb'

end Machine

theorem clocked_exact_decider_mem_RL_and_BPL {A : Language} {q w h : ℕ}
    {M : Machine q w h} (hspace : M.LogSpace) (hdec : M.Decides A)
    {c k : ℕ} (hc : 0 < c)
    (hhalt : ∀ x : Word, M.HaltsBy x (polynomialClock c k x.length)) :
    A ∈ RL ∧ A ∈ BPL := by
  have hy : ∀ x ∈ A,
      M.acceptanceProbability x (polynomialClock c k x.length) = 1 := by
    intro x hx
    obtain ⟨b, hb, hout⟩ := hdec.output_at_halt (hhalt x)
    have hbt : b = true := hb.mpr hx
    simpa [hbt] using Machine.acceptanceProbability_eq_of_output hout
  have hn : ∀ x ∉ A,
      M.acceptanceProbability x (polynomialClock c k x.length) = 0 := by
    intro x hx
    obtain ⟨b, hb, hout⟩ := hdec.output_at_halt (hhalt x)
    have hbf : b = false := Bool.eq_false_iff.mpr (fun hbt => hx (hb.mp hbt))
    simpa [hbf] using Machine.acceptanceProbability_eq_of_output hout
  constructor
  · refine ⟨q, w, h, M, hspace, c, k, hc, ?_⟩
    intro x
    refine ⟨hhalt x, ?_, hn x⟩
    intro hx
    rw [hy x hx]
    norm_num
  · refine ⟨q, w, h, M, hspace, c, k, hc, ?_⟩
    intro x
    refine ⟨hhalt x, ?_, ?_⟩
    · intro hx
      rw [hy x hx]
      norm_num
    · intro hx
      rw [hn x hx]
      norm_num

theorem intervals_subset_visited (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hp : ∀ t, p t - 1 ≤ p (t + 1) ∧ p (t + 1) ≤ p t + 1) :
    ∀ t, Finset.Icc 0 (p t) ⊆ (Finset.range (t + 1)).image p ∧
      Finset.Icc (p t) 0 ⊆ (Finset.range (t + 1)).image p := by
  intro t
  induction t with
  | zero => simp [hp0]
  | succ t ih =>
    have hsub : (Finset.range (t + 1)).image p ⊆
        (Finset.range (t + 1 + 1)).image p :=
      Finset.image_subset_image (Finset.range_mono (by omega))
    have hlast : p (t + 1) ∈ (Finset.range (t + 1 + 1)).image p := by
      exact Finset.mem_image.mpr ⟨t + 1, by simp, rfl⟩
    constructor
    · intro z hz
      obtain ⟨hz0, hzp⟩ := Finset.mem_Icc.mp hz
      by_cases hzt : z ≤ p t
      · exact hsub (ih.1 (Finset.mem_Icc.mpr ⟨hz0, hzt⟩))
      · have heq : z = p (t + 1) := by have := (hp t).2; omega
        simpa [heq] using hlast
    · intro z hz
      obtain ⟨hpz, hz0⟩ := Finset.mem_Icc.mp hz
      by_cases htz : p t ≤ z
      · exact hsub (ih.2 (Finset.mem_Icc.mpr ⟨htz, hz0⟩))
      · have heq : z = p (t + 1) := by have := (hp t).1; omega
        simpa [heq] using hlast

theorem abs_le_visited_card (p : ℕ → ℤ) (hp0 : p 0 = 0)
    (hp : ∀ t, p t - 1 ≤ p (t + 1) ∧ p (t + 1) ≤ p t + 1) (t : ℕ) :
    |p t| ≤ (((Finset.range (t + 1)).image p).card : ℤ) := by
  obtain ⟨hpos, hneg⟩ := intervals_subset_visited p hp0 hp t
  have h₁ := Finset.card_le_card hpos
  have h₂ := Finset.card_le_card hneg
  rw [Int.card_Icc] at h₁ h₂
  rw [abs_le]
  omega

namespace Machine

variable {q w h : ℕ} {M : Machine q w h}

theorem workPos_step_bounds (x : Word) (coins : CoinTape) (t : ℕ) (k : Fin w) :
    (M.run x coins t).workPos k - 1 ≤ (M.run x coins (t + 1)).workPos k ∧
      (M.run x coins (t + 1)).workPos k ≤ (M.run x coins t).workPos k + 1 := by
  rw [run_succ]
  unfold step
  cases hout : M.output (M.run x coins t).state with
  | some b => simp
  | none =>
    dsimp
    unfold Direction.move
    split <;> omega

theorem workPos_abs_le_space (x : Word) (coins : CoinTape) (t : ℕ) (k : Fin w) :
    |(M.run x coins t).workPos k| ≤ (M.spaceThrough x coins t : ℤ) := by
  have hp := abs_le_visited_card (fun s => (M.run x coins s).workPos k)
    (by rfl) (fun s => M.workPos_step_bounds x coins s k) t
  have hcard : ((Finset.range (t + 1)).image
      (fun s => (M.run x coins s).workPos k)).card ≤ M.spaceThrough x coins t := by
    unfold spaceThrough
    exact Finset.single_le_sum
      (f := fun k : Fin w => ((Finset.range (t + 1)).image
        (fun s => (M.run x coins s).workPos k)).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  exact hp.trans (by exact_mod_cast hcard)

theorem work_eq_false_outside {x : Word} {coins : CoinTape} {s : ℕ}
    (hspace : ∀ t, M.spaceThrough x coins t ≤ s) (t : ℕ) (k : Fin w) (z : ℤ)
    (hz : (s : ℤ) < |z|) : (M.run x coins t).work k z = false := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hpos : |(M.run x coins t).workPos k| ≤ (s : ℤ) :=
      (M.workPos_abs_le_space x coins t k).trans (by exact_mod_cast hspace t)
    have hne : z ≠ (M.run x coins t).workPos k := by
      intro heq
      rw [heq] at hz
      exact (not_lt_of_ge hpos) hz
    rw [run_succ]
    unfold step
    cases hout : M.output (M.run x coins t).state <;> simp [hne, ih]

end Machine

abbrev ConfigurationCode (q w h n s : ℕ) :=
  Fin (q + 1) × (Fin h → Fin (n + 2)) × (Fin w → Fin (2 * s + 1)) ×
    (Fin w → Fin (2 * s + 1) → Bool)

def cellPosition (s : ℕ) (i : Fin (2 * s + 1)) : ℤ := (i.val : ℤ) - s

def cellIndex {s : ℕ} (z : ℤ) (hz : |z| ≤ (s : ℤ)) : Fin (2 * s + 1) :=
  ⟨(z + s).toNat, by obtain ⟨_, _⟩ := abs_le.mp hz; omega⟩

@[simp] theorem cellPosition_cellIndex {s : ℕ} (z : ℤ) (hz : |z| ≤ (s : ℤ)) :
    cellPosition s (cellIndex z hz) = z := by
  obtain ⟨_, _⟩ := abs_le.mp hz
  dsimp [cellPosition, cellIndex]
  omega

namespace Configuration

variable {q w h n s : ℕ}

def encode (c : Configuration q w h n) (hp : ∀ k, |c.workPos k| ≤ (s : ℤ)) :
    ConfigurationCode q w h n s :=
  (c.state, c.inputPos, (fun k => cellIndex (c.workPos k) (hp k)),
    (fun k i => c.work k (cellPosition s i)))

theorem eq_of_encode_eq {c d : Configuration q w h n}
    (hpc : ∀ k, |c.workPos k| ≤ (s : ℤ))
    (hpd : ∀ k, |d.workPos k| ≤ (s : ℤ))
    (hwc : ∀ k z, (s : ℤ) < |z| → c.work k z = false)
    (hwd : ∀ k z, (s : ℤ) < |z| → d.work k z = false)
    (he : c.encode hpc = d.encode hpd) : c = d := by
  have hs : c.state = d.state := congrArg Prod.fst he
  have hi : c.inputPos = d.inputPos := congrArg (fun a => a.2.1) he
  have hp : c.workPos = d.workPos := by
    funext k
    have he' := congrArg (fun a : ConfigurationCode q w h n s =>
      cellPosition s (a.2.2.1 k)) he
    simpa [encode] using he'
  have hw : c.work = d.work := by
    funext k z
    by_cases hz : |z| ≤ (s : ℤ)
    · have he' := congrArg (fun a : ConfigurationCode q w h n s =>
        a.2.2.2 k (cellIndex z hz)) he
      simpa [encode] using he'
    · rw [hwc k z (lt_of_not_ge hz), hwd k z (lt_of_not_ge hz)]
  cases c
  cases d
  cases hs
  cases hi
  cases hp
  cases hw
  rfl

end Configuration

namespace Machine

variable {q w h : ℕ} {M : Machine q w h}

theorem run_add_eq_of_eq (hdet : M.Deterministic) {x : Word}
    {coins : CoinTape} {t u : ℕ} (he : M.run x coins t = M.run x coins u) (d : ℕ) :
    M.run x coins (t + d) = M.run x coins (u + d) := by
  induction d with
  | zero => simpa using he
  | succ d ih =>
    rw [Nat.add_succ, Nat.add_succ, run_succ, run_succ, ih]
    exact step_eq_of_deterministic hdet x _ _ _

theorem haltsBy_card_codes (hdet : M.Deterministic) {x : Word} {s : ℕ}
    (hspace : ∀ t, M.spaceThrough x (fun _ => false) t ≤ s)
    (hhalt : ∃ t b, M.output (M.run x (fun _ => false) t).state = some b) :
    M.HaltsBy x (Fintype.card (ConfigurationCode q w h x.length s)) := by
  have hp : ∀ t k, |(M.run x (fun _ => false) t).workPos k| ≤ (s : ℤ) := by
    intro t k
    exact (M.workPos_abs_le_space x (fun _ => false) t k).trans
      (by exact_mod_cast hspace t)
  have hw : ∀ t k z, (s : ℤ) < |z| →
      (M.run x (fun _ => false) t).work k z = false :=
    fun t k z hz => M.work_eq_false_outside hspace t k z hz
  let T := Nat.find hhalt
  obtain ⟨b, hb⟩ : ∃ b, M.output (M.run x (fun _ => false) T).state = some b :=
    Nat.find_spec hhalt
  have htmin : ∀ t b, M.output (M.run x (fun _ => false) t).state = some b → T ≤ t := by
    intro t b ht
    exact Nat.find_min' hhalt ⟨b, ht⟩
  have hinj : Function.Injective (fun i : Fin (T + 1) =>
      (M.run x (fun _ => false) i.val).encode (hp i.val)) := by
    intro i j hij
    have he : M.run x (fun _ => false) i.val = M.run x (fun _ => false) j.val :=
      Configuration.eq_of_encode_eq (hp i.val) (hp j.val) (hw i.val) (hw j.val) hij
    have hle : ∀ a c : Fin (T + 1),
        M.run x (fun _ => false) a.val = M.run x (fun _ => false) c.val → c.val ≤ a.val := by
      intro a c hac
      by_contra hca
      have hadd := M.run_add_eq_of_eq hdet hac (T - c.val)
      have hct : c.val + (T - c.val) = T := by omega
      rw [hct] at hadd
      have ht : M.output (M.run x (fun _ => false) (a.val + (T - c.val))).state = some b := by
        rw [hadd]
        exact hb
      have := htmin _ b ht
      omega
    exact Fin.ext (Nat.le_antisymm (hle j i he.symm) (hle i j he))
  have hcard : T + 1 ≤ Fintype.card (ConfigurationCode q w h x.length s) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  intro coins
  refine ⟨b, ?_⟩
  have hT : M.output (M.run x coins T).state = some b := by
    rw [M.run_eq_of_deterministic hdet x coins (fun _ => false) T]
    exact hb
  rw [M.run_later_of_output hT (by omega)]
  exact hT

end Machine

theorem card_configurationCode (q w h n s : ℕ) :
    Fintype.card (ConfigurationCode q w h n s) =
      (q + 1) * (n + 2) ^ h * (2 * s + 1) ^ w * 2 ^ ((2 * s + 1) * w) := by
  simp only [ConfigurationCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, pow_mul]
  ring

theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 (n + 2) ≤ 2 * (n + 2) := by
  have hpos : 0 < Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) (by omega : 1 < n + 2)
  simp only [Nat.pred_eq_sub_one] at hlt
  calc
    2 ^ Nat.clog 2 (n + 2) = 2 ^ (Nat.clog 2 (n + 2) - 1 + 1) := by
      congr 1
    _ = 2 ^ (Nat.clog 2 (n + 2) - 1) * 2 := pow_succ _ _
    _ ≤ 2 * (n + 2) := by omega

theorem card_configurationCode_log_bound (q w h c n : ℕ) :
    Fintype.card (ConfigurationCode q w h n (c * Nat.clog 2 (n + 2))) ≤
      polynomialClock ((q + 1) * (2 * c + 1) ^ w * (2 ^ (2 * c * w) * 2 ^ w))
        (h + w + 2 * c * w) n := by
  have hl : Nat.clog 2 (n + 2) ≤ n + 2 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hhead : 2 * (c * Nat.clog 2 (n + 2)) + 1 ≤ (2 * c + 1) * (n + 2) := by
    calc
      2 * (c * Nat.clog 2 (n + 2)) + 1 = (2 * c) * Nat.clog 2 (n + 2) + 1 := by ring
      _ ≤ (2 * c) * (n + 2) + (n + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hl) (by omega)
      _ = (2 * c + 1) * (n + 2) := by ring
  have hbits : 2 ^ ((2 * (c * Nat.clog 2 (n + 2)) + 1) * w) ≤
      (2 * (n + 2)) ^ (2 * c * w) * 2 ^ w := by
    have he : (2 * (c * Nat.clog 2 (n + 2)) + 1) * w =
        Nat.clog 2 (n + 2) * (2 * c * w) + w := by ring
    rw [he, pow_add, pow_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (two_pow_clog_le n) _)
  rw [card_configurationCode]
  calc
    _ ≤ (q + 1) * (n + 2) ^ h * (((2 * c + 1) * (n + 2)) ^ w) *
        ((2 * (n + 2)) ^ (2 * c * w) * 2 ^ w) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhead w)) hbits
    _ = _ := by simp only [polynomialClock, mul_pow, pow_add]; ring

namespace Machine

variable {q w h : ℕ} {M : Machine q w h}

theorem Deterministic.polynomial_clock (hdet : M.Deterministic)
    (hspace : M.LogSpace) {A : Language} (hdec : M.Decides A) :
    ∃ c k : ℕ, 0 < c ∧ ∀ x : Word, M.HaltsBy x (polynomialClock c k x.length) := by
  obtain ⟨c, _hc, hs⟩ := hspace
  refine ⟨(q + 1) * (2 * c + 1) ^ w * (2 ^ (2 * c * w) * 2 ^ w),
    h + w + 2 * c * w, by positivity, ?_⟩
  intro x
  obtain ⟨t, b, _hb, hout⟩ := hdec x
  have hclock := M.haltsBy_card_codes hdet (fun u => hs x (fun _ => false) u)
    ⟨t, b, hout (fun _ => false)⟩
  exact hclock.mono (card_configurationCode_log_bound q w h c x.length)

end Machine

theorem L_subset_RL : L ⊆ RL := by
  intro A hA
  obtain ⟨q, w, h, M, hdet, hspace, hdec⟩ := hA
  obtain ⟨c, k, hc, hclock⟩ := hdet.polynomial_clock hspace hdec
  exact (clocked_exact_decider_mem_RL_and_BPL hspace hdec hc hclock).1

theorem L_subset_BPL : L ⊆ BPL := by
  intro A hA
  obtain ⟨q, w, h, M, hdet, hspace, hdec⟩ := hA
  obtain ⟨c, k, hc, hclock⟩ := hdet.polynomial_clock hspace hdec
  exact (clocked_exact_decider_mem_RL_and_BPL hspace hdec hc hclock).2

theorem inverse_cubic_le_eighth (n : ℕ) :
    (1 : ℚ) / ((n : ℚ) + 2) ^ 3 ≤ 1 / 8 := by
  have hm : (2 : ℚ) ≤ (n : ℚ) + 2 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hden : (8 : ℚ) ≤ ((n : ℚ) + 2) ^ 3 := by
    calc
      (8 : ℚ) = 2 ^ 3 := by norm_num
      _ ≤ ((n : ℚ) + 2) ^ 3 := by gcongr
  exact (div_le_iff₀ (by positivity : (0 : ℚ) < ((n : ℚ) + 2) ^ 3)).mpr (by linarith)

theorem no_input_approximation_bound {p z : ℚ} (hp : p ≤ 1 / 3)
    (herr : |z - p| ≤ 1 / 8) : z ≤ 11 / 24 ∧ z < 1 / 2 := by
  have h := (abs_le.mp herr).2
  constructor <;> linarith

theorem yes_input_approximation_bound {p z : ℚ} (hp : 2 / 3 ≤ p)
    (herr : |z - p| ≤ 1 / 8) : 13 / 24 ≤ z ∧ 1 / 2 < z := by
  have h := (abs_le.mp herr).1
  constructor <;> linarith

theorem two_trial_probability_gap {p : ℚ} (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    3 / 4 ≤ 1 - (1 - p) ^ 2 := by
  have ht := mul_nonneg (sub_nonneg.mpr hp)
    (sub_nonneg.mpr hp1)
  nlinarith

end ExactDerandomization

end OAI
