import OAI.Computability.MeanPayoff.InputSize

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

def bitDepth {α : Type} : RandomTree α → ℕ
  | .leaf _ => 0
  | .coin l r => max l.bitDepth r.bitDepth + 1

def read {α : Type} : RandomTree α → (ℕ → Bool) → α
  | .leaf a, _ => a
  | .coin l r, bits => if bits 0 then r.read (fun i => bits (i + 1))
    else l.read (fun i => bits (i + 1))

def readPrefix {α : Type} (t : RandomTree α) {T : ℕ} (bits : Fin T → Bool) : α :=
  t.read (padBits bits)

@[simp] theorem padBits_cons_zero {T : ℕ} (b : Bool) (bits : Fin T → Bool) :
    padBits (Fin.cons b bits) 0 = b := by simp [padBits]

@[simp] theorem padBits_cons_succ {T : ℕ} (b : Bool) (bits : Fin T → Bool) (j : ℕ) :
    padBits (Fin.cons b bits) (j + 1) = padBits bits j := by
  by_cases h : j < T
  · simp only [padBits, Nat.add_lt_add_iff_right, h, ↓reduceDIte]
    rfl
  · simp only [padBits, Nat.add_lt_add_iff_right, h, ↓reduceDIte]

@[simp] theorem readPrefix_leaf {α : Type} (a : α) {T : ℕ} (bits : Fin T → Bool) :
    readPrefix (.leaf a) bits = a := rfl

@[simp] theorem readPrefix_coin_cons {α : Type} (l r : RandomTree α) {T : ℕ}
    (b : Bool) (bits : Fin T → Bool) :
    readPrefix (.coin l r) (Fin.cons b bits) =
      if b then readPrefix r bits else readPrefix l bits := by
  simp only [readPrefix, read, padBits_cons_zero, padBits_cons_succ]

theorem prefix_sum {α : Type} (t : RandomTree α) (f : α → ℚ) (T : ℕ)
    (hT : t.bitDepth ≤ T) :
    ∑ bits : Fin T → Bool, f (t.readPrefix bits) = (2 : ℚ) ^ T * t.expect f := by
  induction T generalizing t with
  | zero =>
    cases t with
    | leaf a => simp [expect]
    | coin l r => simp [bitDepth] at hT
  | succ T ih =>
    cases t with
    | leaf a => simp [expect]
    | coin l r =>
      have hl : l.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have hr : r.bitDepth ≤ T := by simp only [bitDepth] at hT; omega
      have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (T + 1) => Bool))
        (fun bits => f ((coin l r).readPrefix bits))
      rw [← he, Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, readPrefix_coin_cons]
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih l hl, ih r hr]
      simp only [expect, pow_succ]
      ring

theorem prefix_probability {α : Type} (t : RandomTree α) (P : α → Prop) (T : ℕ)
    (hT : t.bitDepth ≤ T) :
    ((Finset.univ.filter (fun bits : Fin T → Bool => P (t.readPrefix bits))).card : ℚ) =
      (2 : ℚ) ^ T * t.probability P := by
  classical
  have h := prefix_sum t (fun a => if P a then (1 : ℚ) else 0) T hT
  simpa only [probability, Finset.sum_boole] using h

theorem game_prefix_success (G : Game) (T : ℕ) (hT : (gameSolve G).bitDepth ≤ T) :
    7 * 2 ^ T ≤ 8 * (Finset.univ.filter
      (fun bits : Fin T → Bool => CorrectSet G ((gameSolve G).readPrefix bits))).card := by
  classical
  have hp := prefix_probability (gameSolve G) (CorrectSet G) T hT
  have hs := gameSolve_success G
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℚ) ≤ 2 ^ T)
  rw [← hp] at hh
  have hh' : (7 : ℚ) * 2 ^ T ≤ 8 * (Finset.univ.filter
      (fun bits : Fin T → Bool => CorrectSet G ((gameSolve G).readPrefix bits))).card := by
    linarith only [hh]
  exact_mod_cast hh'

end RandomTree
end MeanPayoff

namespace MeanPayoff

noncomputable def rootInvocationBound (G : Game) : ℕ :=
  callBound G.n (topWidth G).toNat (parameterRank (rootBudgets G).parameter)

theorem rootInvocationBound_nat (G : Game) :
    rootInvocationBound G ≤ 2 ^ (24000 * (Nat.clog 2 ((input G).length + 2)) ^ 2) := by
  let h := Nat.clog 2 ((input G).length + 2)
  let X := inputScale G
  have hh : 1 ≤ h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simp only [pow_zero]
    omega
  have hn := input_n_le G
  have hr := rootRank_bound G
  have hclog : Nat.clog 2 (G.n + 1) ≤ h :=
    Nat.clog_mono_right (b := 2) (by omega)
  have hrank : parameterRank (rootBudgets G).parameter + 1 ≤ 25 * h := by omega
  have hc := callBase_scale (inputScale_large G) (inputScale_n G) (inputScale_g G)
    (inputScale_s G) (inputScale_log G)
  have hx : X ≤ 2 ^ (24 + h) := by
    have hp := Nat.le_pow_clog (by norm_num : 1 < 2) ((input G).length + 2)
    have hm := Nat.mul_le_mul_left (2 ^ 24) hp
    simpa only [X, inputScale, pow_add] using hm
  have hx37 := Nat.pow_le_pow_left hx 37
  have hcall : callBase G.n (topWidth G).toNat ≤ 2 ^ ((24 + h) * 37) := by
    exact hc.trans (by simpa only [← pow_mul] using hx37)
  have hp := Nat.pow_le_pow_left hcall (parameterRank (rootBudgets G).parameter + 1)
  have he : (24 + h) * 37 * (parameterRank (rootBudgets G).parameter + 1) ≤ 24000 * h ^ 2 := by
    have h24 : 24 + h ≤ 25 * h := by omega
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_right 37 h24) hrank
    nlinarith only [hm]
  unfold rootInvocationBound callBound
  exact hp.trans (by rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) he)

theorem clog_real_le_twice_logb (L : ℕ) :
    (Nat.clog 2 (L + 2) : ℝ) ≤ 2 * Real.logb 2 (L + 2) := by
  have hpos : (0 : ℝ) < L + 2 := by positivity
  have hlog : (1 : ℝ) ≤ Real.logb 2 (L + 2) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).mpr
    simp only [Real.rpow_one]
    linarith only [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.logb 2 (L + 2))
  have he : ⌈Real.logb 2 (L + 2)⌉₊ = Nat.clog 2 (L + 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (L + 2)
  rw [he] at hceil
  linarith only [hceil, hlog]

theorem rootInvocationBound_real (G : Game) :
    (rootInvocationBound G : ℝ) ≤
      (2 : ℝ) ^ (100000 * (Real.logb 2 ((input G).length + 2)) ^ 2) := by
  have hnat := rootInvocationBound_nat G
  have hcast : (rootInvocationBound G : ℝ) ≤
      (2 : ℝ) ^ (24000 * (Nat.clog 2 ((input G).length + 2)) ^ 2) := by exact_mod_cast hnat
  have hc := clog_real_le_twice_logb (input G).length
  have hc0 : (0 : ℝ) ≤ (Nat.clog 2 ((input G).length + 2) : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb 2 ((input G).length + 2) := by linarith only [hc, hc0]
  have hs : 24000 * ((Nat.clog 2 ((input G).length + 2) : ℝ)) ^ 2 ≤
      100000 * (Real.logb 2 ((input G).length + 2)) ^ 2 := by nlinarith only [hc, hc0, hl0]
  apply hcast.trans
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hs


namespace RandomTree

inductive Path {α : Type} : RandomTree α → α → ℕ → Prop
  | leaf (a) : Path (.leaf a) a 0
  | left {l r a d} : Path l a d → Path (.coin l r) a (d + 1)
  | right {l r a d} : Path r a d → Path (.coin l r) a (d + 1)

theorem Path.all {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) {P : α → Prop} (hp : t.All P) : P a := by
  induction h with
  | leaf a => exact hp
  | left h ih => exact ih hp.1
  | right h ih => exact ih hp.2

theorem Path.depth_le {α : Type} {t : RandomTree α} {a : α} {d : ℕ}
    (h : Path t a d) : d ≤ t.bitDepth := by
  induction h with
  | leaf a => exact le_rfl
  | left h ih => dsimp [bitDepth]; omega
  | right h ih => dsimp [bitDepth]; omega

theorem depth_attained {α : Type} (t : RandomTree α) : ∃ a, Path t a t.bitDepth := by
  induction t with
  | leaf a => exact ⟨a, .leaf a⟩
  | coin l r il ir =>
    obtain ⟨a, ha⟩ := il
    obtain ⟨b, hb⟩ := ir
    by_cases h : l.bitDepth ≤ r.bitDepth
    · exact ⟨b, by simpa only [bitDepth, max_eq_right h] using Path.right (l := l) hb⟩
    · exact ⟨a, by simpa only [bitDepth, max_eq_left (le_of_not_ge h)] using Path.left (r := r) ha⟩

theorem path_bind_iff {α β : Type} (t : RandomTree α) (f : α → RandomTree β)
    (b : β) (d : ℕ) : Path (t.bind f) b d ↔
      ∃ a d₁ d₂, Path t a d₁ ∧ Path (f a) b d₂ ∧ d = d₁ + d₂ := by
  induction t generalizing d with
  | leaf a =>
    constructor
    · intro h; exact ⟨a, 0, d, .leaf a, h, by omega⟩
    · rintro ⟨a', d₁, d₂, h, hf, he⟩
      cases h
      simpa only [leaf_bind, he, Nat.zero_add] using hf
  | coin l r il ir =>
    constructor
    · intro h
      cases h with
      | left h =>
        obtain ⟨a, d₁, d₂, h₁, h₂, he⟩ := (il _).mp h
        exact ⟨a, d₁ + 1, d₂, .left h₁, h₂, by omega⟩
      | right h =>
        obtain ⟨a, d₁, d₂, h₁, h₂, he⟩ := (ir _).mp h
        exact ⟨a, d₁ + 1, d₂, .right h₁, h₂, by omega⟩
    · rintro ⟨a, d₁, d₂, h₁, h₂, he⟩
      cases h₁ with
      | left h =>
        subst d
        rw [Nat.add_right_comm]
        exact .left ((il _).mpr ⟨a, _, d₂, h, h₂, rfl⟩)
      | right h =>
        subst d
        rw [Nat.add_right_comm]
        exact .right ((ir _).mpr ⟨a, _, d₂, h, h₂, rfl⟩)

theorem path_map_iff {α β : Type} (t : RandomTree α) (f : α → β) (b : β) (d : ℕ) :
    Path (t.map f) b d ↔ ∃ a, Path t a d ∧ f a = b := by
  rw [map, path_bind_iff]
  constructor
  · rintro ⟨a, d₁, d₂, h₁, h₂, he⟩
    cases h₂
    exact ⟨a, by simpa only [he, Nat.add_zero] using h₁, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨a, d, 0, h, .leaf _, by omega⟩

@[simp] theorem bitDepth_map {α β : Type} (t : RandomTree α) (f : α → β) :
    (t.map f).bitDepth = t.bitDepth := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simpa only [map, bind, bitDepth] using congrArg₂ (fun x y => max x y + 1) il ir

@[simp] theorem bitDepth_uniformBelow (k : ℕ) : (uniformBelow k).bitDepth = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [uniformBelow, bitDepth, bitDepth_map, ih, max_self]

end RandomTree

namespace Counted

def Resource {α : Type} (t : Counted α) (K E : ℕ) : Prop :=
  ∀ p d, RandomTree.Path t.tree p d → d ≤ K * p.2 + E

theorem resource_pure {α : Type} (a : α) (K E : ℕ) : (pure a).Resource K E := by
  intro p d h
  cases h
  exact Nat.zero_le _

theorem resource_mono {α : Type} {t : Counted α} {K E F : ℕ}
    (h : t.Resource K E) (hle : E ≤ F) : t.Resource K F := by
  intro p d hp
  exact (h p d hp).trans (Nat.add_le_add_left hle _)

theorem resource_map {α β : Type} {t : Counted α} (f : α → β) {K E : ℕ}
    (h : t.Resource K E) : (t.map f).Resource K E := by
  intro p d hp
  obtain ⟨q, hq, rfl⟩ := (RandomTree.path_map_iff _ _ _ _).mp hp
  exact h q d hq

theorem resource_bind {α β : Type} {t : Counted α} (f : α → Counted β) {K E F : ℕ}
    (h : t.Resource K E) (hf : ∀ a, (f a).Resource K F) : (t.bind f).Resource K (E + F) := by
  intro p d hp
  obtain ⟨q, d₁, d₂, hq, hp', he⟩ := (RandomTree.path_bind_iff _ _ _ _).mp hp
  obtain ⟨r, hr, rfl⟩ := (RandomTree.path_map_iff _ _ _ _).mp hp'
  have h₁ := h q d₁ hq
  have h₂ := hf q.1 r d₂ hr
  dsimp only [Prod.snd]
  rw [Nat.mul_add]
  omega

theorem resource_lift {α : Type} (t : RandomTree α) (K : ℕ) :
    (lift t).Resource K t.bitDepth := by
  intro p d hp
  obtain ⟨a, ha, rfl⟩ := (RandomTree.path_map_iff _ _ _ _).mp hp
  simpa using ha.depth_le

theorem resource_charge {α : Type} {t : Counted α} {K : ℕ} (h : t.Resource K K) :
    (t.charge 1).Resource K 0 := by
  intro p d hp
  obtain ⟨q, hq, rfl⟩ := (RandomTree.path_map_iff _ _ _ _).mp hp
  have hh := h q d hq
  dsimp only [Prod.snd]
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem resource_trials {α : Type} {t : Counted α} {K E : ℕ} (h : t.Resource K E) (J : ℕ) :
    (trials t J).Resource K (J * E) := by
  induction J with
  | zero => exact resource_pure _ _ _
  | succ J ih =>
    simpa only [trials, Nat.succ_mul, Nat.add_comm] using
      resource_bind (fun a => (trials t J).map (a :: ·)) h (fun a => resource_map _ ih)

theorem resource_traverse {α β : Type} (f : α → Counted β) {K : ℕ}
    (h : ∀ a, (f a).Resource K 0) (as : List α) : (traverse f as).Resource K 0 := by
  induction as with
  | nil => exact resource_pure _ _ _
  | cons a as ih => exact resource_bind _ (h a) (fun _ => resource_map _ ih)

theorem depth_le {α : Type} {t : Counted α} {K E N : ℕ}
    (h : t.Resource K E) (hN : t.Bounded N) : t.erase.bitDepth ≤ K * N + E := by
  rw [erase, RandomTree.bitDepth_map]
  obtain ⟨p, hp⟩ := RandomTree.depth_attained t.tree
  exact (h p _ hp).trans (Nat.add_le_add_right (Nat.mul_le_mul_left K (hp.all hN)) E)

end Counted
end MeanPayoff
end

end OAI
