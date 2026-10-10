import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

universe u

inductive DyadicTree (X : Type u) where
  | leaf : X → DyadicTree X
  | node : DyadicTree X → DyadicTree X → DyadicTree X

namespace DyadicTree

variable {X : Type u}

noncomputable def terminal (t : DyadicTree X) (f : X → ℝ) : ℝ :=
  match t with
  | leaf x => f x
  | node t s => (terminal t f + terminal s f) / 2

@[simp] theorem terminal_leaf (x : X) (f : X → ℝ) :
    terminal (leaf x) f = f x := rfl

@[simp] theorem terminal_node (t s : DyadicTree X) (f : X → ℝ) :
    terminal (node t s) f = (terminal t f + terminal s f) / 2 := rfl

theorem terminal_mono (t : DyadicTree X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    terminal t f ≤ terminal t g := by
  induction t with
  | leaf x => exact h x
  | node t s ht hs => simp only [terminal_node]; linarith

@[simp] theorem terminal_const (t : DyadicTree X) (c : ℝ) :
    terminal t (fun _ => c) = c := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [terminal_node, ht, hs]; ring

theorem terminal_linear (t : DyadicTree X) (f g : X → ℝ) (a b : ℝ) :
    terminal t (fun x => a * f x + b * g x) =
      a * terminal t f + b * terminal t g := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [terminal_node, ht, hs]; ring

def height : DyadicTree X → ℕ
  | leaf _ => 0
  | node t s => max (height t) (height s) + 1

def Full : ℕ → DyadicTree X → Prop
  | 0, leaf _ => True
  | 0, node _ _ => False
  | _ + 1, leaf _ => False
  | n + 1, node t s => Full n t ∧ Full n s

def pad : ℕ → DyadicTree X → DyadicTree X
  | 0, t => t
  | n + 1, leaf x => node (pad n (leaf x)) (pad n (leaf x))
  | n + 1, node t s => node (pad n t) (pad n s)

theorem pad_full (n : ℕ) (t : DyadicTree X) (h : height t ≤ n) :
    Full n (pad n t) := by
  induction n generalizing t with
  | zero =>
      cases t with
      | leaf x => trivial
      | node t s => simp [height] at h
  | succ n ih =>
      cases t with
      | leaf x =>
          exact ⟨ih (leaf x) (Nat.zero_le n), ih (leaf x) (Nat.zero_le n)⟩
      | node t s =>
          have hm : max (height t) (height s) ≤ n := Nat.le_of_succ_le_succ h
          exact ⟨ih t ((le_max_left _ _).trans hm),
            ih s ((le_max_right _ _).trans hm)⟩

@[simp] theorem terminal_pad (n : ℕ) (t : DyadicTree X) (f : X → ℝ) :
    terminal (pad n t) f = terminal t f := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp only [pad, terminal_node, ih]; ring
      | node t s => simp only [pad, terminal_node, ih]

variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

noncomputable def root : DyadicTree X → X
  | leaf x => x
  | node t s => (2 : ℝ)⁻¹ • (root t + root s)

@[simp] theorem root_leaf (x : X) : root (leaf x) = x := rfl

@[simp] theorem root_node (t s : DyadicTree X) :
    root (node t s) = (2 : ℝ)⁻¹ • (root t + root s) := rfl

noncomputable def moment (p : ℝ) (t : DyadicTree X) : ℝ :=
  terminal t (fun x => ‖x‖ ^ p)

omit sectionNormedSpaceℝX in
@[simp] theorem moment_leaf [NormedSpace ℝ X] (p : ℝ) (x : X) : moment p (leaf x) = ‖x‖ ^ p := rfl

omit sectionNormedSpaceℝX in
@[simp] theorem moment_node [NormedSpace ℝ X] (p : ℝ) (t s : DyadicTree X) :
    moment p (node t s) = (moment p t + moment p s) / 2 := rfl

noncomputable def energy (p : ℝ) : DyadicTree X → ℝ
  | leaf _ => 0
  | node t s => (energy p t + energy p s) / 2 +
      ‖(2 : ℝ)⁻¹ • (root t - root s)‖ ^ p

@[simp] theorem energy_leaf (p : ℝ) (x : X) : energy p (leaf x) = 0 := rfl

@[simp] theorem energy_node (p : ℝ) (t s : DyadicTree X) :
    energy p (node t s) = (energy p t + energy p s) / 2 +
      ‖(2 : ℝ)⁻¹ • (root t - root s)‖ ^ p := rfl

omit sectionNormedSpaceℝX in
theorem moment_nonneg [NormedSpace ℝ X] (p : ℝ) (t : DyadicTree X) : 0 ≤ moment p t := by
  have h := terminal_mono t (fun x => Real.rpow_nonneg (norm_nonneg x) p)
  simpa only [terminal_const, moment] using h

theorem energy_nonneg (p : ℝ) (t : DyadicTree X) : 0 ≤ energy p t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs =>
      exact add_nonneg (div_nonneg (add_nonneg ht hs) (by norm_num))
        (Real.rpow_nonneg (norm_nonneg _) p)

def translate (a : X) : DyadicTree X → DyadicTree X
  | leaf x => leaf (a + x)
  | node t s => node (translate a t) (translate a s)

def scale (a : ℝ) : DyadicTree X → DyadicTree X
  | leaf x => leaf (a • x)
  | node t s => node (scale a t) (scale a s)

@[simp] theorem root_translate (a : X) (t : DyadicTree X) :
    root (translate a t) = a + root t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [translate, root_node, ht, hs]; module

@[simp] theorem root_scale (a : ℝ) (t : DyadicTree X) :
    root (scale a t) = a • root t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [scale, root_node, ht, hs]; module

@[simp] theorem scale_scale (a b : ℝ) (t : DyadicTree X) :
    scale a (scale b t) = scale (a * b) t := by
  induction t with
  | leaf x => simp only [scale, smul_smul]
  | node t s ht hs => simp only [scale, ht, hs]

@[simp] theorem scale_one (t : DyadicTree X) : scale 1 t = t := by
  induction t with
  | leaf x => simp [scale]
  | node t s ht hs => simp only [scale, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem terminal_translate [NormedSpace ℝ X] (a : X) (t : DyadicTree X) (f : X → ℝ) :
    terminal (translate a t) f = terminal t (fun x => f (a + x)) := by
  induction t with
  | leaf x => rfl
  | node t s ht hs => simp only [translate, terminal_node, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem translate_translate [NormedSpace ℝ X] (a b : X) (t : DyadicTree X) :
    translate a (translate b t) = translate (a + b) t := by
  induction t with
  | leaf x => simp [translate, add_assoc]
  | node t s ht hs => simp only [translate, ht, hs]

omit sectionNormedSpaceℝX in
@[simp] theorem translate_zero [NormedSpace ℝ X] (t : DyadicTree X) : translate 0 t = t := by
  induction t with
  | leaf x => simp [translate]
  | node t s ht hs => simp only [translate, ht, hs]

@[simp] theorem energy_translate (p : ℝ) (a : X) (t : DyadicTree X) :
    energy p (translate a t) = energy p t := by
  induction t with
  | leaf x => rfl
  | node t s ht hs =>
      simp only [translate, energy_node, root_translate, ht, hs,
        add_sub_add_left_eq_sub]

@[simp] theorem moment_scale (p a : ℝ) (t : DyadicTree X) :
    moment p (scale a t) = |a| ^ p * moment p t := by
  induction t with
  | leaf x =>
      simp only [scale, moment_leaf, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg a) (norm_nonneg x)]
  | node t s ht hs => simp only [scale, moment_node, ht, hs]; ring

@[simp] theorem energy_scale (p a : ℝ) (t : DyadicTree X) :
    energy p (scale a t) = |a| ^ p * energy p t := by
  induction t with
  | leaf x => simp [scale]
  | node t s ht hs =>
      simp only [scale, energy_node, root_scale, ht, hs]
      have he : (2 : ℝ)⁻¹ • (a • root t - a • root s) =
          a • ((2 : ℝ)⁻¹ • (root t - root s)) := by module
      rw [he, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg a) (norm_nonneg _)]
      ring

@[simp] theorem root_pad (n : ℕ) (t : DyadicTree X) : root (pad n t) = root t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp only [pad, root_node, ih]; module
      | node t s => simp only [pad, root_node, ih]

omit sectionNormedSpaceℝX in
@[simp] theorem moment_pad [NormedSpace ℝ X] (p : ℝ) (n : ℕ) (t : DyadicTree X) :
    moment p (pad n t) = moment p t := terminal_pad n t _

@[simp] theorem energy_pad {p : ℝ} (hp : 0 < p) (n : ℕ) (t : DyadicTree X) :
    energy p (pad n t) = energy p t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      cases t with
      | leaf x => simp [pad, energy_node, ih, Real.zero_rpow hp.ne']
      | node t s => simp only [pad, energy_node, ih, root_pad]

end DyadicTree
end MarkovSuperreflexivity

end OAI
