import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

namespace OAI

namespace PeriodicTilingThree

abbrev Column (p : ℕ) := Fin (p ^ 2)
abbrev Symbol (p : ℕ) := (ZMod p)ˣ
abbrev Word (p : ℕ) := Column p → Symbol p
abbrev WordArray (p : ℕ) := Column p → ℤ → Symbol p
abbrev Channel (p : ℕ) := Column p ⊕ Fin 2

def Label (p : ℕ) : Channel p → Type
  | .inl _ => Symbol p
  | .inr _ => Unit

instance instFintypeLabel (p : ℕ) [NeZero p] (i : Channel p) : Fintype (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance instDecidableEqLabel (p : ℕ) (i : Channel p) : DecidableEq (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

instance instInhabitedLabel (p : ℕ) (i : Channel p) : Inhabited (Label p i) := by
  cases i <;> dsimp [Label] <;> infer_instance

def Allowed (p : ℕ) (w : Word p) : Prop :=
  ∃ a b : ℤ,
    (¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b) ∧
    ∀ n : Column p,
      let t := a * (n.val : ℤ) + b
      (¬ (p : ℤ) ∣ t → (w n : ZMod p) = (t : ZMod p)) ∧
      ((p : ℤ) ∣ t → ¬ (p : ℤ) ^ 2 ∣ t →
        (w n : ZMod p) = ((t / (p : ℤ) : ℤ) : ZMod p))

def LineRule (p : ℕ) (W : WordArray p) : Prop :=
  ∀ d e : ℤ, Allowed p (fun n => W n (d * (n.val : ℤ) + e))

def NonconstantColumns {p : ℕ} (W : WordArray p) : Prop :=
  ∀ n, ∃ m m' : ℤ, W n m ≠ W n m'

def VerticalPeriod {p : ℕ} (W : WordArray p) (M : ℤ) : Prop :=
  ∀ n m, W n (m + M) = W n m

def affineValue {p : ℕ} (A B C : ZMod p) (n : Column p) (m : ℤ) : ZMod p :=
  A * (n.val : ZMod p) + B * (m : ZMod p) + C

def AffineApproximation {p : ℕ} (W : WordArray p) (A B C : ZMod p) : Prop :=
  (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) ∧
  ∀ n m, affineValue A B C n m ≠ 0 →
    (W n m : ZMod p) = affineValue A B C n m

def lineValue {p : ℕ} (n : Column p) (x : Plane) : ℤ :=
  x.2 + (n.val : ℤ) * x.1

def lineKernelStep {p : ℕ} (n : Column p) : Plane :=
  (1, -(n.val : ℤ))

@[simp] theorem lineValue_vertical {p : ℕ} (n : Column p) (m : ℤ) :
    lineValue n (0, m) = m := by
  simp [lineValue]

noncomputable def allowedWords (p : ℕ) [NeZero p] : Finset (Word p) := by
  classical
  exact Finset.univ.filter (Allowed p)

@[simp] theorem mem_allowedWords {p : ℕ} [NeZero p] (w : Word p) :
    w ∈ allowedWords p ↔ Allowed p w := by
  classical
  simp [allowedWords]

end PeriodicTilingThree

end OAI
