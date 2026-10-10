import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.Select

namespace OAI

open Matrix

namespace CurrentKS.Descent

def minList : List ℚ → ℚ
  | [] => 1
  | a::as => min a (minList as)

lemma minList_pos (l : List ℚ) (h : ∀ a∈l,0<a) : 0 < minList l := by
  induction l with
  | nil => norm_num [minList]
  | cons a as ih =>
    exact lt_min (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma minList_le {l : List ℚ} {a : ℚ} (ha : a∈l) : minList l≤a := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ha)

def fuel (r : ℚ) : ℕ := ⌈100/r⌉₊+1

lemma fuel_spec {r : ℚ} (hr : 0<r) : (100:ℝ)<(fuel r:ℝ)*(r:ℝ) := by
  have hc : (100:ℚ)/r < (fuel r:ℚ) := by
    have hh := Nat.le_ceil (100/r)
    dsimp [fuel]
    push_cast
    linarith
  have hh : (100:ℚ)<(fuel r:ℚ)*r := (div_lt_iff₀ hr).mp hc
  exact_mod_cast hh

lemma run_value_le {α : Type*} (step : α → Option α) (P : α → Prop) (f : α → ℝ)
    (hp : ∀ x y,P x → step x=some y → P y)
    (hd : ∀ x y,P x → step x=some y → f y≤f x)
    (k : ℕ) (x : α) (hx : P x) : f (run step k x)≤f x := by
  induction k generalizing x with
  | zero => exact le_refl _
  | succ k ih =>
    rw [run]
    cases he : step x with
    | none => exact le_refl _
    | some y => exact (ih y (hp x y hx he)).trans (hd x y hx he)

end CurrentKS.Descent

end OAI
