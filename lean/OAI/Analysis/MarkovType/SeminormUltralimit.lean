import OAI.Analysis.MarkovType.ScalarUltralimit
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

namespace OAI

noncomputable section

open Filter

namespace MarkovSuperreflexivity

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

def seminormULim (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) : Seminorm ℝ E :=
  Seminorm.of (fun x => realULim U (fun n => p n x))
    (by
      intro x y
      have h := realULim_le_realULim U (hb (x + y)) ((hb x).add (hb y))
        (Filter.Eventually.of_forall (fun n => map_add_le_add (p n) x y))
      simpa only [realULim_add U (hb x) (hb y)] using h)
    (by
      intro a x
      have he : (fun n => p n (a • x)) = (fun n => ‖a‖ * p n x) := by
        funext n
        exact map_smul_eq_mul (p n) a x
      change realULim U (fun n => p n (a • x)) =
        ‖a‖ * realULim U (fun n => p n x)
      rw [he, realULim_const_mul U ‖a‖ (hb x)])

@[simp] theorem seminormULim_apply (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) (x : E) :
    seminormULim U p hb x = realULim U (fun n => p n x) := rfl

theorem seminormULim_le (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) (q : Seminorm ℝ E)
    (h : ∀ x : E, ∀ᶠ n in (U : Filter ℕ), p n x ≤ q x) : seminormULim U p hb ≤ q := by
  intro x
  exact realULim_le_of_eventually_le U (hb x) (h x)

theorem le_seminormULim (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) (q : Seminorm ℝ E)
    (h : ∀ x : E, ∀ᶠ n in (U : Filter ℕ), q x ≤ p n x) : q ≤ seminormULim U p hb := by
  intro x
  exact le_realULim_of_eventually_le U (hb x) (h x)

theorem seminormULim_definite (U : Ultrafilter ℕ) (p : ℕ → Seminorm ℝ E)
    (hb : ∀ x : E, RealSeqBounded (fun n => p n x)) (q : Seminorm ℝ E)
    (hq : ∀ x : E, q x = 0 → x = 0)
    (h : ∀ x : E, ∀ᶠ n in (U : Filter ℕ), q x ≤ p n x) :
    ∀ x : E, seminormULim U p hb x = 0 → x = 0 := by
  intro x hx
  apply hq x
  apply le_antisymm
  · exact (le_seminormULim U p hb q h x).trans_eq hx
  · exact apply_nonneg q x

end MarkovSuperreflexivity

end

end OAI
