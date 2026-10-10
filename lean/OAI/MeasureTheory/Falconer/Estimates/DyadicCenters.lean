import OAI.MeasureTheory.Falconer.Estimates.DyadicTree
import OAI.MeasureTheory.Falconer.Incidence.GridCount

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

def dyadicCode {d : ℕ} : List (Fin d → Bool) → Fin d → ℤ
  | [] => fun _ => 0
  | b :: p => fun i => (if b i then (2 : ℤ)^p.length else 0) + dyadicCode p i

theorem dyadicCode_bounds {d : ℕ} (p : List (Fin d → Bool)) (i : Fin d) :
    0 ≤ dyadicCode p i ∧ dyadicCode p i < (2 : ℤ)^p.length := by
  induction p with
  | nil => simp [dyadicCode]
  | cons b p ih =>
    simp only [dyadicCode, List.length_cons, pow_succ]
    split <;> omega

theorem DyadicCube.descendant_origin {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (i : Fin d) :
    (Q.descendant p).origin i =
      Q.origin i + (Q.side / (2 : ℝ)^p.length) * (dyadicCode p i : ℝ) := by
  induction p generalizing Q with
  | nil => simp [DyadicCube.descendant, dyadicCode]
  | cons b p ih =>
    rw [DyadicCube.descendant, ih]
    simp only [DyadicCube.child, PiLp.toLp_apply, dyadicCode, List.length_cons, pow_succ]
    cases b i <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
    · push_cast
      ring
    · push_cast
      field_simp
      ring

theorem DyadicCube.descendant_center {d : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (i : Fin d) :
    (Q.descendant p).center i =
      Q.origin i + (Q.side / (2 : ℝ)^p.length)/2 +
        (Q.side / (2 : ℝ)^p.length) * (dyadicCode p i : ℝ) := by
  change (Q.descendant p).origin i + (Q.descendant p).side / 2 = _
  rw [Q.descendant_origin, Q.descendant_side]
  ring

theorem dyadicCode_injective_at_depth {d n : ℕ} {p q : List (Fin d → Bool)}
    (hp : p.length = n) (hq : q.length = n) (heq : dyadicCode p = dyadicCode q) : p = q := by
  classical
  let Q : DyadicCube d := ⟨0,1⟩
  have hQ : 0 < Q.side := by norm_num [Q]
  by_contra hne
  have hc : (Q.descendant p).center = (Q.descendant q).center := by
    ext i
    rw [Q.descendant_center, Q.descendant_center, hp, hq, heq]
  have hleft := (Q.descendant p).center_mem (Q.descendant_side_pos hQ p)
  have hright := (Q.descendant q).center_mem (Q.descendant_side_pos hQ q)
  rw [← hc] at hright
  exact Set.disjoint_left.mp (Q.descendants_disjoint (hp.trans hq.symm) hne) hleft hright

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
