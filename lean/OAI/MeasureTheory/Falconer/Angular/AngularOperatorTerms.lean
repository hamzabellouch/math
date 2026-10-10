import OAI.MeasureTheory.Falconer.Estimates.OrderedLeibniz
import OAI.MeasureTheory.Falconer.Angular.InverseStationaryOperators
import Mathlib.Algebra.BigOperators.Ring.List

namespace OAI

namespace PlanarFalconer
open scoped ContDiff
namespace AngularDifferentialExpr

noncomputable def terms : AngularDifferentialExpr → List (ℂ × ℕ)
  | .term c k => [(c,k)]
  | .add p q => p.terms ++ q.terms
  | .comp p q => p.terms.flatMap (fun a => q.terms.map (fun b => (a.1*b.1,a.2+b.2)))

theorem terms_order (p : AngularDifferentialExpr) {a : ℂ × ℕ} (ha : a ∈ p.terms) :
    a.2 ≤ p.order := by
  induction p generalizing a with
  | term c k =>
    have he : a = (c,k) := List.mem_singleton.mp ha
    subst a
    exact le_rfl
  | add p q hp hq =>
    obtain ha | ha := List.mem_append.mp ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | comp p q hp hq =>
    obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact Nat.add_le_add (hp hb) (hq hc)

theorem terms_cost (p : AngularDifferentialExpr) :
    (p.terms.map (fun a => ‖a.1‖)).sum = p.cost := by
  induction p with
  | term c k => simp [terms,cost]
  | add p q hp hq => simp [terms,cost,hp,hq]
  | comp p q hp hq =>
    simp only [terms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def,norm_mul,List.sum_map_mul_left,List.sum_map_mul_right,hp,hq,cost]

theorem terms_derivative (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (p.apply f) x =
      (p.terms.map (fun a => a.1*iteratedDeriv (n+a.2) f x)).sum := by
  induction p generalizing f n with
  | term c k => simp [terms,apply,iteratedDeriv_const_mul_field,iteratedDeriv_iterated]
  | add p q hp hq =>
    simp only [terms,List.map_append,List.sum_append,apply]
    rw [iteratedDeriv_fun_add (smooth_finite (p.apply_contDiff hf) n x)
      (smooth_finite (q.apply_contDiff hf) n x),hp hf,hq hf]
  | comp p q hp hq =>
    change iteratedDeriv n (p.apply (q.apply f)) x = _
    rw [hp (q.apply_contDiff hf)]
    simp only [terms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [hq hf,← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro b hb
    simp [Nat.add_assoc,mul_assoc]

theorem terms_apply (p : AngularDifferentialExpr) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    p.apply f x = (p.terms.map (fun a => a.1*iteratedDeriv a.2 f x)).sum := by
  simpa using p.terms_derivative hf 0 x

end AngularDifferentialExpr

theorem inverseStationaryOperator_terms (j : ℕ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    inverseStationaryOperator j f x =
      ((inverseStationaryExpr j).terms.map (fun a => a.1*iteratedDeriv a.2 f x)).sum :=
  (inverseStationaryExpr j).terms_apply hf x

theorem inverseStationaryOperator_terms_order (j : ℕ) {a : ℂ × ℕ}
    (ha : a ∈ (inverseStationaryExpr j).terms) : a.2 ≤ 2*j :=
  ((inverseStationaryExpr j).terms_order ha).trans (inverseStationaryExpr_order j)

end PlanarFalconer

end OAI
