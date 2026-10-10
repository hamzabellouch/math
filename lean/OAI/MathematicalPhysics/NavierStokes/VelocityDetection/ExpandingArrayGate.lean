import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ExpandingArray
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.GateBounds

namespace OAI

noncomputable section
namespace VelocityDetection.ExpandingArray
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open Expanding Stacks FiniteAddresses UniformDerivatives
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))
    (terminal : Fin N) (ν : ℝ) (m : ℕ)

def gate (n : ℕ) (c : Active hb table (capacity b m n)) (q : ℝ × Coord 2) : Coord 2 :=
  TranslationGates.field (radius ν (K₀ N b m) (D b) n)
    (path hb table terminal ν m n c q.1) (deriv (path hb table terminal ν m n c) q.1) q.2

@[fun_prop] theorem contDiff_gate (n : ℕ) (c : Active hb table (capacity b m n)) :
    ContDiff ℝ ∞ (gate hb table terminal ν m n c) :=
  TranslationGates.contDiff_movingField _ (contDiff_path hb table terminal ν m n c)
    ((contDiff_infty_iff_deriv.mp (contDiff_path hb table terminal ν m n c)).2)

theorem gates_uniformly_bounded (hν : 0 < ν) (hm : 1 ≤ m) (i : Fin 2) :
    Bounded (fun (a : (n : ℕ) × Active hb table (capacity b m n)) q =>
      gate hb table terminal ν m a.1 a.2 q i) := by
  unfold gate
  refine TranslationGates.bounded_movingField
    (I := (n : ℕ) × Active hb table (capacity b m n))
    (fun a => radius ν (K₀ N b m) (D b) a.1)
    (fun a => radius_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) a.1)
    (fun a => path hb table terminal ν m a.1 a.2)
    (fun a => contDiff_path hb table terminal ν m a.1 a.2) ?_ i
  intro j n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨C, hC, hc⟩ := path_derivative_bounds hb table terminal ν m hν hm n
  refine ⟨C, hC, fun a t => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact (hc a.1 a.2 t j).trans
    (div_le_self hC (one_le_pow₀ (duration_ge_one hν (K₀_nonneg N b m) (D_ge_one hb) a.1)))

end VelocityDetection.ExpandingArray
end

end OAI
