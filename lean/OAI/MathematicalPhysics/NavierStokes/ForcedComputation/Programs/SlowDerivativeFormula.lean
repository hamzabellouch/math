import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.MixedNormalFormData

namespace OAI

/-! Exact finite formulas for every mixed derivative of the actual slow force. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Filter
open scoped ContDiff Topology BigOperators

theorem mixedDerivative_quadraticPhase {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ha : ZeroAdvection V) (α : List (Fin 4)) :
    mixedDerivative (fun y => quadraticPhase V y.2 y.1) α =
      mixedDerivative V (α ++ [0]) - mixedDerivative V α := by
  have he : (fun y => quadraticPhase V y.2 y.1) = mixedDerivative V [0] - V := by
    funext y
    simp only [quadraticPhase, ha y.1 y.2, add_zero, timeDerivative_eq hV]
    rfl
  rw [he, mixedDerivative_sub (mixedDerivative_smooth hV _) hV,
    mixedDerivative_append]

theorem mixedDerivative_viscousPhase {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (α : List (Fin 4)) :
    mixedDerivative (fun y => viscousPhase V y.2 y.1) α =
      ∑ j : Fin 3, mixedDerivative V (α ++ [j.succ, j.succ]) := by
  have he : (fun y => viscousPhase V y.2 y.1) =
      ∑ j : Fin 3, mixedDerivative V [j.succ, j.succ] := by
    funext y
    simpa only [viscousPhase, Finset.sum_apply] using laplacian_eq_mixed hV y.1 y.2
  rw [he, mixedDerivative_sum _ (fun j => mixedDerivative_smooth hV _)]
  simp only [mixedDerivative_append]

theorem slowFromRest_mixed_formula {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hzero : ∀ t, t < (1 / 32 : ℝ) → ∀ x, V (t, x) = 0)
    (ha : ZeroAdvection V) (ν : ℝ) (n : ℕ) (β : List (Fin 3))
    {t : ℝ} (ht : -(1 / 2 : ℝ) < t) (x : Space) :
    mixedDerivative (force ν (slowFromRest V))
      (List.replicate n 0 ++ β.map Fin.succ) (t, x) =
      (1 + t)⁻¹ ^ (2 + n) •
        phaseIter 2 (fun s => spatialPhase (fun y => quadraticPhase V y.2 y.1) β (s, x)) n
          (logClock t) -
      ν • ((1 + t)⁻¹ ^ (1 + n) •
        phaseIter 1 (fun s => spatialPhase (fun y => viscousPhase V y.2 y.1) β (s, x)) n
          (logClock t)) := by
  let Q : Velocity := fun y => quadraticPhase V y.2 y.1
  let D : Velocity := fun y => viscousPhase V y.2 y.1
  have hQ : ContDiff ℝ ∞ Q := quadraticPhase_smooth hV
  have hD : ContDiff ℝ ∞ D := viscousPhase_smooth hV
  have hQx : ContDiff ℝ ∞ (fun s => spatialPhase Q β (s, x)) :=
    (spatialPhase_smooth hQ β).comp (contDiff_id.prodMk contDiff_const)
  have hDx : ContDiff ℝ ∞ (fun s => spatialPhase D β (s, x)) :=
    (spatialPhase_smooth hD β).comp (contDiff_id.prodMk contDiff_const)
  rw [mixedDerivative_time_spatial (force_smooth (slowFromRest_smooth hV hzero) ν)]
  have he : (fun s => spatialWord β (fun y => force ν (slowFromRest V) (s, y)) x)
      =ᶠ[𝓝 t] fun s => logarithmicProfile 2 (fun q => spatialPhase Q β (q, x)) s -
        ν • logarithmicProfile 1 (fun q => spatialPhase D β (q, x)) s := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hf : (fun y => force ν (slowFromRest V) (s, y)) = fun y => slowForce ν V (s, y) :=
      funext (slowFromRest_force_eq hV hzero ha ν hs)
    rw [hf]
    exact spatialWord_slowForce hV ν β s x
  rw [he.iteratedDeriv_eq n]
  have hqt := logarithmicProfile_contDiffAt 2 hQx (show -1 < t by linarith)
  have hdt := logarithmicProfile_contDiffAt 1 hDx (show -1 < t by linarith)
  rw [iteratedDeriv_fun_sub (hqt.of_le (by simp))
      ((hdt.const_smul ν).of_le (by simp)), iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_logarithmicProfile 2 n hQx (by linarith),
    iteratedDeriv_logarithmicProfile 1 n hDx (by linarith)]
  rfl

end ForcedComputation

end

end OAI
