import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszScaleError
import OAI.NumberTheory.JointDickman.Analysis.PerronTailDecay

namespace OAI

/-! # Global errors smaller than every fixed logarithmic power -/
namespace JointDickman
open Complex Filter Asymptotics
open scoped Topology

theorem squarefreeRiesz_scale_decay {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : ℝ,
      (fun q : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
        squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)) =o[atTop]
      (fun q => q^b) := by
  obtain ⟨A,C,D,hA,_,hD,hbound⟩ := squarefreeRiesz_scale_error hz hz1
  refine ⟨A,hA,fun b => ?_⟩
  have hg : (fun q : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
      squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)) =O[atTop]
      (fun q => (D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
        (Real.exp q/2)^(-1/2:ℝ)) := by
    apply IsBigO.of_bound C
    filter_upwards [hbound] with q hq
    have hη := perronScaleWidth_pos hA (q := q)
    have hp : 0 ≤ (D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
        (Real.exp q/2)^(-1/2:ℝ) := by positivity
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
    exact hq
  exact hg.trans_isLittleO
    ((perronScale_left_scalar_decay hz hz1.le hD.le hA b).add (perronScale_tail_scalar_decay b))

theorem squarefreeRiesz_global_decay {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : ℝ,
      (fun L : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        squarefreeRieszLocalHankel z (perronLogScaleWidth A L) L) =o[atTop]
      (fun L => L^b) := by
  obtain ⟨A,hA,hdecay⟩ := squarefreeRiesz_scale_decay hz hz1
  refine ⟨A,hA,fun b => ?_⟩
  have h := (hdecay (10*b)).comp_tendsto
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10))
  apply h.congr'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    have he : (L^(1/10:ℝ))^10 = L := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hL]
      norm_num
    simp only [Function.comp_apply]
    rw [he]
    rfl
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    simp only [Function.comp_apply]
    rw [←Real.rpow_mul hL]
    congr 1
    ring

end JointDickman

end OAI
