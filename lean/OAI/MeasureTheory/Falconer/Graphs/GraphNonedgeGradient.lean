import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgePerturbation
import OAI.MeasureTheory.Falconer.Graphs.GraphAmplitudeScale

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_four_endpoint_errors (P : Fin 4 → DyadicSquare) (x : Fin 4 → Plane)
    {δ : ℝ} (hP : ∀ a, 0 < (P a).side) (hδ : ∀ a, (P a).side ≤ δ)
    (hx : ∀ a, x a ∈ (P a).carrier) (a b : Fin 4) :
    ‖(x a-x b)-((P a).center-(P b).center)‖ ≤ 4*δ := by
  have ha := (P a).dist_le (hP a).le (hx a) ((P a).center_mem (hP a))
  have hb := (P b).dist_le (hP b).le (hx b) ((P b).center_mem (hP b))
  have he := dist_sub_sub_le (x a) (x b) (P a).center (P b).center
  rw [dist_eq_norm] at he
  exact he.trans (by linarith [hδ a,hδ b])

theorem graph_eta_phase_hasFDerivAt (R s z : ℝ) (v w η : Plane) :
    HasFDerivAt (fun e : Plane => R*inner ℝ e (graphA z v+s • graphB z w))
      (R • innerSL ℝ (graphA z v+s • graphB z w)) η := by
  convert (R • innerSL ℝ (graphA z v+s • graphB z w)).hasFDerivAt (x := η) using 1
  ext e
  simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,real_inner_comm]

theorem graph_z_phase_hasDerivAt (R s z : ℝ) (v w η : Plane) :
    HasDerivAt (fun t : ℝ => R*inner ℝ η (graphA t v+s • graphB t w))
      (R*inner ℝ η (graphDerivative s v w)) z := by
  have he : (fun t : ℝ => R*inner ℝ η (graphA t v+s • graphB t w)) =
      fun t => R*inner ℝ η ((1/2:ℝ) • (v+s • w)) + t*(R*inner ℝ η (graphDerivative s v w)) := by
    funext t
    simp only [graph_phase_affine,inner_add_right,real_inner_smul_right]
    ring
  rw [he]
  convert! (hasDerivAt_const z (R*inner ℝ η ((1/2:ℝ) • (v+s • w)))).add
      ((hasDerivAt_id z).mul_const (R*inner ℝ η (graphDerivative s v w))) using 1
  simp

theorem graph_vector_nonedge_lower (R s z z₀ : ℝ) (v w v₀ w₀ : Plane)
    {S ε : ℝ} (hR : 0 ≤ R)
    (herr : ‖(graphA z v+s • graphB z w)-(graphA z₀ v₀+s • graphB z₀ w₀)‖ ≤ ε)
    (hsmall : ε ≤ S/2) (hfail : S < ‖graphA z₀ v₀+s • graphB z₀ w₀‖) :
    R*S/2 ≤ ‖R • innerSL ℝ (graphA z v+s • graphB z w)‖ := by
  have htri := norm_le_norm_add_norm_sub (graphA z v+s • graphB z w) (graphA z₀ v₀+s • graphB z₀ w₀)
  have hlo : S/2 ≤ ‖graphA z v+s • graphB z w‖ := by linarith
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hR,innerSL_apply_norm]
  nlinarith

theorem graph_scalar_nonedge_lower (R s : ℝ) (v w v₀ w₀ e e₀ : Plane)
    {S ε r : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hr : 1/8 ≤ r)
    (herr : |inner ℝ e (graphDerivative s v w)-inner ℝ e₀ (graphDerivative s v₀ w₀)| ≤ ε)
    (hsmall : ε ≤ S/2) (hfail : S < |inner ℝ e₀ (graphDerivative s v₀ w₀)|) :
    R*S/16 ≤ |R*inner ℝ (r • e) (graphDerivative s v w)| := by
  have htri := abs_sub_abs_le_abs_sub (inner ℝ e₀ (graphDerivative s v₀ w₀))
    (inner ℝ e (graphDerivative s v w))
  rw [abs_sub_comm] at htri
  have hlo : S/2 ≤ |inner ℝ e (graphDerivative s v w)| := by linarith
  have hprod := mul_le_mul hr hlo (by positivity : (0:ℝ)≤S/2) (by linarith : 0 ≤ r)
  rw [real_inner_smul_left,abs_mul,abs_mul,abs_of_nonneg hR,abs_of_nonneg (by linarith : 0 ≤ r)]
  nlinarith

end PlanarFalconer

end OAI
