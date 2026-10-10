import OAI.MeasureTheory.Falconer.Geometry.DyadicGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFalconer

def quarterTurn (v : Plane) : Plane := WithLp.toLp 2 ![-v 1,v 0]
def planeDot (v w : Plane) : ℝ := v 0*w 0 + v 1*w 1
noncomputable def graphA (z : ℝ) (v : Plane) : Plane := (1/2 : ℝ) • (v-z • quarterTurn v)
noncomputable def graphB (z : ℝ) (v : Plane) : Plane := (1/2 : ℝ) • (v+z • quarterTurn v)
noncomputable def graphDerivative (s : ℝ) (v w : Plane) : Plane :=
  (1/2 : ℝ) • (-quarterTurn v + s • quarterTurn w)
noncomputable def graphDirection (z : ℝ) (ξ : Plane) : Plane :=
  (Real.sqrt (1+z^2))⁻¹ • (ξ+z • quarterTurn ξ)

theorem planeDot_abs_le (v w : Plane) : |planeDot v w| ≤ ‖v‖*‖w‖ := by
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hv hw
  have hsq : (planeDot v w)^2 ≤ ‖v‖^2*‖w‖^2 := by
    rw [hv,hw]
    unfold planeDot
    nlinarith [sq_nonneg (v 0*w 1-v 1*w 0)]
  have hp : 0 ≤ ‖v‖*‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (planeDot v w),abs_nonneg (planeDot v w)]

theorem quarterTurn_twice (v : Plane) : quarterTurn (quarterTurn v) = -v := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem norm_quarterTurn_add (z : ℝ) (v : Plane) :
    ‖quarterTurn v + z • v‖ = Real.sqrt (1+z^2) * ‖v‖ := by
  have hs : 0 ≤ 1+z^2 := by positivity
  have hsq := Real.sq_sqrt hs
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq (quarterTurn v + z • v)
  simp [Fin.sum_univ_two,quarterTurn] at hv hw
  have he : ‖quarterTurn v + z • v‖^2 = (Real.sqrt (1+z^2)*‖v‖)^2 := by
    calc
      _ = (-v 1+z*v 0)^2+(v 0+z*v 1)^2 := hw
      _ = _ := by rw [mul_pow,hsq,hv]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp he

theorem graph_transverse_identity (z s : ℝ) (ξ v w : Plane) :
    (1+z^2)*planeDot ξ (graphDerivative s v w) =
      planeDot (quarterTurn ξ-z • ξ) v +
        planeDot ξ (quarterTurn (graphA z v+s • graphB z w) +
          z • (graphA z v+s • graphB z w)) := by
  simp [planeDot,quarterTurn,graphDerivative,graphA,graphB]
  ring

theorem graph_direction_transverse (z : ℝ) (ξ v : Plane) :
    planeDot (quarterTurn (graphDirection z ξ)) v =
      (Real.sqrt (1+z^2))⁻¹ * planeDot (quarterTurn ξ-z • ξ) v := by
  simp [planeDot,quarterTurn,graphDirection]
  ring

theorem graph_product_strip (z s S : ℝ) (ξ v w : Plane)
    (hξ : ‖ξ‖ = 1) (hS : 0 ≤ S)
    (hchart : Real.sqrt (1+z^2) ≤ 4)
    (hedge : ‖graphA z v+s • graphB z w‖ ≤ S)
    (hderiv : |planeDot ξ (graphDerivative s v w)| ≤ S) :
    |planeDot (quarterTurn (graphDirection z ξ)) v| ≤ 5*S := by
  let t := Real.sqrt (1+z^2)
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t^2 = 1+z^2 := Real.sq_sqrt (by positivity)
  let e := graphA z v+s • graphB z w
  have herr : |planeDot ξ (quarterTurn e+z • e)| ≤ t*S := by
    calc
      _ ≤ ‖ξ‖*‖quarterTurn e+z • e‖ := planeDot_abs_le _ _
      _ = t*‖e‖ := by rw [hξ,one_mul,norm_quarterTurn_add]
      _ ≤ t*S := mul_le_mul_of_nonneg_left hedge ht.le
  have hid := graph_transverse_identity z s ξ v w
  have htrans : |planeDot (quarterTurn ξ-z • ξ) v| ≤ (t^2+t)*S := by
    have he : planeDot (quarterTurn ξ-z • ξ) v =
        (1+z^2)*planeDot ξ (graphDerivative s v w) -
          planeDot ξ (quarterTurn e+z • e) := by dsimp [e]; linarith [hid]
    rw [he]
    calc
      _ ≤ |(1+z^2)*planeDot ξ (graphDerivative s v w)| +
          |planeDot ξ (quarterTurn e+z • e)| := abs_sub _ _
      _ ≤ (t^2)*S+t*S := by
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+z^2),← ht2]
        exact add_le_add (mul_le_mul_of_nonneg_left hderiv (sq_nonneg _)) herr
      _ = _ := by ring
  rw [graph_direction_transverse,abs_mul,abs_of_pos (inv_pos.mpr ht)]
  change t⁻¹ * |planeDot (quarterTurn ξ-z • ξ) v| ≤ 5*S
  have hmul := mul_le_mul_of_nonneg_left htrans (inv_nonneg.mpr ht.le)
  have he : t⁻¹*((t^2+t)*S) = (t+1)*S := by field_simp
  rw [he] at hmul
  exact hmul.trans (by dsimp [t] at *; nlinarith)

end PlanarFalconer

end OAI
