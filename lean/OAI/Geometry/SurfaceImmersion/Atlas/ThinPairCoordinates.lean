import OAI.Geometry.SurfaceImmersion.Correction.PairModelCoordinates

namespace OAI

/-! Model fillings can be made arbitrarily thin around the connecting interval. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma thin_pair_coordinates {c h : ℝ} (hh : 0 < h) {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U) :
    ∃ R k : ℝ, 1 < R ∧ 0 < k ∧
      (pairCoordinateMap c h k) ⁻¹' ball (0:Base) R ⊆ U := by
  obtain ⟨r,hr,hrect⟩ := compact_axis_rectangle (show c-h ≤ c+h by linarith) hU
    (by simpa only [crosscapAxis_apply] using haxis)
  let R := 1+r/(2*h)
  let k := 2*R/r
  have hR : 1 < R := by
    have hp : 0 < r/(2*h) := div_pos hr (mul_pos (by norm_num) hh)
    dsimp [R]
    linarith
  have hk : 0 < k := by dsimp [k]; positivity
  have hRh : R*h = h+r/2 := by dsimp [R]; field_simp
  have hkhalf : k*(r/2) = R := by dsimp [k]; field_simp
  refine ⟨R,k,hR,hk,?_⟩
  intro x hx
  have hn : ‖pairCoordinateMap c h k x‖ < R := by simpa only [mem_preimage,mem_ball,dist_zero_right] using hx
  have hu : |(x 1-c)/h| < R := by
    exact (norm_le_pi_norm (pairCoordinateMap c h k x) 0).trans_lt hn
  have hv : |k*x 0| < R := by
    exact (norm_le_pi_norm (pairCoordinateMap c h k x) 1).trans_lt hn
  have hxt : -r ≤ x 0 ∧ x 0 ≤ r := by
    rw [abs_lt] at hv
    constructor <;> nlinarith
  have htt : c-h-r ≤ x 1 ∧ x 1 ≤ c+h+r := by
    rw [abs_lt] at hu
    have hl : -R*h < x 1-c := (lt_div_iff₀ hh).mp hu.1
    have hu' : x 1-c < R*h := (div_lt_iff₀ hh).mp hu.2
    constructor <;> linarith
  have he : (![x 0,x 1] : Base) = x := by ext i; fin_cases i <;> rfl
  rw [←he]
  exact hrect (x 0) hxt (x 1) htt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
