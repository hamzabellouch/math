import OAI.Geometry.SurfaceImmersion.Atlas.ThinPairCoordinates

namespace OAI

/-! The signed canonical normal fields and their scaled frame fillings. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def centeredOppositeNormal (c h s : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2,s*x 0]

def centeredEqualNormal (c h k s : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2-(h*k*x 0)^2,s*((x 1-c)/h)*x 0]

def centeredEqualHomotopy (c h k s v : ℝ) (x : Base) : Base :=
  ![(x 1-c)^2-h^2-v*(h*k*x 0)^2,s*((x 1-c)/h)*x 0]

lemma centeredEqualHomotopy_smooth (c h k s : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Base => centeredEqualHomotopy c h k s z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [centeredEqualHomotopy] <;> fun_prop

lemma centeredEqualHomotopy_zero_iff {c h k s v : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    (hv : 0 ≤ v) (x : Base) :
    centeredEqualHomotopy c h k s v x = 0 ↔
      x = crosscapAxis (c-h) ∨ x = crosscapAxis (c+h) := by
  constructor
  · intro he
    have h0 : (x 1-c)^2-h^2-v*(h*k*x 0)^2 = 0 := congrFun he 0
    have h1 : s*((x 1-c)/h)*x 0 = 0 := congrFun he 1
    have hx0 : x 0 = 0 := by
      by_contra hn
      have hc : x 1 = c := by
        have hc' := (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hn)).resolve_left hs
        exact sub_eq_zero.mp ((div_eq_zero_iff).mp hc' |>.resolve_right hh.ne')
      rw [hc] at h0
      have := mul_nonneg hv (sq_nonneg (h*k*x 0))
      nlinarith [sq_pos_of_pos hh]
    rw [hx0] at h0
    have hf : (x 1-(c-h))*(x 1-(c+h)) = 0 := by nlinarith [h0]
    rcases mul_eq_zero.mp hf with hl | hr
    · left
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hx0,sub_eq_zero.mp hl]
    · right
      ext i
      fin_cases i <;> simp [crosscapAxis_apply,hx0,sub_eq_zero.mp hr]
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;>
      simp [centeredEqualHomotopy,crosscapAxis_apply]

lemma centeredOppositeNormal_scaled (c h k s : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (x : Base) :
    (normalPairScale (h^2) (s/k)).comp (oppositeIndexFrame (pairCoordinateMap c h k x)) =
      defectFrame (centeredOppositeNormal c h s) x := by
  rw [oppositeIndexFrame,normalPairScale_axis]
  congr 1 <;> dsimp [pairCoordinateMap,defectFrame,centeredOppositeNormal]
  · field_simp
  · field_simp

lemma centeredEqualNormal_scaled (c h k s : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (x : Base) :
    (normalPairScale (h^2) (s/(2*k))).comp (equalIndexFrame (pairCoordinateMap c h k x)) =
      defectFrame (centeredEqualNormal c h k s) x := by
  rw [equalIndexFrame,normalPairScale_axis]
  congr 1 <;> dsimp [pairCoordinateMap,defectFrame,centeredEqualNormal]
  · field_simp
    ring
  · field_simp

theorem centeredOppositeNormal_filling {c h s : ℝ} (hh : 0 < h) (hs : s ≠ 0)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U) :
    HasRelativeDefectFilling (centeredOppositeNormal c h s) U := by
  obtain ⟨R,k,hR,hk,hbox⟩ := thin_pair_coordinates hh hU haxis
  obtain ⟨B,K,hB,hBI,hK,hKR,hBe⟩ := compact_opposite_index_frame_filling_radius hR
  obtain ⟨A,hA,hAI,hK',hAe⟩ := pullback_model_filling hB hBI hK hBe c h k (h^2) (s/k)
    hh.ne' hk.ne' (pow_ne_zero _ hh.ne') (div_ne_zero hs hk.ne')
  refine ⟨A,(pairCoordinates c h k hh.ne' hk.ne') ⁻¹' K,hA,hK',?_,fun x _ => hAI x,?_⟩
  · intro x hx
    exact hbox (hKR hx)
  · intro x hx
    rw [hAe x hx]
    exact centeredOppositeNormal_scaled c h k s hh.ne' hk.ne' x

theorem centeredEqualNormal_filling {c h k s R : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hs : s ≠ 0) (hR : 1 < R) {U : Set Base}
    (hbox : (pairCoordinateMap c h k) ⁻¹' ball (0:Base) R ⊆ U) :
    HasRelativeDefectFilling (centeredEqualNormal c h k s) U := by
  obtain ⟨B,K,hB,hBI,hK,hKR,hBe⟩ := compact_equal_index_frame_filling_radius hR
  obtain ⟨A,hA,hAI,hK',hAe⟩ := pullback_model_filling hB hBI hK hBe c h k (h^2) (s/(2*k))
    hh.ne' hk.ne' (pow_ne_zero _ hh.ne') (div_ne_zero hs (mul_ne_zero (by norm_num) hk.ne'))
  refine ⟨A,(pairCoordinates c h k hh.ne' hk.ne') ⁻¹' K,hA,hK',?_,fun x _ => hAI x,?_⟩
  · intro x hx
    exact hbox (hKR hx)
  · intro x hx
    rw [hAe x hx]
    exact centeredEqualNormal_scaled c h k s hh.ne' hk.ne' x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
