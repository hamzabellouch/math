import OAI.Geometry.CylinderCovering.Physical.UnitEdgeFootprintsDefinitions
import OAI.Geometry.CylinderCovering.Radial.Projection
import OAI.Geometry.CylinderCovering.Footprints.Containment
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints
open TriangularCovering

private def e : Space := !₂[1, 0, 0]
private def a : Space := !₂[0, 0, height]
private def b : Space := !₂[0, 1, 0]
private def velocity (η m : ℝ) : Space :=
  !₂[0, η * (1 / 4 + m ^ 2), 2 * height * η * m]

lemma height_pos : 0 < height := by unfold height; positivity
lemma height_sq : height ^ 2 = 1 / 2 := by norm_num [height, div_pow]

private lemma normal_unit : ‖e‖ = 1 := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
  norm_num [e, Fin.sum_univ_succ]

private lemma normal_a : inner ℝ e a = 0 := by simp [inner_coord, e, a]
private lemma normal_b : inner ℝ e b = 0 := by simp [inner_coord, e, b]
private lemma normal_velocity (η m : ℝ) : inner ℝ e (velocity η m) = 0 := by
  simp [inner_coord, e, velocity]

private lemma raw_eq (η m : ℝ) : e + velocity η m = rawDirection η m := by
  ext i
  fin_cases i <;> simp [e, velocity, rawDirection]

private lemma chart_eq (u v : ℝ) : (0 : Space) + u • a + v • b = intercept u v := by
  ext i
  fin_cases i <;> simp [a, b, intercept]
  ring

private lemma gram_factor :
    Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) = height := by
  simp only [inner_coord, a, b]
  dsimp
  ring_nf
  exact Real.sqrt_sq height_pos.le

private lemma velocity_norm_sq (η m : ℝ) :
    ‖velocity η m‖ ^ 2 = η ^ 2 * ((1 / 4 + m ^ 2) ^ 2 + 2 * m ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [velocity, Fin.sum_univ_succ]
  nlinarith only [height_sq]

private lemma triangle_eq (η d M m : ℝ) :
    triangle
      (0 + (-η * d) • a + (m * (-η * d)) • b)
      (0 + (M + η * d) • a + (m * (M + η * d) - d / 2 * ((M + η * d) - (-η * d))) • b)
      (0 + (M + η * d) • a + (m * (M + η * d) + d / 2 * ((M + η * d) - (-η * d))) • b) =
      foot η d M m := by
  rw [chart_eq, chart_eq, chart_eq]
  have hr : (M + η * d) - (-η * d) = M + 2 * η * d := by ring
  rw [hr]
  rfl

theorem local_realization : LocalRealizationStatement := by
  intro η d M m hη hd hM
  let l := -η * d
  let r := M + η * d
  have hlr : l < r := by dsimp [l, r]; nlinarith [mul_pos hη hd]
  have hκ : 0 < Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
    rw [gram_factor]; exact height_pos
  have hcross := RadialProjection.collar_projection_nondegenerate 0 e a b (velocity η m)
    l r m d normal_unit normal_a normal_b (normal_velocity η m) hd hlr hκ
  let P := (0 : Space) + l • a + (m * l) • b
  let Q := (0 : Space) + r • a + (m * r - d / 2 * (r - l)) • b
  let R := (0 : Space) + r • a + (m * r + d / 2 * (r - l)) • b
  let C := projectedCylinder (unit (e + velocity η m))
    (unit_norm (RadialProjection.sideways_ne_zero normal_unit (normal_velocity η m))) P Q R hcross
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · change unit (e + velocity η m) = axis η m
    rw [raw_eq]
    rfl
  · change projection (unit (e + velocity η m)) '' triangle P Q R = base η d M m
    rw [raw_eq]
    change projection (axis η m) '' triangle P Q R = _
    unfold P Q R l r
    rw [triangle_eq]
    rfl
  · change area (projection (unit (e + velocity η m)) '' triangle P Q R) = _
    have ha := RadialProjection.collar_projection_area 0 e a b (velocity η m)
      l r m d normal_unit normal_a normal_b (normal_velocity η m) hd.le
    rw [gram_factor, velocity_norm_sq] at ha
    rw [ha]
    unfold areaFormula l r
    congr 2
    ring
  · intro s ρ x hsm hρ0 hρM hx
    let u := ρ + 2 * η * x * (s - m)
    let v := s * ρ + η * x * (s ^ 2 - m ^ 2)
    have huv := FootprintContainment.unit_edge_triangle hη.le hd.le hx hsm hρ0 hρM
      (show u = ρ + 2 * η * x * (s - m) by rfl)
      (show v - m * u = (s - m) * ρ + η * x * (s - m) ^ 2 by dsimp [u, v]; ring)
    have hp : (0 : Space) + u • a + v • b ∈ triangle P Q R := by
      rw [← RadialProjection.coordinate_region_image 0 a b hlr hd]
      refine ⟨(u, v), ?_, rfl⟩
      exact ⟨huv.1, huv.2.1, by simpa only [l, sub_neg_eq_add, neg_mul] using huv.2.2⟩
    apply projectedCylinder_mem_direction (e + velocity η m)
      (RadialProjection.sideways_ne_zero normal_unit (normal_velocity η m)) P Q R hcross hp x
    ext i
    fin_cases i <;> simp [representedPoint, e, a, b, velocity, u, v] <;> ring

lemma mesh_eq (N : ℕ) : mesh N = 1 / (N : ℝ) := by
  norm_num [mesh, RadialRiemann.step]

lemma midpoint_mem (N : ℕ) (i : Fin N) :
    midpoint N i ∈ RadialRiemann.cell (-1 / 2) (1 / 2) N i := by
  have hd := RadialRiemann.step_pos (by norm_num : (-1 / 2 : ℝ) < 1 / 2)
    (Nat.zero_lt_of_lt i.isLt)
  have hs := RadialRiemann.point_succ (-1 / 2 : ℝ) (1 / 2) N i
  change _ ≤ _ ∧ _ ≤ _
  unfold midpoint
  constructor <;> linarith

lemma midpoint_bound {N : ℕ} {i : Fin N} {s : ℝ}
    (hs : s ∈ RadialRiemann.cell (-1 / 2) (1 / 2) N i) :
    |s - midpoint N i| ≤ mesh N / 2 := by
  have hi := RadialRiemann.point_succ (-1 / 2 : ℝ) (1 / 2) N i
  rw [abs_le]
  unfold midpoint mesh
  constructor <;> linarith [hs.1, hs.2]

theorem sourceCap_continuous (η : ℝ) : Continuous (sourceCap η) := by
  unfold sourceCap
  fun_prop

theorem sourceCap_pos (η s : ℝ) : 0 < sourceCap η s := by
  unfold sourceCap
  apply Real.sqrt_pos.mpr
  positivity

theorem family_realization : FamilyRealizationStatement := by
  intro η hη R hR hR0
  have hab : (-1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hex : ∀ N (i : Fin N), ∃ C : TriCylinder,
      C.axis = axis η (midpoint N i) ∧
      C.base = base η (mesh N) (maximumCap R N i) (midpoint N i) ∧
      area C.base = areaFormula η (mesh N) (maximumCap R N i) (midpoint N i) ∧
      ∀ s ρ x : ℝ, |s - midpoint N i| ≤ mesh N / 2 → 0 ≤ ρ →
        ρ ≤ maximumCap R N i → |x| ≤ 1 / 2 → representedPoint η s ρ x ∈ C.carrier := by
    intro N i
    exact local_realization η (mesh N) (maximumCap R N i) (midpoint N i) hη
      (RadialRiemann.step_pos hab (Nat.zero_lt_of_lt i.isLt))
      (RadialRiemann.capMax_nonneg hab hR hR0 i)
  choose C haxis hbase harea hmem using hex
  refine ⟨C, fun N i => ⟨haxis N i, hbase N i, harea N i⟩, ?_, ?_⟩
  · intro N hN z hz
    obtain ⟨s, hs, ρ, hρ, x, hx, rfl⟩ := hz
    obtain ⟨i, hi⟩ := RadialRiemann.exists_cell hN hs
    refine ⟨i, hmem N i s ρ x (midpoint_bound hi) hρ.1 ?_ hx⟩
    exact hρ.2.trans (RadialRiemann.le_capMax hab hR hi)
  · have hvel : ContinuousOn (velocity η) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) := by
      apply Continuous.continuousOn
      unfold velocity
      fun_prop
    have hlim := RadialRiemann.physical_collar_tendsto hab hR hvel (2 * η) height
      midpoint midpoint_mem
    have hsum : (fun N => totalArea (C N)) =
        (fun N => ∑ i : Fin N,
          height * RadialRiemann.step (-1 / 2) (1 / 2) N *
          (RadialRiemann.capMax R (-1 / 2) (1 / 2) N i +
            (2 * η) * RadialRiemann.step (-1 / 2) (1 / 2) N) ^ 2 /
          (2 * Real.sqrt (1 + ‖velocity η (midpoint N i)‖ ^ 2))) := by
      funext N
      unfold totalArea
      apply Finset.sum_congr rfl
      intro i _
      rw [harea N i, velocity_norm_sq]
      rfl
    rw [hsum]
    convert hlim using 1
    congr 1
    unfold limitingArea
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [velocity_norm_sq]

end CylinderCovering.UnitEdgeFootprints

end

end OAI
