import OAI.Probability.GammaPassage.PathChain
import Mathlib.Analysis.Convex.Segment

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

noncomputable def segmentPoint (p q : Vertex) (t : ℝ) : Plane :=
  latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)

noncomputable def waypoint (p q : Vertex) (B j : ℕ) : Vertex :=
  latticeFloor (segmentPoint p q ((j : ℝ)/B))

def SegmentTube (p q : Vertex) (R : ℝ) : Set Vertex :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖latticeEmbed z-segmentPoint p q t‖ ≤ R}

@[simp] theorem waypoint_zero (p q : Vertex) (B : ℕ) : waypoint p q B 0=p := by
  simp [waypoint,segmentPoint]

theorem waypoint_end (p q : Vertex) (B : ℕ) (hB : 0 < B) : waypoint p q B B=q := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  simp [waypoint,segmentPoint,hb]

theorem waypoint_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)‖ ≤ 2 :=
  latticeFloor_error _

theorem waypoint_displacement_error (p q : Vertex) (B j : ℕ) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p)‖ ≤ 4 := by
  have he : latticeEmbed (waypoint p q B (j+1)-waypoint p q B j) -
      (1/(B : ℝ)) • latticeEmbed (q-p) =
      (latticeEmbed (waypoint p q B (j+1))-segmentPoint p q (((j+1 : ℕ) : ℝ)/B)) -
      (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B)) := by
    rw [latticeEmbed_sub,latticeEmbed_sub]
    unfold segmentPoint
    ext i
    simp [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [waypoint_error p q B (j+1),waypoint_error p q B j])

theorem waypoint_displacement_norm (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    ‖latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)‖ ≤
      ‖latticeEmbed (q-p)‖/(B : ℝ)+4 := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := norm_add_le
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)-(1/(B : ℝ)) • latticeEmbed (q-p))
    ((1/(B : ℝ)) • latticeEmbed (q-p))
  rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hb)] at hn
  have he := waypoint_displacement_error p q B j
  have hid : (1/(B : ℝ))*‖latticeEmbed (q-p)‖=‖latticeEmbed (q-p)‖/(B : ℝ) := by ring
  rw [hid] at hn
  linarith

theorem waypoint_cost_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (β : ℝ) (hβ : 0 ≤ β) (hlip : ∀ v w, |μ v-μ w| ≤ β*‖v-w‖)
    (p q : Vertex) (B j : ℕ) (hB : 0 < B) :
    μ (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j)) ≤
      μ (latticeEmbed (q-p))/(B : ℝ)+4*β := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have ht := (le_abs_self _).trans (hlip
    (latticeEmbed (waypoint p q B (j+1)-waypoint p q B j))
    ((1/(B : ℝ)) • latticeEmbed (q-p)))
  have he := mul_le_mul_of_nonneg_left (waypoint_displacement_error p q B j) hβ
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hb)] at ht
  have hid : (1/(B : ℝ))*μ (latticeEmbed (q-p))=μ (latticeEmbed (q-p))/(B : ℝ) := by ring
  rw [hid] at ht
  linarith

theorem waypoint_ball_in_tube (p q : Vertex) (B j : ℕ) (hB : 0 < B) (hj : j ≤ B)
    (R : ℝ) (z : Vertex) (hz : ‖latticeEmbed (z-waypoint p q B j)‖ ≤ R) :
    z ∈ SegmentTube p q (R+2) := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  refine ⟨(j : ℝ)/B,div_nonneg (Nat.cast_nonneg _) hb.le,?_,?_⟩
  · exact (div_le_one hb).mpr (by exact_mod_cast hj)
  have he := waypoint_error p q B j
  have ht := norm_add_le (latticeEmbed z-latticeEmbed (waypoint p q B j))
    (latticeEmbed (waypoint p q B j)-segmentPoint p q ((j : ℝ)/B))
  rw [sub_add_sub_cancel] at ht
  rw [latticeEmbed_sub] at hz
  linarith

/-- Exact connection between the tube predicate and the closed Euclidean
segment used in cr:local-travel. -/
theorem mem_segmentTube_iff (p q z : Vertex) (R : ℝ) :
    z ∈ SegmentTube p q R ↔ ∃ v ∈ segment ℝ (latticeEmbed p) (latticeEmbed q),
      ‖latticeEmbed z-v‖ ≤ R := by
  constructor
  · rintro ⟨t,ht0,ht1,hbound⟩
    refine ⟨segmentPoint p q t,?_,hbound⟩
    rw [segment_eq_image']
    exact ⟨t,⟨ht0,ht1⟩,rfl⟩
  · rintro ⟨v,hv,hbound⟩
    rw [segment_eq_image'] at hv
    obtain ⟨t,ht,rfl⟩ := hv
    exact ⟨t,ht.1,ht.2,hbound⟩

end GammaFPP.IntervalTravelBridge

end OAI
