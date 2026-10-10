import Mathlib
import OAI.Combinatorics.UniformKServer.SideTracker

namespace OAI

                                    
section

/-! The exact side primitives have dimension-free input slopes, uniformly in
 the number of sides and their sizes. Companion §04 side-potential-bounds. -/
namespace UniformKServer.SideStability
noncomputable section
open Finset UniformKServer.SideTracker

/-- The coefficient of the parent input D, after analytic integration. -/
def dCoefficient (θ z s : ℝ) : ℝ :=
  (s-z*Real.log (1+s/z))/θ+z*Real.log (1+s/z)/2
/-- The negative coefficient of the side input B. -/
def bCoefficient (b θ z s : ℝ) : ℝ :=
  (b+θ/2)*Real.log (1+s/z)/θ

theorem coordinate_affine (b θ z C B D s : ℝ) :
    coordinate b θ z C B D s = C*(D*dCoefficient θ z s-B*bCoefficient b θ z s) := by
  unfold coordinate dCoefficient bCoefficient
  ring

theorem logarithm_bounds {z s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    0 ≤ z*Real.log (1+s/z) ∧ z*Real.log (1+s/z) ≤ s := by
  have hp : 0 < 1+s/z := by positivity
  refine ⟨mul_nonneg hz.le (Real.log_nonneg (by linarith [div_nonneg hs hz.le])), ?_⟩
  have h := Real.log_le_sub_one_of_pos hp
  have hm := mul_le_mul_of_nonneg_left h hz.le
  have he : z*(1+s/z-1)=s := by field_simp; ring
  rwa [he] at hm

theorem dCoefficient_bounds {θ z s T : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hs : 0 ≤ s) (hT : 1/θ ≤ T) :
    0 ≤ dCoefficient θ z s ∧ dCoefficient θ z s ≤ (T+1/2)*s := by
  obtain ⟨hl,hu⟩ := logarithm_bounds hz hs
  have hq : (s-z*Real.log (1+s/z))/θ ≤ s/θ := (div_le_div_iff_of_pos_right hθ).mpr (by linarith)
  unfold dCoefficient
  refine ⟨by positivity, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hT hs
  rw [mul_comm (1/θ) s, ←div_eq_mul_one_div s θ] at hm
  nlinarith

theorem bCoefficient_bounds {b θ z s J Q : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ)
    (hz : 0 < z) (hs : 0 ≤ s) (hJ : Real.log (1+s/z)/θ ≤ J)
    (hQ : b+θ/2 ≤ Q) :
    0 ≤ bCoefficient b θ z s ∧ bCoefficient b θ z s ≤ Q*J := by
  have hl : 0 ≤ Real.log (1+s/z) := nonneg_of_mul_nonneg_right (logarithm_bounds hz hs).1 hz
  unfold bCoefficient
  rw [mul_div_assoc]
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul hQ hJ (by positivity) (by linarith)

/-- A scalar slope bound; B,D may have either sign, as needed for a raw
 filtered-input difference. -/
theorem coordinate_bound {b θ z s T J Q : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ)
    (hz : 0 < z) (hs : 0 ≤ s) (hT : 1/θ ≤ T)
    (hJ : Real.log (1+s/z)/θ ≤ J) (hQ : b+θ/2 ≤ Q) (C B D : ℝ) :
    |coordinate b θ z C B D s| ≤ |C| * (|D| *(T+1/2)*s+|B| *Q*J) := by
  obtain ⟨hd,hd'⟩ := dCoefficient_bounds hθ hz hs hT
  obtain ⟨hb',hb''⟩ := bCoefficient_bounds hb hθ hz hs hJ hQ
  rw [coordinate_affine,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
  calc
    _ ≤ |D*dCoefficient θ z s|+|B*bCoefficient b θ z s| := abs_sub _ _
    _ = |D| *dCoefficient θ z s+|B| *bCoefficient b θ z s := by
      rw [abs_mul,abs_mul,abs_of_nonneg hd,abs_of_nonneg hb']
    _ ≤ |D| *((T+1/2)*s)+|B| *(Q*J) := add_le_add
      (mul_le_mul_of_nonneg_left hd' (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hb'' (abs_nonneg _))
    _ = _ := by ring

theorem coordinate_sub (b θ z C B D B' D' s : ℝ) :
    coordinate b θ z C B D s-coordinate b θ z C B' D' s =
      coordinate b θ z C (B-B') (D-D') s := by
  simp only [coordinate_affine]
  ring

variable {ι : Type*} [Fintype ι]

/-- Summing the exact coefficients costs the side-domain bound, not its
 cardinality. This applies even when the raw filtered inputs are infeasible. -/
theorem input_bound (b C D D' T J Q W : ℝ) (θ z B B' w : ι → ℝ)
    (hb : 0 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hw : domain W w) (hT : ∀ i, 1/θ i ≤ T)
    (hJ : ∀ i, Real.log (1+w i/z i)/θ i ≤ J)
    (hQ : ∀ i, b+θ i/2 ≤ Q) (hT' : 0 ≤ T+1/2) :
    |potential b C D θ z B w-potential b C D' θ z B' w| ≤
      |C| * (|D-D'| *(T+1/2)*W+Q*J*(∑ i, |B i-B' i|)) := by
  unfold potential
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ i, |coordinate b (θ i) (z i) C (B i) D (w i)-
      coordinate b (θ i) (z i) C (B' i) D' (w i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |C| * (|D-D'| *(T+1/2)*w i+|B i-B' i| *Q*J) := by
      apply sum_le_sum
      intro i _
      rw [coordinate_sub]
      exact coordinate_bound hb (hθ i) (hz i) (hw.1 i) (hT i) (hJ i) (hQ i) ..
    _ = |C| * (|D-D'| *(T+1/2)*(∑ i, w i)+Q*J*(∑ i, |B i-B' i|)) := by
      rw [←mul_sum,sum_add_distrib,←mul_sum]
      congr 2
      rw [←sum_mul,←sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left
      (mul_le_mul_of_nonneg_left hw.2 (mul_nonneg (abs_nonneg _) hT')) _) (abs_nonneg _)

end
end UniformKServer.SideStability

end

end OAI
