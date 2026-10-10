import OAI.Combinatorics.Crossing.VertexSpokeBounds
import Mathlib.Analysis.Real.Sqrt

namespace OAI

noncomputable section
namespace Zarankiewicz

def radialPort (a b : Plane) (r : ℝ) : Plane :=
  a+(r/Real.sqrt (squaredLength (b-a))) • (b-a)

theorem squaredLength_smul (v : Plane) (t : ℝ) : squaredLength (t • v)=t^2*squaredLength v := by
  dsimp [squaredLength]
  ring

theorem radialPort_sub (a b : Plane) (r : ℝ) :
    radialPort a b r-a=(r/Real.sqrt (squaredLength (b-a))) • (b-a) := by
  simp only [radialPort,add_sub_cancel_left]

theorem radialPort_on_circle (a b : Plane) (hab : a ≠ b) (r : ℝ) :
    squaredLength (radialPort a b r-a)=r^2 := by
  have hL := squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm)
  have hs : Real.sqrt (squaredLength (b-a)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  rw [radialPort_sub,squaredLength_smul,div_pow,Real.sq_sqrt hL.le]
  exact div_mul_cancel₀ _ (ne_of_gt hL)

theorem radialPort_parameter (a b : Plane) (r : ℝ) :
    radialPort a b r=segmentPoint a b (r/Real.sqrt (squaredLength (b-a))) := by
  apply Prod.ext <;> dsimp [radialPort,segmentPoint] <;> ring

theorem radialPort_parameter_between (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (b-a)) :
    r/Real.sqrt (squaredLength (b-a)) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hL : 0 < squaredLength (b-a) := (sq_nonneg r).trans_lt hshort
  have hs := Real.sqrt_pos.mpr hL
  have hs2 := Real.sq_sqrt hL.le
  exact ⟨div_pos hr hs,(div_lt_one hs).mpr (by nlinarith)⟩

theorem radialPort_mem_openSegment (a b : Plane) (r : ℝ) (hr : 0 < r)
    (hshort : r^2 < squaredLength (b-a)) : radialPort a b r ∈ openSegmentTrace a b := by
  exact ⟨r/Real.sqrt (squaredLength (b-a)),radialPort_parameter_between a b r hr hshort,
    (radialPort_parameter a b r).symm⟩

theorem radialPort_ne_center (a b : Plane) (hab : a ≠ b) (r : ℝ) (hr : 0 < r) :
    radialPort a b r ≠ a := by
  intro h
  have hh := radialPort_on_circle a b hab r
  rw [h,sub_self] at hh
  have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
  rw [hz] at hh
  nlinarith

end Zarankiewicz

end

end OAI
