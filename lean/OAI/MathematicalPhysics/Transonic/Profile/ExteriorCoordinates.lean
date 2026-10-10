import OAI.MathematicalPhysics.Transonic.Profile.PhysicalProfile

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Set

def location (r h x : ℝ) : ℝ := r*(1+h*x)
def coordinate (r h y : ℝ) : ℝ := (y/r-1)/h

lemma coordinate_location {r h : ℝ} (hr : r≠0) (hh : h≠0) (x : ℝ) :
    coordinate r h (location r h x)=x := by
  unfold coordinate location
  field_simp
  ; ring

lemma location_coordinate {r h : ℝ} (hr : r≠0) (hh : h≠0) (y : ℝ) :
    location r h (coordinate r h y)=y := by
  unfold coordinate location
  field_simp
  ; ring

lemma location_monotone {r h : ℝ} (hr : 0<r) (hh : 0<h) : StrictMono (location r h) := by
  intro a b hab
  unfold location
  apply mul_lt_mul_of_pos_left _ hr
  linarith [mul_lt_mul_of_pos_left hab hh]

lemma coordinate_mem {r h a b y : ℝ} (hr : 0<r) (hh : 0<h)
    (hy : y∈Icc (location r h a) (location r h b)) : coordinate r h y∈Icc a b := by
  have hm := (location_monotone hr hh).monotone
  have hs := location_monotone hr hh
  rw [← location_coordinate (ne_of_gt hr) (ne_of_gt hh) y] at hy
  exact ⟨hs.le_iff_le.mp hy.1,hs.le_iff_le.mp hy.2⟩

lemma coordinate_derivative (r h y : ℝ) :
    HasDerivAt (coordinate r h) ((1/r)/h) y :=
  (((hasDerivAt_id y).div_const r).sub_const 1).div_const h

lemma chart_within_derivative {s : Set ℝ} {u : ℝ → ℝ} {y m : ℝ}
    (hu : HasDerivWithinAt u m s y) (hd : 1-y*u y≠0) :
    HasDerivWithinAt (fun t => velocityToU t (u t))
      ((1-(u y)^2-(1-y^2)*m)/(1-y*u y)^2) s y := by
  change HasDerivWithinAt (fun t => (t-u t)/(1-t*u t)) _ s y
  convert ((hasDerivWithinAt_id y s).fun_sub hu).fun_div
    ((hasDerivWithinAt_const y s (1:ℝ)).fun_sub ((hasDerivWithinAt_id y s).fun_mul hu)) hd using 1 <;>
    first | rfl | (simp only [id_eq];ring)

end SepticProfile.ExteriorPolynomial

end
end

end OAI
