import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
namespace SepticProfile.FixedInterval

def inv (Q : ℤ) (a : Box) : Box :=
  let l := Q*Q/(a.center+a.radius)
  let u := Q*Q/(a.center-a.radius)+1
  ⟨(l+u)/2,(u-l)/2+2⟩

lemma holds_inv {Q : ℤ} (hQ : 0<Q) {a : Box} {x : ℝ}
    (hx : Holds Q a x) (ha : 0<a.center-a.radius) :
    Holds Q (inv Q a) (1/x) := by
  have hrad := radius_nonneg hx
  have hu : 0<a.center+a.radius := by omega
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  have hlo : (0:ℝ)<(a.center:ℝ)-a.radius := by exact_mod_cast ha
  have hhi : (0:ℝ)<(a.center:ℝ)+a.radius := by exact_mod_cast hu
  have hb := abs_le.mp hx
  have hxpos : 0<x := by nlinarith [hb.1]
  let l : ℤ := Q*Q/(a.center+a.radius)
  let u : ℤ := Q*Q/(a.center-a.radius)+1
  have h1 : (l:ℝ)*((a.center:ℝ)+a.radius) ≤ (Q:ℝ)^2 := by
    have := (quotient_bounds (Q*Q) (a.center+a.radius) hu).1
    simpa only [l,pow_two,Int.cast_mul,Int.cast_add] using (show ((Q*Q/(a.center+a.radius):ℤ):ℝ)*((a.center:ℝ)+a.radius)≤(Q:ℝ)*(Q:ℝ) by exact_mod_cast this)
  have h2 : (Q:ℝ)^2 < (u:ℝ)*((a.center:ℝ)-a.radius) := by
    have := (quotient_bounds (Q*Q) (a.center-a.radius) ha).2
    simpa only [u,pow_two,Int.cast_mul,Int.cast_add,Int.cast_one] using (show (Q:ℝ)*(Q:ℝ)<((Q*Q/(a.center-a.radius)+1:ℤ):ℝ)*((a.center:ℝ)-a.radius) by exact_mod_cast this)
  have hl0 : 0≤l := Int.ediv_nonneg (by positivity) (le_of_lt hu)
  have hu0 : 0≤u := by dsimp [u];have := Int.ediv_nonneg (show 0≤Q*Q by positivity) (le_of_lt ha);omega
  have hl0' : (0:ℝ)≤l := by exact_mod_cast hl0
  have hu0' : (0:ℝ)≤u := by exact_mod_cast hu0
  have h1' : (l:ℝ)≤(Q:ℝ)/x := by
    rw [le_div_iff₀ hxpos]
    have := mul_le_mul_of_nonneg_left (show (Q:ℝ)*x≤(a.center:ℝ)+a.radius by linarith [hb.2]) hl0'
    nlinarith
  have h2' : (Q:ℝ)/x<(u:ℝ) := by
    rw [div_lt_iff₀ hxpos]
    have := mul_le_mul_of_nonneg_left (show (a.center:ℝ)-a.radius≤(Q:ℝ)*x by linarith [hb.1]) hu0'
    nlinarith
  have huv : l≤u := by exact_mod_cast (show (l:ℝ)≤u from h1'.trans h2'.le)
  have hcl := quotient_bounds (l+u) 2 (by norm_num)
  have hrd := quotient_bounds (u-l) 2 (by norm_num)
  have hcl1 : (((l+u)/2:ℤ):ℝ)*2≤(l:ℝ)+u := by exact_mod_cast hcl.1
  have hcl2 : (l:ℝ)+u<((((l+u)/2:ℤ):ℝ)+1)*2 := by exact_mod_cast hcl.2
  have hrd1 : (((u-l)/2:ℤ):ℝ)*2≤(u:ℝ)-l := by exact_mod_cast hrd.1
  have hrd2 : (u:ℝ)-l<((((u-l)/2:ℤ):ℝ)+1)*2 := by exact_mod_cast hrd.2
  change |(Q:ℝ)*(1/x)-(((l+u)/2:ℤ):ℝ)| ≤ (((u-l)/2+2:ℤ):ℝ)
  push_cast
  rw [mul_one_div,abs_le]
  constructor <;> linarith

lemma holds_div {Q : ℤ} (hQ : 0<Q) {a b : Box} {x y : ℝ}
    (hx : Holds Q a x) (hy : Holds Q b y) (hb : 0<b.center-b.radius) :
    Holds Q (mul Q a (inv Q b)) (x/y) := by
  simpa [div_eq_mul_inv] using holds_mul hQ hx (holds_inv hQ hy hb)

end SepticProfile.FixedInterval


end

end OAI
