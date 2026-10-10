import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
namespace CylinderCovering.SingularOverlap
open RuledApproximation

lemma overlap_remainder_of_bounds {p K c x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hcK : c*K ≤ 1/2)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    |rm+rp-1-c^2*(x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2))| ≤
      14*K^2*c^3 := by
  have hKn : 0 ≤ K := by linarith
  have hxs : |x^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hys : |y^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg y)]; nlinarith only [(abs_le.mp hy).1,(abs_le.mp hy).2]
  have hbm' : |bm-y| ≤ c*K := by
    rw [hbm,sub_sub_cancel_left,abs_neg,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hx hPm) hc
  have hbp' : |bp-x| ≤ c*K := by
    rw [hbp,add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hy hPp) hc
  let D := rm+rp-1
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hEd : |y*(Qp-bp)-x*(Qm-bm)| ≤ K*D := by
    calc
      _ ≤ |y*(Qp-bp)|+|x*(Qm-bm)| := abs_sub _ _
      _ ≤ K*(rp-1/2)+K*(rm-1/2) := add_le_add (abs_unit_mul_le hy hQp) (abs_unit_mul_le hx hQm)
      _ = _ := by dsimp [D]; ring
  have hPe : |y^2*Pp+x^2*Pm| ≤ 2*K := by
    calc
      _ ≤ |y^2*Pp|+|x^2*Pm| := abs_add_le _ _
      _ ≤ K+K := add_le_add (abs_unit_mul_le hys hPp) (abs_unit_mul_le hxs hPm)
      _ = _ := by ring
  have hDeq : D=c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := by
    dsimp [D]
    rw [hsum,hbm,hbp]
    ring
  have hDb : D ≤ 4*K*c^2 := by
    have hu : D ≤ c^2*(2*K)+c*(K*D) := by
      calc
        D = c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := hDeq
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hPe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hEd) hc)
    have hmul := mul_le_mul_of_nonneg_right hcK hD
    nlinarith only [hmul,hu]
  have hrmb : rm-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hrpb : rp-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hc2 : c^2 ≤ c := by nlinarith only [hc,hc1]
  have hPmy' : |Pm-(p/4+(2-p)*y^2)| ≤ 5*K^2*c := by
    apply hPmy.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbm' hrmb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  have hPpx' : |Pp-(p/4+(2-p)*x^2)| ≤ 5*K^2*c := by
    apply hPpx.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbp' hrpb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  let A := x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2)
  have hAe : |y^2*Pp+x^2*Pm-A| ≤ 10*K^2*c := by
    calc
      _ = |y^2*(Pp-(p/4+(2-p)*x^2))+x^2*(Pm-(p/4+(2-p)*y^2))| := by dsimp [A]; congr 1; ring
      _ ≤ |y^2*(Pp-(p/4+(2-p)*x^2))|+|x^2*(Pm-(p/4+(2-p)*y^2))| := abs_add_le _ _
      _ ≤ 5*K^2*c+5*K^2*c := add_le_add (abs_unit_mul_le hys hPpx') (abs_unit_mul_le hxs hPmy')
      _ = _ := by ring
  change |D-c^2*A| ≤ 14*K^2*c^3
  calc
    _ = |c^2*(y^2*Pp+x^2*Pm-A)+c*(y*(Qp-bp)-x*(Qm-bm))| := by
      rw [hDeq]
      congr 1
      ring
    _ ≤ |c^2*(y^2*Pp+x^2*Pm-A)|+|c*(y*(Qp-bp)-x*(Qm-bm))| :=
      abs_add_le _ _
    _ = c^2*|y^2*Pp+x^2*Pm-A|+c*|y*(Qp-bp)-x*(Qm-bm)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg hc]
    _ ≤ c^2*(10*K^2*c)+c*(K*D) := add_le_add
      (mul_le_mul_of_nonneg_left hAe (sq_nonneg c))
      (mul_le_mul_of_nonneg_left hEd hc)
    _ ≤ c^2*(10*K^2*c)+c*(K*(4*K*c^2)) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDb hKn) hc)
    _ = 14*K^2*c^3 := by ring

theorem actual_overlap_remainder (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (c x y : ℝ) (zm zp : Plane),
      0 ≤ c → c ≤ 1 → c*K ≤ 1/2 → |x| ≤ 1 → |y| ≤ 1 →
      1/2 ≤ zm 1 → zm 1 ≤ 2 → 1/2 ≤ zp 1 → zp 1 ≤ 2 →
      |zm 0| ≤ zm 1 → |zp 0| ≤ zp 1 →
      zm 0=y-c*x*singularField p zm 0 → zp 0=x+c*y*singularField p zp 0 →
      zm 1+zp 1=1+c*(y*singularField p zp 1-x*singularField p zm 1) →
      |zm 1+zp 1-1-c^2*(x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2))| ≤
        14*K^2*c^3 := by
  obtain ⟨K,hK,he⟩ := singular_region_estimates p
  refine ⟨K,hK,?_⟩
  intro c x y zm zp hc hc1 hcK hx hy hrm hzm hrp hzp hbzm hbzp hezm hezp hesum
  obtain ⟨hPm,hQm,hPmy,_⟩ := he zm y (hbzm.trans hzm) hrm hzm
    (hy.trans (by norm_num))
  obtain ⟨hPp,hQp,hPpx,_⟩ := he zp x (hbzp.trans hzp) hrp hzp
    (hx.trans (by norm_num))
  exact overlap_remainder_of_bounds hK hc hc1 hcK hx hy hrm hrp
    hPm hPp hQm hQp hPmy hPpx hezm hezp hesum

end CylinderCovering.SingularOverlap

end

end OAI
