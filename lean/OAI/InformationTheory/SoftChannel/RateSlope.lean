import OAI.InformationTheory.SoftChannel.HighReserve

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanBlast.CourtadeKumar

def slopeT (z : ℝ) : ℝ := 1+z/3+z^2/5
def slopePolynomial (z : ℝ) : ℝ :=
  2*(1-z)^2*slopeT z^2*((1-z)*slopeT z+1)-curvatureN z
def RateSlope_slopeBernstein : Fin 10 → ℝ :=
  ![(8/3:ℝ),
    (512/225:ℝ),
    (334/175:ℝ),
    (5861/3750:ℝ),
    (93828088/75796875:ℝ),
    (102326753/109484375:ℝ),
    (8980934524/13685546875:ℝ),
    (71721266999/175957031250:ℝ),
    (9531748404/48876953125:ℝ),
    (18341751592/733154296875:ℝ)]

lemma RateSlope_slopeBernstein_pos (i : Fin 10) : 0 < RateSlope_slopeBernstein i := by
  fin_cases i <;> norm_num [RateSlope_slopeBernstein]

lemma slopePolynomial_bernstein (t : ℝ) :
    slopePolynomial ((3/5)*t) = bernsteinSum 9 RateSlope_slopeBernstein t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [slopePolynomial,slopeT,curvatureN,RateSlope_slopeBernstein,Fin.sum_univ_succ,
    Nat.descFactorial,Nat.factorial]
  ring

lemma slopePolynomial_pos {z : ℝ} (hz : z ∈ Icc 0 (3/5:ℝ)) : 0 < slopePolynomial z := by
  have h := bernsteinSum_pos 9 RateSlope_slopeBernstein RateSlope_slopeBernstein_pos (by linarith [hz.1] : 0 ≤ (5/3:ℝ)*z)
    (by linarith [hz.2] : (5/3:ℝ)*z ≤ 1)
  rw [← slopePolynomial_bernstein] at h
  convert! h using 1; congr 1; ring

lemma slopeT_lower {u : ℝ} (hu : u ∈ Ioo 0 1) : u*slopeT (u^2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu.1.le hu.2 3
  norm_num [Finset.sum_range_succ] at h
  convert! h using 1; unfold slopeT; ring

lemma r_slope_bound_psi {u : ℝ} (hu : u ∈ Ioo 0 1) (hu2 : u^2 ≤ (3/5:ℝ)) :
    rSecondDeriv (psi u) < 2*rDeriv (psi u) := by
  have ha : 0 < 1-u^2 := by linarith
  have hv := Real.artanh_pos hu
  have ht : 0 < slopeT (u^2) := by unfold slopeT; positivity
  have hT := slopeT_lower hu
  have hN := curvatureNumerator_upper hu.1 hu.2
  have hP := slopePolynomial_pos ⟨sq_nonneg u,hu2⟩
  unfold slopePolynomial at hP
  have hn := (div_le_iff₀ (pow_pos hu.1 3)).mp hN
  have hn' := (mul_le_mul_of_nonneg_right hn ha.le)
  have hcancel : (curvatureN (u^2)/(1-u^2)*u^3)*(1-u^2) = curvatureN (u^2)*u^3 := by field_simp
  rw [hcancel] at hn'
  have hc := mul_pos hP (pow_pos hu.1 3)
  have hp2 := pow_le_pow_left₀ (mul_pos hu.1 ht).le hT 2
  have hp3 := pow_le_pow_left₀ (mul_pos hu.1 ht).le hT 3
  have hm2 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 2*(1-u^2)^2*u by exact mul_nonneg (by positivity) hu.1.le)
  have hm3 := mul_le_mul_of_nonneg_left hp3 (show 0 ≤ 2*(1-u^2)^3 by positivity)
  rw [rSecondDeriv_psi hu,rDeriv_psi hu]
  apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos ha) (pow_pos hv 3))).mpr
  have hden : (1+u/((1-u^2)*Real.artanh u))*((1-u^2)^2*Real.artanh u^3) =
    (1-u^2)^2*Real.artanh u^3+u*(1-u^2)*Real.artanh u^2 := by field_simp
  rw [mul_assoc,hden]
  have hcore : ((1+u^2)*Real.artanh u-u)*(1-u^2) <
      (2*((1-u^2)^2*Real.artanh u^3+u*(1-u^2)*Real.artanh u^2))*(1-u^2) := by
    nlinarith
  exact (mul_lt_mul_iff_left₀ ha).mp (by simpa only [mul_comm (1-u^2)] using hcore)

lemma r_slope_bound {I : ℝ} (hI : I ∈ Icc 0 softCutoff) : rSecondDeriv I < 2*rDeriv I := by
  rcases hI.1.eq_or_lt with rfl | hI0
  · norm_num
  have hIL := hI.2.trans_lt softCutoff_lt_ell
  have hu := psiInv_mem_Ioo ⟨hI0,hIL⟩
  have hule : psiInv I ≤ (77/100:ℝ) := by
    apply (strictMonoOn_psi.le_iff_le ⟨hu.1.le,hu.2.le⟩ (by norm_num)).mp
    rw [psi_psiInv hI0.le hIL]; exact hI.2
  have h := r_slope_bound_psi hu (by nlinarith [hu.1])
  rwa [psi_psiInv hI0.le hIL] at h

end LeanBlast.CourtadeKumar
end
end

end OAI
