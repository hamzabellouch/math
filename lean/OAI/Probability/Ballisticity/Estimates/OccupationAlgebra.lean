import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma occupation_scale_factor {nᵤ nᵣ D u r a : ℝ} (hu : 0 < u) (hr : 0 < r)
    (hD : 0 ≤ D) (hn : 0 ≤ nᵣ) (hua : u ≤ a*r)
    (hcomp : nᵤ ≤ D*nᵣ*(u/r)^((7:ℝ)/4)) :
    nᵤ ≤ (D*nᵣ/r^((3:ℝ)/2))*a^((1:ℝ)/4)*u^((3:ℝ)/2) := by
  have he : (u/r)^((7:ℝ)/4) = (u/r)^((3:ℝ)/2)*(u/r)^((1:ℝ)/4) := by
    rw [← Real.rpow_add (div_pos hu hr)]
    norm_num
  have hrat : u/r ≤ a := (div_le_iff₀ hr).mpr hua
  have hm := Real.rpow_le_rpow (div_nonneg hu.le hr.le) hrat (by norm_num : (0:ℝ) ≤ 1/4)
  calc
    nᵤ ≤ D*nᵣ*((u/r)^((3:ℝ)/2)*(u/r)^((1:ℝ)/4)) := by simpa only [he] using hcomp
    _ ≤ D*nᵣ*((u/r)^((3:ℝ)/2)*a^((1:ℝ)/4)) := by gcongr
    _ = _ := by rw [Real.div_rpow hu.le hr.le]; ring

lemma three_halves_double_factor {b : ℝ} (hb : 0 ≤ b) :
    (2*b)^((3:ℝ)/2)-b^((3:ℝ)/2) = ((2:ℝ)^((3:ℝ)/2)-1)*b^((3:ℝ)/2) := by
  rw [Real.mul_rpow (by norm_num) hb]
  ring

lemma three_halves_double_pos : 0 < (2:ℝ)^((3:ℝ)/2)-1 := by
  have h := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (by norm_num : (0:ℝ) < 3/2)
  linarith

noncomputable def occupationCoefficient (J C q M b r ρ A δ : ℝ) : ℝ :=
  C*J*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1)) +
  M*J*(2*ρ)^((1:ℝ)/4) + M*J*A^((1:ℝ)/4)*δ

lemma occupationCoefficient_nonneg {J C q M b r ρ A δ : ℝ}
    (hJ : 0 ≤ J) (hC : 0 ≤ C) (hq : 0 < q) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    0 ≤ occupationCoefficient J C q M b r ρ A δ := by
  unfold occupationCoefficient
  have hp := three_halves_double_pos
  positivity

lemma occupationCoefficient_lower {J C q M b r ρ A δ z : ℝ}
    (hJ : 0 ≤ J) (hC : 0 ≤ C) (hq : 0 < q) (hM : 0 ≤ M)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hz : z ≤ C*J*(b/r)^((1:ℝ)/4)*b^((3:ℝ)/2)) :
    z ≤ occupationCoefficient J C q M b r ρ A δ*
      (q*((2*b)^((3:ℝ)/2)-b^((3:ℝ)/2))) := by
  have hden : 0 < q*((2:ℝ)^((3:ℝ)/2)-1) := mul_pos hq three_halves_double_pos
  have hrest : 0 ≤ M*J*(2*ρ)^((1:ℝ)/4)+M*J*A^((1:ℝ)/4)*δ := by positivity
  have hp : 0 ≤ b^((3:ℝ)/2) := Real.rpow_nonneg hb _
  rw [three_halves_double_factor hb]
  apply hz.trans
  have hcoefficient : C*J*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1)) ≤
      occupationCoefficient J C q M b r ρ A δ := by
    unfold occupationCoefficient
    linarith
  have hm := mul_le_mul hcoefficient (le_refl (q*((2:ℝ)^((3:ℝ)/2)-1)*b^((3:ℝ)/2)))
    (mul_nonneg hden.le hp) (occupationCoefficient_nonneg hJ hC hq hM hb hr hρ hA hδ)
  rw [← mul_assoc, div_mul_cancel₀ _ hden.ne'] at hm
  simpa only [mul_assoc] using hm

lemma occupationCoefficient_upper {J C q M b r ρ A δ t u v : ℝ}
    (hJ : 0 ≤ J) (hC : 0 ≤ C) (hq : 0 < q) (hM : 0 < M)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hv : v ≤ t*J*(2*ρ)^((1:ℝ)/4)*u^((3:ℝ)/2)) :
    v ≤ occupationCoefficient J C q M b r ρ A δ*(t/M*u^((3:ℝ)/2)) := by
  have hfirst : 0 ≤ C*J*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1)) := by
    have hp := three_halves_double_pos
    positivity
  have hlast : 0 ≤ M*J*A^((1:ℝ)/4)*δ := by positivity
  have hcoef : M*J*(2*ρ)^((1:ℝ)/4) ≤ occupationCoefficient J C q M b r ρ A δ := by
    unfold occupationCoefficient
    linarith
  have hm := mul_le_mul hcoef (le_refl (t/M*u^((3:ℝ)/2)))
    (by positivity) (occupationCoefficient_nonneg hJ hC hq hM.le hb hr hρ hA hδ)
  apply hv.trans
  convert hm using 1
  field_simp

lemma occupationCoefficient_far {J C q M b r ρ A δ t u v : ℝ}
    (hJ : 0 ≤ J) (hC : 0 ≤ C) (hq : 0 < q) (hM : 0 < M)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hv : v ≤ t*J*A^((1:ℝ)/4)*u^((3:ℝ)/2)*δ) :
    v ≤ occupationCoefficient J C q M b r ρ A δ*(t/M*u^((3:ℝ)/2)) := by
  have hfirst : 0 ≤ C*J*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1)) := by
    have hp := three_halves_double_pos
    positivity
  have hnear : 0 ≤ M*J*(2*ρ)^((1:ℝ)/4) := by positivity
  have hcoef : M*J*A^((1:ℝ)/4)*δ ≤ occupationCoefficient J C q M b r ρ A δ := by
    unfold occupationCoefficient
    linarith
  have hm := mul_le_mul hcoef (le_refl (t/M*u^((3:ℝ)/2)))
    (by positivity) (occupationCoefficient_nonneg hJ hC hq hM.le hb hr hρ hA hδ)
  apply hv.trans
  convert hm using 1
  field_simp

end DirectionalTransience

end

end

end OAI
