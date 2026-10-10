import Mathlib
import OAI.Geometry.Cannon.Conformal.BoundedCrossRatios

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonQM
open Set Metric Filter Bornology

lemma plane_weakQS_of_bounded (f : ℂ ≃ₜ ℂ) {C : ℝ} (hC : 0 < C)
    (hf : ∀ x y z w : ℂ, Distinct x y z w → (crossRatio x y z w : ℝ) ≤ 2 →
      (crossRatio (f x) (f y) (f z) (f w) : ℝ) ≤ C) :
    CannonMetricQC.WeakQS f (1+2*C) := by
  intro x y z hxyz
  have hη0 : 0 ≤ C := hC.le
  have hH : 1 ≤ 1+2*C := by linarith
  by_cases hxy : x=y
  · subst y; simp; positivity
  by_cases hxz : x=z
  · subst z
    have : x=y := dist_eq_zero.mp (le_antisymm (by simpa using hxyz) dist_nonneg)
    exact (hxy this).elim
  by_cases hyz : y=z
  · subst z
    exact le_mul_of_one_le_left dist_nonneg hH
  have ht : Tendsto f (cobounded ℂ) (cobounded ℂ) := by
    simpa only [cobounded_eq_cocompact] using f.isClosedEmbedding.tendsto_cocompact
  have hs := eventually_dist_large y (dist z y)
  have hi := ht.eventually (eventually_dist_large (f z) (dist (f y) (f z)))
  obtain ⟨w,hw,hwi,hwx⟩ := (hs.and (hi.and (eventually_ne_cobounded x))).exists
  have hwy : w ≠ y := by intro he; rw [he,dist_self] at hw; exact not_lt_of_ge dist_nonneg hw
  have hwz : w ≠ z := by intro he; rw [he] at hw; exact (lt_irrefl _ hw)
  have hquad : Distinct x y w z := ⟨hxy,hwx.symm,hxz,hwy.symm,hyz,hwz⟩
  have hsource : dist w z ≤ 2*dist y w := by
    have hh := dist_triangle w y z
    rw [dist_comm z y] at hw
    rw [dist_comm w y] at hw hh
    linarith
  have htarget : dist (f y) (f w) ≤ 2*dist (f w) (f z) := by
    have hh := dist_triangle (f y) (f z) (f w)
    rw [dist_comm (f z) (f w)] at hh
    linarith
  have hp : 0 < dist x z := dist_pos.mpr hxz
  have hpy : 0 < dist y w := dist_pos.mpr hwy.symm
  have hrat : crossRatio x y w z ≤ 2 := by
    have hh : dist x y*dist w z ≤ 2*(dist x z*dist y w) := by
      calc
        _ ≤ dist x z*(2*dist y w) := mul_le_mul hxyz hsource dist_nonneg dist_nonneg
        _ = _ := by ring
    apply NNReal.coe_le_coe.mp
    change dist x y*dist w z/(dist x z*dist y w) ≤ (2:ℝ)
    exact (div_le_iff₀ (mul_pos hp hpy)).mpr hh
  have hc := hf x y w z hquad (by exact_mod_cast hrat)
  have hfxz : 0 < dist (f x) (f z) := dist_pos.mpr (fun he => hxz (f.injective he))
  have hfyw : 0 < dist (f y) (f w) := dist_pos.mpr (fun he => hwy (f.injective he).symm)
  have hfwz : 0 < dist (f w) (f z) := dist_pos.mpr (fun he => hwz (f.injective he))
  have hcR : dist (f x) (f y)*dist (f w) (f z) ≤
      C*(dist (f x) (f z)*dist (f y) (f w)) := by
    have hh := hc
    change dist (f x) (f y)*dist (f w) (f z)/(dist (f x) (f z)*dist (f y) (f w)) ≤ C at hh
    exact (div_le_iff₀ (mul_pos hfxz hfyw)).mp hh
  have he : dist (f x) (f y) ≤ 2*C*dist (f x) (f z) := by
    apply (mul_le_mul_iff_left₀ hfwz).mp
    calc
      _ ≤ C*(dist (f x) (f z)*dist (f y) (f w)) := hcR
      _ ≤ C*(dist (f x) (f z)*(2*dist (f w) (f z))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htarget dist_nonneg) hη0
      _ = _ := by ring
  nlinarith [dist_nonneg (x:=f x) (y:=f z)]

lemma BoundedCrossRatios.plane_weakQS (f : ℂ ≃ₜ ℂ) (hf : BoundedCrossRatios f) :
    ∃ H : ℝ, 0 < H ∧ CannonMetricQC.WeakQS f H := by
  obtain ⟨C,hC,hc⟩ := hf 2
  exact ⟨1+2*C,by positivity,plane_weakQS_of_bounded f hC hc⟩
end CannonQM

end
end
end
end
end
end

end OAI
