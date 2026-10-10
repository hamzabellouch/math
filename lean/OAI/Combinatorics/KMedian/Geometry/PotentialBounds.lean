import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalPotential
import OAI.Combinatorics.KMedian.Geometry.MomentAnalysis

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic Finset

variable {I : Type*}

theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half hx
  unfold B
  linarith only [h]

theorem m_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m x ≤ 1 := by
  have hA := A_le_two hx1
  have hBx := mul_nonneg (B_nonneg x) hx0
  unfold m
  unfold B at hBx
  linarith only [hA, hBx]

theorem coefficient_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1 ≤ coefficient x y ∧ coefficient x y ≤ 3 := by
  refine ⟨coefficient_ge_one hy0, ?_⟩
  rw [coefficient_eq]
  have hm := m_le_one hx0 hx1
  have hB := (mul_le_of_le_one_left hy0 (B_le_one hx0)).trans hy1
  linarith only [hm, hB]

theorem cost_le_mass_mul {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, d i ≤ R) : cost g d S ≤ mass g S*R := by
  have h := sum_le_sum (fun i (hi : i ∈ S) => mul_le_mul_of_nonneg_left (hd i hi) hg)
  simpa only [cost, mass, sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem cost_le_radius {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hR : 0 ≤ R) (hd : ∀ i ∈ S, d i ≤ R) (hy : mass g S ≤ 1) :
    cost g d S ≤ R := by
  exact (cost_le_mass_mul hg hd).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hy hR)

theorem potential_bounds {x g R b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) :
    0 ≤ potential x g d S b ∧ potential x g d S b ≤ 8*R := by
  have hy0 := mass_nonneg hg S
  have hV0 := cost_nonneg hg hd0
  have hVR := cost_le_radius hg hR hdR hy
  have ha := coefficient_bounds hx0 hx1 hy0 hy
  have hcap0 := mul_nonneg (sub_nonneg.mpr hy) hb0
  have hcap := mul_le_mul_of_nonneg_right (show 1-mass g S ≤ 1 by linarith only [hy0]) hb0
  have hc := mul_le_mul ha.2 hVR hV0 (by norm_num : (0:ℝ) ≤ 3)
  rw [potential, ← coefficient_eq]
  constructor
  · exact add_nonneg (mul_nonneg (by linarith only [ha.1]) hV0) hcap0
  · nlinarith only [hc, hcap, hbR]

theorem internal_charge_bound {x g R b dh : ℝ} {d : I → ℝ} {S T : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hTS : T ⊆ S) (hdh0 : 0 ≤ dh) (hdhR : dh ≤ R) :
    |dh-(∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0)-potential x g d S b| ≤ 8*R := by
  have hf := potential_bounds hx0 hx1 hg hR hd0 hdR hy hb0 hbR
  have ha := (coefficient_bounds hx0 hx1 (mass_nonneg hg S) hy).1
  have hhinge0 : 0 ≤ ∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0 :=
    sum_nonneg (fun _ _ => mul_nonneg hg (le_max_right _ _))
  have hhinge : (∑ i ∈ T, g*max (dh-coefficient x (mass g S)*d i) 0) ≤ dh := by
    calc
      _ ≤ ∑ _i ∈ T, g*dh := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ hg
        apply max_le _ hdh0
        have hmul := mul_nonneg (show 0 ≤ coefficient x (mass g S) by linarith only [ha]) (hd0 i (hTS hi))
        linarith only [hmul]
      _ = mass g T*dh := by simp only [mass, sum_const, nsmul_eq_mul]; ring
      _ ≤ dh := mul_le_of_le_one_left hdh0 ((mass_mono hg hTS).trans hy)
  exact abs_le.mpr ⟨by linarith only [hf.2, hhinge], by linarith only [hf.1, hhinge0, hdhR, hR]⟩

theorem external_charge_bound {x y R δ Y V b : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hY0 : 0 ≤ Y) (hYV : Y ≤ V) (hVR : V ≤ R)
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) :
    |δ*b-coefficient x y*Y-B x*δ*(V-Y)| ≤ 8*R := by
  have ha := coefficient_bounds hx0 hx1 hy0 hy1
  have ha0 : 0 ≤ coefficient x y := by linarith only [ha.1]
  have hB0 := B_nonneg x
  have hB1 := B_le_one hx0
  have hδb0 := mul_nonneg hδ0 hb0
  have hδbR : δ*b ≤ 5*R := (mul_le_of_le_one_left hb0 hδ1).trans hbR
  have haY0 := mul_nonneg ha0 hY0
  have haYR := mul_le_mul ha.2 (hYV.trans hVR) hY0 (by norm_num : (0:ℝ) ≤ 3)
  have hBY0 := mul_nonneg (mul_nonneg hB0 hδ0) (sub_nonneg.mpr hYV)
  have hBYR : B x*δ*(V-Y) ≤ R := by
    have hm : B x*δ ≤ 1 := (mul_le_of_le_one_left hδ0 hB1).trans hδ1
    have h := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hYV)
    nlinarith only [h, hY0, hVR]
  exact abs_le.mpr ⟨by linarith only [hδb0, haYR, hBYR, hR],
    by linarith only [hδbR, haY0, hBY0, hR]⟩

end MetricKMedian.PhysicalPotential
end
end

end OAI
