import Mathlib
import OAI.Combinatorics.KMedian.Process.TaperData

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem minimal_near_unit {g P D N : ℝ} (d : I → ℝ) (S : Finset I)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P < 1) (hD : 0 ≤ D)
    (hunit : (S.card:ℝ)*g=1) (hnear : ∀ i ∈ S, d i ≤ D)
    (hminimal : ∀ R : ℝ, 0 < R → 1 ≤ mass g P d (1/R) → N ≤ R) :
    N ≤ D/(1-P) := by
  have hden : 0 < 1-P := sub_pos.mpr hP1
  by_cases hd : 0 < D
  · apply hminimal _ (div_pos hd hden)
    rw [one_div_div]
    exact mass_from_near_unit d S hg hP hP1 hd hunit hnear
  · have he : D=0 := le_antisymm (le_of_not_gt hd) hD
    rw [he, zero_div]
    by_contra hn
    have hN : 0 < N := lt_of_not_ge hn
    let D' := (N/2)*(1-P)
    have hd' : 0 < D' := mul_pos (by linarith only [hN]) hden
    have hn' : ∀ i ∈ S, d i ≤ D' := by
      intro i hi
      exact (he ▸ hnear i hi).trans hd'.le
    have hh := hminimal (D'/(1-P)) (div_pos hd' hden)
      (by rw [one_div_div]; exact mass_from_near_unit d S hg hP hP1 hd' hunit hn')
    dsimp only [D'] at hh
    rw [mul_div_cancel_right₀ _ (ne_of_gt hden)] at hh
    linarith only [hh,hN]

variable {X : Type*} [PseudoMetricSpace X]

theorem backup_source_close {g P R : ℝ} (location : I → X) (client : X)
    (S : Finset I) (N : I → ℝ) (q : I → I → ℝ)
    (hg : 0 ≤ g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hR : 0 ≤ R)
    (hunit : (S.card:ℝ)*g=1) (hnear : ∀ i ∈ S, dist client (location i) ≤ R)
    (hN : ∀ i, 0 ≤ N i) (hq : ∀ h i, 0 ≤ q h i)
    (hminimal : ∀ i ∈ S, ∀ r : ℝ, 0 < r →
      1 ≤ mass g P (fun t => dist (location i) (location t)) (1/r) → N i ≤ r)
    (htaper : ∀ h i, 0 < q h i → dist (location i) (location h) ≤ N i*(1-P*q h i))
    {i h : I} (hi : i ∈ S) (hedge : 0 < q h i) :
    dist client (location h) ≤ 5*R := by
  have hpair : ∀ t ∈ S, dist (location i) (location t) ≤ 2*R := by
    intro t ht
    have hh := dist_triangle (location i) client (location t)
    rw [dist_comm (location i) client] at hh
    linarith only [hh,hnear i hi,hnear t ht]
  have hp : P < 1 := by linarith only [hP1]
  have hn := minimal_near_unit (fun t => dist (location i) (location t)) S hg hP hp
    (show 0 ≤ 2*R by positivity) hunit hpair (hminimal i hi)
  have hb : (2*R)/(1-P) ≤ 4*R := by
    apply (div_le_iff₀ (sub_pos.mpr hp)).mpr
    have hh := mul_le_mul_of_nonneg_left hP1 hR
    nlinarith only [hh]
  have he : dist (location i) (location h) ≤ N i := by
    apply (htaper h i hedge).trans
    have hh : 0 ≤ P*q h i := mul_nonneg hP.le (hq h i)
    nlinarith only [hN i,hh]
  have hh := dist_triangle client (location i) (location h)
  linarith only [hh,hnear i hi,he,hn,hb]

end MetricKMedian.Taper
end
end

end OAI
