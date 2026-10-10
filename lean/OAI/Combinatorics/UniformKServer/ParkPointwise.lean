import Mathlib
import OAI.Combinatorics.UniformKServer.ParkCoefficients
import OAI.Combinatorics.UniformKServer.ParkScale

namespace OAI

                                    
section

/-! Height-free actual parked coefficients. The good-scale dyadic grouping in
 the manuscript is replaced by a stronger logarithmic capacity telescope. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem pointwise (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q c ρ : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (hc : 0<c) (hρ : 0<ρ) (p J : ℕ) (hs : 67*q^p≤1)
    (b d : ℕ→ℝ) (hb : ∀ j, 0≤b j)
    (hden : ∀ j<J, inner μ y R q j≤ρ*d j)
    (hind : ∀ j<J, b j/d j≤ρ*c)
    (hcap : ∀ j<J, tail b J j≤c*(outer μ y R q j-1)) :
    (∑ j∈range J, b j/d j)≤ρ*c*(2+(p:ℝ)/Real.log 2)*Real.log K := by
  let g : ℕ→ℝ := fun j => if bad μ y R q j then 0 else b j
  have hg (j : ℕ) : 0≤g j := by dsimp [g]; split_ifs <;> [exact le_rfl; exact hb j]
  have hgb (j : ℕ) : g j≤b j := by dsimp [g]; split_ifs <;> [exact hb j; exact le_rfl]
  have htail (j : ℕ) : tail g J j≤tail b J j := sum_le_sum fun i _ => hgb i
  have hk : 1≤K := by have ht := sum_nonneg fun z (_ : z∈univ) => hμ z; linarith
  have hgt : tail g J 0≤c*(K-1) := by
    by_cases hJ : 0<J
    · have ht := (htail 0).trans (hcap 0 hJ)
      have hm := (GeometricMass.mass_total μ hμ y (67*GeometricMass.radius R q 0)).trans hK
      exact ht.trans (mul_le_mul_of_nonneg_left (by dsimp [outer]; linarith) hc.le)
    · have he : J=0 := by omega
      simp only [he,tail_end]
      exact mul_nonneg hc.le (by linarith)
  have hgood := capacity_telescope c K hc hk g (outer μ y R q) hg J
    (outer_one μ hμ y R q) (fun j hj => (htail j).trans (hcap j hj)) hgt
  have hpoint (j : ℕ) (hj : j<J) : b j/d j≤
      (if bad μ y R q j then ρ*c else 0)+2*ρ*(g j/outer μ y R q j) := by
    by_cases hbad : bad μ y R q j
    · simpa only [g,ite_eq_left hbad,zero_div,mul_zero,add_zero] using hind j hj
    · have ha : 0< outer μ y R q j := by linarith [outer_one μ hμ y R q j]
      have hd : 0< d j := by
        have hh := hden j hj
        have hi := inner_one μ hμ y R q j
        by_contra hn
        have := mul_nonpos_of_nonneg_of_nonpos hρ.le (le_of_not_gt hn)
        linarith
      have had : outer μ y R q j≤2*ρ*d j := by
        have hba : outer μ y R q j≤2*inner μ y R q j := le_of_not_gt hbad
        linarith [hden j hj]
      simp only [g,ite_eq_right hbad,zero_add]
      rw [←mul_div_assoc]
      apply (div_le_div_iff₀ hd ha).mpr
      nlinarith [mul_le_mul_of_nonneg_left had (hb j)]
  have ht := sum_le_sum fun j hj => hpoint j (mem_range.mp hj)
  rw [sum_add_distrib,←sum_filter,sum_const,nsmul_eq_mul,←mul_sum] at ht
  have hbad := bad_count μ hμ y K R q hK hR hq p J hs
  have hcρ : 0≤ρ*c := mul_nonneg hρ.le hc.le
  have h1 := mul_le_mul_of_nonneg_right hbad hcρ
  have h2 := mul_le_mul_of_nonneg_left hgood (by positivity : 0≤2*ρ)
  calc
    _ ≤ _ := ht
    _ ≤ ((p:ℝ)*Real.log K/Real.log 2)*(ρ*c)+(2*ρ)*(c*Real.log K) := add_le_add h1 h2
    _ = _ := by ring

end UniformKServer.ParkCoefficients

end


end

end OAI
