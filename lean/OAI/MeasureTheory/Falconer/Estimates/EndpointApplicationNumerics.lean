import OAI.MeasureTheory.Falconer.Estimates.EndpointRowBudget
import OAI.MeasureTheory.Falconer.Geometry.ActiveCoverScale

namespace OAI

/-! # Scalar endpoint budgets in the form used by the controlled slice -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem endpoint_stable_small {h : ℕ} {δ ρ : ℝ} (hδ : δ ≤ ρ)
    (hs : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) : 2*(h:ℝ)*δ < 1 := by
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hn : (h+3:ℝ) ≥ 1 := by linarith
  have hb : (h:ℝ)*ρ ≤ 1/4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hδ hh]

theorem endpoint_active_cover_power {h : ℕ} {δ ε u C ρ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεu : ε ≤ u) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hcount : (2*(1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)))^h*δ^(-1-12*u) ≤ δ^(-1-40*u)) :
    (δ^(-u))^11*(δ^(-(h+1:ℝ)-ε)*
      (2*(δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ δ^(-1-40*u) := by
  let D : ℝ := 1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hh := gaussian_active_cover_scale h hδ hδ1 hεu hD
    (le_refl (δ^(-(h+1:ℝ)-ε)))
  have hr : δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1) = D*δ := by dsimp [D]; ring
  rw [hr]
  have hq : -((h+1:ℝ)-(h:ℝ)) = -1 := by ring
  rw [hq] at hh
  simp only [gaussian_scale_power hδ,Nat.cast_ofNat] at hh
  have hp : δ^(-(12*u))*δ^((-1:ℝ)) = δ^(-1-12*u) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  rw [mul_assoc,hp] at hh
  simpa only [gaussian_scale_power hδ,Nat.cast_ofNat] using hh.trans hcount

theorem endpoint_bad_mass_ennreal {δ u τ : ℝ} (hδ : 0 < δ)
    (hbad : δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3)) :
    ENNReal.ofReal (δ^τ)+2*ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal (δ^τ) ≤
      ENNReal.ofReal ((δ^(2*u))^3/(4*((δ^(-u))^6)^3)) := by
  have hp : (δ^(-u))^6 = δ^(-6*u) := by
    simpa only [Nat.cast_ofNat,neg_mul] using gaussian_scale_power hδ 6
  rw [hp]
  calc
    _ = ENNReal.ofReal (δ^τ+2*δ^(-6*u)*δ^τ) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ^(-6*u)),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbad

theorem endpoint_selection_row_budget {δ u τ c₁ c₂ V : ℝ}
    (hδ : 0 < δ) (hV : 0 ≤ V) (Z A₁ A₂ : ℝ≥0∞)
    (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbase : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
      ENNReal.ofReal (1/(4*δ^(-u))) := by
  have hh := endpoint_row_base_ennreal hδ hV Z A₁ A₂ hZ hA₁ hA₂ hbase
  have hp (j : ℕ) : (δ^(-u))^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hi : δ^u/4 = 1/(4*δ^(-u)) := by rw [Real.rpow_neg hδ.le]; field_simp
  rw [hp 6,hp 3]
  simpa only [Nat.cast_ofNat,neg_mul,hi] using hh

end Falconer

end OAI
