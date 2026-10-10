import OAI.MeasureTheory.Falconer.Radial.RadialDyadicBracket
import OAI.MeasureTheory.Falconer.Radial.RadialScaleWindow

namespace OAI

/-! # From the retained dyadic scales to every cap radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radial_all_radius_bound (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (G : Set (Space d × Space d)) (N K : ℕ) {e ell ell₁ : ℝ}
    (hell : 0 ≤ ell) (hell₁ : ell ≤ ell₁) (he : 0 ≤ e) (hK : ell ≤ e*K)
    (hconst : (2:ℝ)^ell₁ ≤ ((2:ℝ)^N)^e)
    (hcap : ∀ j ∈ Finset.Icc (N/K) N, ∀ x w : Space d,
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} ≤
        ENNReal.ofReal (((2:ℝ)^j)^(-ell₁))) :
    ∀ x w : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ≤
        ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := by
  intro x w r hr hr1
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hR0 : 0 < (2:ℝ)^N := by positivity
  by_cases hs : r ≤ ((2:ℝ)^(N/K))⁻¹
  · obtain ⟨j,hjB,hjN,hjr,hrj⟩ := radial_dyadic_bracket_above N (N/K) hr hs
    have hbound := hcap j (Finset.mem_Icc.mpr ⟨hjB,hjN⟩) x w
    apply (measure_mono (show {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ r} ⊆
      {z | (x,z) ∈ G ∧ ‖normalize (z-x)-w‖ ≤ ((2:ℝ)^j)⁻¹} from
      fun z hz => ⟨hz.1,hz.2.trans hjr⟩)).trans
    apply hbound.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      ((2:ℝ)^j)^(-ell₁) = (((2:ℝ)^j)⁻¹)^ell₁ := by rw [Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]
      _ ≤ (2*r)^ell₁ := Real.rpow_le_rpow (by positivity) hrj.le (hell.trans hell₁)
      _ = (2:ℝ)^ell₁*r^ell₁ := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ ((2:ℝ)^N)^e*r^ell := by
        apply mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hell₁) (by positivity) (by positivity)
  · have hb : ((2:ℝ)^(N/K))⁻¹ ≤ r := (lt_of_not_ge hs).le
    have hexp : (N/K:ℕ)*(ell:ℝ) ≤ (N:ℝ)*e := by
      have hdiv : ((N/K:ℕ):ℝ)*(K:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N K
      calc
        _ ≤ ((N/K:ℕ):ℝ)*(e*K) := mul_le_mul_of_nonneg_left hK (by positivity)
        _ = (((N/K:ℕ):ℝ)*(K:ℝ))*e := by ring
        _ ≤ (N:ℝ)*e := mul_le_mul_of_nonneg_right hdiv he
    have hone : (1:ℝ) ≤ ((2:ℝ)^N)^e*(((2:ℝ)^(N/K))⁻¹)^ell := by
      rw [Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity),
        ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      exact Real.one_le_rpow (by norm_num) (by linarith)
    calc
      _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (1:ℝ) := by simp
      _ ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^ell) := ENNReal.ofReal_le_ofReal
        (hone.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hell) (by positivity)))

end Falconer

end OAI
