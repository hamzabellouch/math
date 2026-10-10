import OAI.MeasureTheory.Falconer.Estimates.ReverseLawTransfer

namespace OAI

/-! # Reverse-cap bounds under source restriction at every original radius -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ r : ℝ, 1/(2:ℝ)^v ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K'*r^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro r hr hr1 u hu
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) u < r} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz r (hδ.trans hr) hr1 u hu).trans ?_)
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI
