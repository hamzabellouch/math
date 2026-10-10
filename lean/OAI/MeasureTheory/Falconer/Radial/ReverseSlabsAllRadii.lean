import OAI.MeasureTheory.Falconer.Angular.ReverseCapsAllRadii

namespace OAI

/-! # Original all-radius slab bounds under restriction of a pair relation -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_slabs_all_radii (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N v : ℕ} (hvN : v ≤ N) {K K' ζ : ℝ} (hK : K ≤ K')
    (hslab : ∀ᵐ z ∂μ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K*r^ζ)) :
    ∀ᵐ z ∂ρ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^v ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G' ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K'*r^ζ) := by
  filter_upwards [hρ.ae_le hslab] with z hz
  intro u hu r hr hr1
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have hm : ν {x | (z,x) ∈ G' ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤
      ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hm.trans ((hz u hu r (hδ.trans hr) hr1).trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK
    (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ 1/(2:ℝ)^v).trans hr) _))

end Falconer

end OAI
