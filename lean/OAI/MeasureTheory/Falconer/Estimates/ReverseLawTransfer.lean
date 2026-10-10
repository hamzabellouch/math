import OAI.MeasureTheory.Falconer.Estimates.SourceClassOriginalLaws
import OAI.MeasureTheory.Falconer.Radial.RadialSphereBounds

namespace OAI

/-! # Original reverse cap and slab bounds on the coarser middle scale -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem reverse_caps_transfer (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N M : ℕ} (hMN : M ≤ N) {K K' q : ℝ} (hK : K ≤ K')
    (hcap : ∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      ∀ u : Space d, ‖u‖ = 1 →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤ ENNReal.ofReal (K*r^q)) :
    ∀ᵐ z ∂ρ, ∀ w : Sphere d, ∀ j : ℕ, j ≤ M →
      ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal (K'*(1/(2:ℝ)^j)^q) := by
  filter_upwards [hρ.ae_le hcap] with z hz
  intro w j hj
  have hr : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (hj.trans hMN))
  have hr1 : 1/(2:ℝ)^j ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hmono : ν {x | (z,x) ∈ G' ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} ≤
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < 1/(2:ℝ)^j} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hmono.trans ((hz _ hr hr1 w (sphere_norm w)).trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (by positivity))

theorem reverse_slabs_transfer (μ ρ ν : Measure (Space d)) (hρ : ρ ≪ μ)
    {G G' : Set (Space d × Space d)} (hsub : G' ⊆ G)
    {N M : ℕ} (hMN : M ≤ N) {K K' ζ : ℝ} (hK : K ≤ K')
    (hslab : ∀ᵐ z ∂μ, ∀ u : Space d, ‖u‖ = 1 → ∀ r : ℝ,
      1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} ≤ ENNReal.ofReal (K*r^ζ)) :
    ∀ᵐ z ∂ρ, ∀ w : Sphere d, ∀ r : ℝ, 1/(2:ℝ)^M ≤ r → r ≤ 1 →
      ν {x | (z,x) ∈ G' ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} ≤
        ENNReal.ofReal (K'*r^ζ) := by
  filter_upwards [hρ.ae_le hslab] with z hz
  intro w r hr hr1
  have hNM : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^M :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hMN)
  have hmono : ν {x | (z,x) ∈ G' ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} ≤
      ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space d) (normalize (x-z))| ≤ r} :=
    measure_mono (fun _ hx => ⟨hsub hx.1,hx.2⟩)
  apply hmono.trans ((hz w (sphere_norm w) r (hNM.trans hr) hr1).trans ?_)
  have hr0 : 0 ≤ r := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^M).trans hr
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr0 _))

end Falconer

end OAI
