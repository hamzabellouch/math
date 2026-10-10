import OAI.Geometry.Perimeter.Regularity.EllipticScaleStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def LinearContractionProperty (n : ℕ) (θ δ K : ℝ) : Prop :=
  ∀ (A : Euc n → Euc n →L[ℝ] Euc n), Continuous A →
  ∀ (f : Euc n → ℝ), ContDiff ℝ 1 f → ∀ F : Euc n → Euc n, Continuous F →
  ∀ (p : Euc n) (r : ℝ), 0 < r → WeakLinearEquation A f F (Metric.ball p r) →
  ∀ (A₀ : Euc n →L[ℝ] Euc n) (F₀ q : Euc n) (α β : ℝ), 0 ≤ α → 0 ≤ β →
    (∀ x∈Metric.ball p r, ‖ContinuousLinearMap.id ℝ (Euc n)-A x‖ ≤ δ ∧
      ‖A₀-A x‖ ≤ α ∧ ‖F x-F₀‖ ≤ β) →
    ∃ q' : Euc n, ‖q'-q‖^2 ≤ K*scaledGradientEnergy f p r q ∧
      scaledGradientEnergy f p (θ*r) q' ≤ scaledGradientEnergy f p r q/16+K*(α*‖q‖+β)^2

theorem exists_linear_contraction (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ θ δ K : ℝ, 0 < θ ∧ θ < min ρ (1/2) ∧ 0 < δ ∧ 1 ≤ K ∧ LinearContractionProperty n θ δ K := by
  obtain ⟨C,hC,hB⟩ := linear_gradient_scaled_step hn
  let V := volume.real (Metric.ball (0:Euc n) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  have htend : Tendsto (fun t : ℝ ↦ 2*C^2*t^2*V) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun t : ℝ ↦ 2*C^2*t^2*V) 0 := by fun_prop
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero,zero_mul] using hh.tendsto
  obtain ⟨s,hs,hsb⟩ := Metric.tendsto_nhds_nhds.mp htend (1/32) (by norm_num)
  let θ := min (s/2) (min (ρ/2) (1/4))
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hθs : θ < s := (min_le_left _ _).trans_lt (by linarith)
  have hθρ : θ < ρ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hθhalf : θ < 1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  have hsmall : 2*C^2*θ^2*V ≤ 1/32 := by
    have hh := hsb (x := θ) (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hθ] using hθs)
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
    exact hh.le
  let δ := Real.sqrt (θ^n/128)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ^2=θ^n/128 := Real.sq_sqrt (by positivity)
  have hdpart : 4*δ^2*(θ^n)⁻¹=1/32 := by rw [hδsq]; field_simp; norm_num
  let K := max 1 (max (C^2) (4*(θ^n)⁻¹*V))
  have hK : 1 ≤ K := le_max_left _ _
  have hKC : C^2 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKV : 4*(θ^n)⁻¹*V ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨θ,δ,K,hθ,lt_min hθρ hθhalf,hδ,hK,?_⟩
  intro A hA f hf F hF p r hr h A₀ F₀ q α β hα hβ hb
  obtain ⟨q',hqp,hqE⟩ := hB A hA f hf F hF p r hr h A₀ F₀ q δ α β hδ.le hα hβ hb
  have hE : 0  ≤  scaledGradientEnergy f p r q := scaledGradientEnergy_nonneg f p hr.le q
  refine ⟨q',hqp.trans (mul_le_mul_of_nonneg_right hKC hE),?_⟩
  have hqE' := hqE θ hθ hθhalf.le
  rw [hdpart] at hqE'
  have h1 := mul_le_mul_of_nonneg_right hsmall hE
  have h2 := mul_le_mul_of_nonneg_right hKV (sq_nonneg (α*‖q‖+β))
  change _ ≤ _ at hqE'
  dsimp only [V] at h1 h2
  nlinarith

theorem WeakLinearEquation.mono {A : Euc n → Euc n →L[ℝ] Euc n}
    {f : Euc n → ℝ} {F : Euc n → Euc n} {U W : Set (Euc n)}
    (h : WeakLinearEquation A f F U) (hWU : W⊆U) : WeakLinearEquation A f F W := by
  intro φ
  exact h ⟨φ.val,φ.property.1,φ.property.2.1,φ.property.2.2.trans hWU⟩

end RPISingularHarnack

end

end OAI
