import OAI.MeasureTheory.Falconer.Estimates.SpatialAnnulusKernel

namespace OAI

/-! # Exact separated spatial factors in every dimension. Fourier inversion is applied on Space d, with an integrable coefficient and endpoint phases of norm one. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap ComplexConjugate
variable {d : ℕ}

noncomputable def spatialFourierCoeff (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 𝓢(Space d, ℂ) := 𝓕 (spatialAnnulusSchwartz (d := d) δ L hδ hL j)

noncomputable def spatialFourierCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : ℝ := ∫ ξ : Space d, ‖spatialFourierCoeff (d := d) δ L hδ hL j ξ‖

noncomputable def spatialFourierPhase (s : ℝ) (ξ x : Space d) : ℂ :=
  Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • x))*Complex.I)

theorem spatialFourierCost_nonneg (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : 0 ≤ spatialFourierCost (d := d) δ L hδ hL j :=
  integral_nonneg (fun _ => norm_nonneg _)

@[fun_prop] theorem spatialFourierPhase_continuous (s : ℝ) :
    Continuous (fun z : Space d × Space d => spatialFourierPhase s z.1 z.2) := by
  unfold spatialFourierPhase
  fun_prop

theorem spatialFourierPhase_norm (s : ℝ) (ξ x : Space d) :
    ‖spatialFourierPhase s ξ x‖ = 1 := by
  simp [spatialFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem spatialFourierPhase_sub (s : ℝ) (ξ x y : Space d) :
    spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y) =
      Complex.exp (↑(2*Real.pi*inner ℝ ξ (s⁻¹ • (x-y)))*Complex.I) := by
  simp only [spatialFourierPhase, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, smul_sub,
    inner_sub_right, mul_sub, Complex.ofReal_sub]
  congr 1
  ring

theorem spatialFourierCoeff_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) : Integrable (spatialFourierCoeff (d := d) δ L hδ hL j) :=
  (spatialFourierCoeff (d := d) δ L hδ hL j).integrable

theorem spatialFourierSeparation_integrable (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : Space d) :
    Integrable (fun ξ => spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y))) := by
  have hx : Continuous (fun ξ => spatialFourierPhase s ξ x) := by
    unfold spatialFourierPhase
    fun_prop
  have hy : Continuous (fun ξ => spatialFourierPhase s ξ y) := by
    unfold spatialFourierPhase
    fun_prop
  apply (spatialFourierCoeff_integrable δ L hδ hL j).norm.mono'
    ((spatialFourierCoeff (d := d) δ L hδ hL j).continuous.mul
      (hx.mul (Complex.continuous_conj.comp hy))).aestronglyMeasurable
  filter_upwards with ξ
  simp [spatialFourierPhase_norm]

theorem spatialFourierSeparation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (s : ℝ) (x y : Space d) :
    (∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y))) =
      spatialAnnulusKernel (d := d) δ L hδ hL j (s⁻¹ • (x-y)) := by
  have he := congrArg (fun f : 𝓢(Space d, ℂ) => f (s⁻¹ • (x-y)))
    (show (𝓕⁻ (𝓕 (spatialAnnulusSchwartz (d := d) δ L hδ hL j) : 𝓢(Space d, ℂ)) :
      𝓢(Space d, ℂ)) = spatialAnnulusSchwartz (d := d) δ L hδ hL j from
      FourierTransform.fourierInv_fourier_eq _)
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at he
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards with ξ
  rw [spatialFourierPhase_sub]
  exact mul_comm _ _

theorem spatialInverseDistance_separation (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) {s : ℝ} (hs : 0 < s) {x y : Space d}
    (hd₁ : δ ≤ dist x y / s) (hd₂ : dist x y / s ≤ L) :
    (↑((dist x y / s)^j)⁻¹ : ℂ) =
      ∫ ξ, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        (spatialFourierPhase s ξ x * conj (spatialFourierPhase s ξ y)) := by
  have hn : ‖s⁻¹ • (x-y)‖ = dist x y / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, dist_eq_norm, div_eq_inv_mul]
  rw [spatialFourierSeparation, spatialAnnulusKernel_eq δ L hδ hL j
    (by rwa [hn]) (by rwa [hn]), hn, Complex.ofReal_inv]

end Falconer

end OAI
