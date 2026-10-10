import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.AdmissibleCutoffWaveLocalizedDerivatives

namespace OAI

noncomputable section
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
theorem normal_family_wave_localized_estimates (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ T : ℝ, 0 < T ∧ ∀ q ∈ metricFrameSet g K, ∀ (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix), ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (normalFamilyWave g φ A b q z Q ζ m D n) x‖ ≤
              T*n^k*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x))*
                Real.exp (-(κ/2)*n*‖x‖^2) ∧
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1)
              (fun i j y => A (q,y) i j) (fun j y => b (q,y) j)
              (normalFamilyWave g φ A b q z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*normalFamilyWave g φ A b q z Q ζ m D n y) x‖ ≤
              T*(n^(D+1))⁻¹*Real.exp (n*normalWaveProfile g φ q (normalWaveEquiv x)) := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  obtain ⟨r1,hr1,he1⟩ := admissible_cutoff_wave_localized_derivatives G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  obtain ⟨r2,hr2,he2⟩ := admissible_cutoff_wave_residual G β hG hβ hG0 hGd hGc hβc
    Φ hΦ hΦ0 hΦ2 B C hκ m D
  refine ⟨min r1 r2,lt_min hr1 hr2,?_⟩
  intro ζ hζ hζ0
  obtain ⟨T1,hT1,hb1⟩ := he1 ζ hζ hζ0
  obtain ⟨T2,hT2,hb2⟩ := he2 ζ hζ hζ0
  refine ⟨max T1 T2,lt_of_lt_of_le hT1 (le_max_left _ _),?_⟩
  intro q hq z Q hz hn hQ n hn1 hlin x hx k hk
  have hx1 := Metric.ball_subset_ball (min_le_left r1 r2) hx
  have hx2 := Metric.ball_subset_ball (min_le_right r1 r2) hx
  refine ⟨(hb1 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx1 k hk).trans ?_,
    (hb2 ⟨q,hq⟩ z Q hz hn hQ n hn1 hlin x hx2 k hk).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left T1 T2) (pow_nonneg (le_trans zero_le_one hn1) _))
        (Real.exp_pos _).le) (Real.exp_pos _).le
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right T1 T2)
        (inv_nonneg.mpr (pow_nonneg (le_trans zero_le_one hn1) _))) (Real.exp_pos _).le
end YauCounterexamples
end

end OAI
