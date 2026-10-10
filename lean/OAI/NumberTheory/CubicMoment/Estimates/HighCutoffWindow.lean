import OAI.NumberTheory.CubicMoment.Estimates.LowCutoffWindow
import OAI.NumberTheory.CubicMoment.Estimates.LocalizedStopped

namespace OAI

/-! Apply the high-height logarithmic estimate to the actual smooth
Fourier windows in the sharp prime interval decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

theorem high_stopped_cutoff_window
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (j r : ℕ) :
    ∃ γ K Z₀ : ℝ, 0 < γ ∧ 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X₀ T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^(2+γ) → A ≤ Z^3 →
      0 < X₀ → Z^(1/50:ℝ) ≤ T → 0 < H → T ≤ 2*Real.pi*H →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧
        1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨Kh,hKh,hsecond⟩ := localizedEndpointWeight_second_uniform
  let Mh := 1+Kh
  have hMh : 0 ≤ Mh := by dsimp [Mh]; positivity
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := localized_stopped_bilinear_log_saving
    hpnt hMV hC hHuxley hM j r
  refine ⟨γ,2*K*Mh,max Z₀ 65536,hγ,by dsimp [Mh]; positivity,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hTH hP hS
  have hZ1 : 1 ≤ Z := by have hh := (le_max_right Z₀ 65536).trans hZ; linarith
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ1) (1/50:ℝ)).trans_le hT
  let h := localizedEndpointWeight H T
  have hhi : Integrable h := localizedEndpointWeight_integrable H hTp
  have hhd : Differentiable ℝ h := (localizedEndpointWeight_smooth H hTp).differentiable (by simp)
  have hder := localizedEndpointWeight_derivatives H hTp
  have hh (t : ℝ) : ‖h t‖ ≤ Mh := (localizedEndpointWeight_norm_le H hTp t).trans
    (by dsimp [Mh]; linarith)
  have hhs (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : h t = 0 :=
    localizedEndpointWeight_zero H hTp t ht
  have hh2 (t : ℝ) : ‖(T:ℂ)^2*deriv (deriv h) t‖ ≤ Mh :=
    (hsecond H T hH hTp hTH t).trans (by dsimp [Mh]; linarith)
  have hhs2 (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : deriv (deriv h) t = 0 :=
    localizedEndpointWeight_second_zero H hTp t ht
  have hx := hbound R D E U P S ψ w Z A X₀ T Mh v selected remaining
    hR hE hψ hw hrough hv hsize ((le_max_left _ _).trans hZ) hA hAupper hAcubic hX hT hMh hP hS
    h hhi hhd hder.1 hder.2.1 hder.2.2 hh hhs hh2 hhs2
  have hx2 := hbound R D E U P S ψ w Z A (2*X₀) T Mh v selected remaining
    hR hE hψ hw hrough hv hsize ((le_max_left _ _).trans hZ) hA hAupper hAcubic (by positivity) hT hMh hP hS
    h hhi hhd hder.1 hder.2.1 hder.2.2 hh hhs hh2 hhs2
  unfold cutoffBilinearWindow
  rw [bilinear_cutoff_window_endpoints P S _ _ H hTp hX]
  exact (norm_sub_le _ _).trans ((add_le_add hx hx2).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
