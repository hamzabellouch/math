import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointProfile
import OAI.NumberTheory.CubicMoment.Estimates.LowStopped

namespace OAI

/-! Apply the low-height logarithmic estimate to the actual smooth
Fourier windows in the sharp prime interval decomposition. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def cutoffBilinearWindow (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*
    heightFourierIntegral (fun t => cutoffHeightMultiplier H t*heightWindow T t)
      (Real.log (norm (a*b))-Real.log X₀)

theorem low_stopped_cutoff_window
    (hpnt : PrimaryPrimePNT) {C M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hM : 0 ≤ M) (j r a : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (R D E U P S : Finset Eisenstein) (ψ : ℝ → ℝ) (w Z A X₀ T H : ℝ)
        (v : Eisenstein → ℂ) (selected : Eisenstein → Eisenstein → Prop)
        (remaining : Eisenstein → Prop),
      (∀ b ∈ R, primary b) → (∀ e ∈ E, primary e) →
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → 1 ≤ w →
      (∀ b ∈ R, ∀ p ∈ primaryPrimeFactors b, w ≤ norm p) →
      (∀ b ∈ R, ‖v b‖ ≤ M) → Z < w^r →
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → A ≤ Z^3 →
      0 < X₀ → (1+Real.log Z)^Ct ≤ T → 0 < H → T ≤ 2*Real.pi*H →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧
        1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨Kh,hKh,hsecond⟩ := localizedEndpointWeight_second_uniform
  let Mh := 1+Kh
  have hMh : 0 ≤ Mh := by dsimp [Mh]; positivity
  obtain ⟨K,Ct,hK,hbound⟩ := low_localized_stopped_bilinear_log_saving
    hpnt hMV hC hHuxley hM j r a
  refine ⟨2*K*Mh,Ct,by dsimp [Mh]; positivity,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hTH hP hS
  have hZ1 : 1 ≤ Z := by nlinarith
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) Ct).trans_le hT
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
    hR hE hψ hw hrough hv hsize hZ hA hAupper hAcubic hX hT hMh hP hS
    h hhi hhd hder.1 hder.2.1 hder.2.2 hh hhs hh2 hhs2
  have hx2 := hbound R D E U P S ψ w Z A (2*X₀) T Mh v selected remaining
    hR hE hψ hw hrough hv hsize hZ hA hAupper hAcubic (by positivity) hT hMh hP hS
    h hhi hhd hder.1 hder.2.1 hder.2.2 hh hhs hh2 hhs2
  unfold cutoffBilinearWindow
  rw [bilinear_cutoff_window_endpoints P S _ _ H hTp hX]
  exact (norm_sub_le _ _).trans ((add_le_add hx hx2).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
