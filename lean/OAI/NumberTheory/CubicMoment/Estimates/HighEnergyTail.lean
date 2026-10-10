import OAI.NumberTheory.CubicMoment.Estimates.LocalizedLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointProfile
import OAI.NumberTheory.CubicMoment.Estimates.BilinearHeightTail
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope

namespace OAI

/-! Upper-height tails with arbitrary coefficient energies. The power-width
range comes from the published-input localized estimate. Full-line Mellin
restoration retains the actual product envelope. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem high_energy_cutoff_tail
    {C Mα Mβ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (n dα dβ : ℕ) :
    ∃ γ K Z₀ : ℝ, 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X₀ T H : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^(2+γ) → 0 < X₀ →
      Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖cutoffBilinearTail P S α β H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨Kh,hKh,hsecond⟩ := localizedEndpointWeight_second_uniform
  let Mh := 1+Kh
  have hMh : 0 ≤ Mh := by dsimp [Mh]; positivity
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := localized_integral_log_saving hMV hC hHuxley
    hMα hMβ (n+1) dα dβ
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨γ,K₀*(2*K*Mh),max Z₀ 1,hγ,by dsimp [Mh]; positivity,?_⟩
  intro P S α β Z A X₀ T H hZ hA hAu hX hT hH hHZ hP hS hea heb
  have hZ1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hT1 : 1 ≤ T := (Real.one_le_rpow hZ1 (by norm_num : (0:ℝ) ≤ 1/50)).trans hT
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖cutoffBilinearWindow P S α β H t X₀‖ ≤
        (2*K*Mh)*(A^(5/6:ℝ)*Z^(5/6:ℝ))/(1+Real.log Z)^(n+1) := by
    have htp : 0 < t := zero_lt_one.trans_le (hT1.trans ht)
    let w := localizedEndpointWeight H t
    have hi : Integrable w := localizedEndpointWeight_integrable H htp
    have hd : Differentiable ℝ w := (localizedEndpointWeight_smooth H htp).differentiable (by simp)
    have hder := localizedEndpointWeight_derivatives H htp
    have hw (u : ℝ) : ‖w u‖ ≤ Mh := (localizedEndpointWeight_norm_le H htp u).trans
      (by dsimp [Mh]; linarith)
    have hz (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : w u = 0 :=
      localizedEndpointWeight_zero H htp u hu
    have hw2 (u : ℝ) : ‖(t:ℂ)^2*deriv (deriv w) u‖ ≤ Mh :=
      (hsecond H t (zero_lt_one.trans_le hH) htp htH.le u).trans
        (by dsimp [Mh]; linarith)
    have hz2 (u : ℝ) (hu : u ∉ dyadicHeightSupport t) : deriv (deriv w) u = 0 :=
      localizedEndpointWeight_second_zero H htp u hu
    have hb := hbound P S α β Z A X₀ t Mh ((le_max_left _ _).trans hZ) hA hAu hX (hT.trans ht) hMh
      hP hS hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    have hb2 := hbound P S α β Z A (2*X₀) t Mh ((le_max_left _ _).trans hZ) hA hAu (by positivity)
      (hT.trans ht) hMh hP hS hea heb w hi hd hder.1 hder.2.1 hder.2.2 hw hz hw2 hz2
    unfold cutoffBilinearWindow
    rw [bilinear_cutoff_window_endpoints P S α β H htp hX]
    exact (norm_sub_le _ _).trans ((add_le_add hb hb2).trans_eq (by ring))
  have hb := hsum H T Z (A^(5/6:ℝ)*Z^(5/6:ℝ)) (2*K*Mh) n
    (fun t => cutoffBilinearWindow P S α β H t X₀) hH hT1 hZ1 hHZ
    (by positivity) (by positivity) hf
  simpa only [cutoffBilinearTail,mul_assoc] using hb

theorem high_energy_envelope_cutoff_tail
    {C Mα Mβ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (n dα dβ : ℕ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W) :
    ∃ γ K Z₀ : ℝ, 0 < γ ∧ 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X T H : ℝ),
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → 0 < X →
      Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ b ∈ P, primary b ∧ 1 ≤ norm b/A ∧ norm b/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ b ∈ P, ‖α b‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := high_energy_cutoff_tail hMV hC hHuxley
    hMα hMβ n dα dβ
  have hmass := zeroLineMellinMass_nonneg W
  refine ⟨γ,(zeroLineMellinMass W+1)*K,max Z₀ 1,hγ,by positivity,?_⟩
  intro P S α β Z A X T H hZ hA hAu hX hT hH hHZ hP hS hea heb
  have hZ1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hZp : 0 < Z := zero_lt_one.trans_le hZ1
  have hAp : 0 < A := (by positivity : 0 < 2*Z^(3/2:ℝ)).trans_le hA
  have hM : 0 ≤ K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n := by
    have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
    positivity
  have hb := envelopeCutoffBilinearTail_bound P S α β
    (fun b hb => (hP b hb).1) (fun b hb => (hS b hb).1)
    W hW hpos hsm H T hX hM (fun u => by
      apply hbound P S (fun b => α b*normTwist u b)
        (fun b => β b*normTwist u b) Z A X T H ((le_max_left _ _).trans hZ) hA hAu hX hT hH hHZ hP hS
      · simpa only [norm_mul,norm_normTwist,mul_one] using hea
      · simpa only [norm_mul,norm_normTwist,mul_one] using heb)
  calc
    _ ≤ zeroLineMellinMass W*(K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n) := hb
    _ ≤ (zeroLineMellinMass W+1)*(K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^n) :=
      mul_le_mul_of_nonneg_right (by linarith) hM
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
