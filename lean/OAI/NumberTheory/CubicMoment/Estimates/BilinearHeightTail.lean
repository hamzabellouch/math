import OAI.NumberTheory.CubicMoment.Estimates.HighCutoffWindow
import OAI.NumberTheory.CubicMoment.Estimates.HeightWindowSum

namespace OAI

/-! Summing all actual stopped bilinear height windows. One extra
logarithmic saving pays for the explicit finite window count. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cutoffBilinearTail (P B : Finset Eisenstein) (α β : Eisenstein → ℂ)
    (H T X₀ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (heightWindowCount H T),
    cutoffBilinearWindow P B α β H (T*(3/2:ℝ)^i) X₀

theorem low_stopped_cutoff_tail
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
      0 < X₀ → (1+Real.log Z)^Ct ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧
        1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖cutoffBilinearTail P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨K,Ct,hK,hbound⟩ := low_stopped_cutoff_window hpnt hMV hC hHuxley hM (j+1) r a
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨K₀*K,Ct,by positivity,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hHZ hP hS
  have hZ1 : 1 ≤ Z := by nlinarith
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hT1 : 1 ≤ T := (one_le_pow₀ (by linarith [Real.log_nonneg hZ1])).trans hT
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H t X₀‖ ≤
        K*(A^(5/6:ℝ)*Z^(5/6:ℝ))/(1+Real.log Z)^(j+1) := by
    simpa only [mul_assoc] using hbound R D E U P S ψ w Z A X₀ t H v selected remaining
      hR hE hψ hw hrough hv hsize hZ hA hAupper hAcubic hX (hT.trans ht)
      (zero_lt_one.trans_le hH) htH.le hP hS
  have hh := hsum H T Z (A^(5/6:ℝ)*Z^(5/6:ℝ)) K j
    (fun t => cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
      (stoppedBeta R D v ψ w selected) H t X₀)
    hH hT1 hZ1 hHZ (by positivity) hK.le hf
  simpa only [cutoffBilinearTail,mul_assoc] using hh

theorem high_stopped_cutoff_tail
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
      Z₀ ≤ Z → 2*Z^(3/2:ℝ) ≤ A → A ≤ Z^(2+γ) → A ≤ Z^3 →
      0 < X₀ → Z^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ Z^3 →
      (∀ e ∈ P, primary e ∧ Squarefree e ∧
        1 ≤ norm e/A ∧ norm e/A ≤ 2) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      ‖cutoffBilinearTail P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H T X₀‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨γ,K,Z₀,hγ,hK,hbound⟩ := high_stopped_cutoff_window hpnt hMV hC hHuxley hM (j+1) r
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  refine ⟨γ,K₀*K,max Z₀ 1,hγ,by positivity,?_⟩
  intro R D E U P S ψ w Z A X₀ T H v selected remaining hR hE hψ hw hrough hv hsize
    hZ hA hAupper hAcubic hX hT hH hHZ hP hS
  have hZ1 : 1 ≤ Z := (le_max_right _ _).trans hZ
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hT1 : 1 ≤ T := (Real.one_le_rpow hZ1 (by norm_num : (0:ℝ) ≤ 1/50)).trans hT
  have hf (t : ℝ) (ht : T ≤ t) (htH : t < 2*Real.pi*H) :
      ‖cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
        (stoppedBeta R D v ψ w selected) H t X₀‖ ≤
        K*(A^(5/6:ℝ)*Z^(5/6:ℝ))/(1+Real.log Z)^(j+1) := by
    simpa only [mul_assoc] using hbound R D E U P S ψ w Z A X₀ t H v selected remaining
      hR hE hψ hw hrough hv hsize ((le_max_left _ _).trans hZ) hA hAupper hAcubic
      hX (hT.trans ht) (zero_lt_one.trans_le hH) htH.le hP hS
  have hh := hsum H T Z (A^(5/6:ℝ)*Z^(5/6:ℝ)) K j
    (fun t => cutoffBilinearWindow P S (stoppedAlpha E U ψ w remaining)
      (stoppedBeta R D v ψ w selected) H t X₀)
    hH hT1 hZ1 hHZ (by positivity) hK.le hf
  simpa only [cutoffBilinearTail,mul_assoc] using hh

end CubicFirstMoment

end

end OAI
