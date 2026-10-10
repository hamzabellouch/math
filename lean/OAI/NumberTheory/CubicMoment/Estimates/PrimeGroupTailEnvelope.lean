import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailWide
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailWindow
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailEnvelope

namespace OAI

/-! Full-line Mellin restoration for the enlarged-range height tail. The
original smooth product envelope and every height window remain present. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_envelope_log_saving
    {C Mα Mβ D : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hD : 1 ≤ D) (k dα dβ : ℕ) (Q : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
      (B A T H X : ℝ), B₀ ≤ B → (2*D*B)^(27/25:ℝ) ≤ A →
      A ≤ B^(19/10:ℝ) → (2*D*B)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ B^3 → 0 < X →
      (∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ Q*A) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ B ≤ norm b ∧ norm b ≤ D*B) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log B)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*B*(1+Real.log B)^dβ →
      ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  obtain ⟨K,B₀,hK,hbound⟩ := primeGroupTail_wide_bilinear_log_saving hMV hC hHuxley
    hMα hMβ hD (k+1) dα dβ Q
  obtain ⟨K₀,hK₀,hsum⟩ := height_window_sum_log_saving
  let K₁ := K₀*(2*K)
  refine ⟨(zeroLineMellinMass W+1)*K₁,max B₀ 1,
    by dsimp [K₁]; positivity [zeroLineMellinMass_nonneg W],?_⟩
  intro P S α β B A T H X hB hA hAu hT hH hHB hX hP hS hα hβ
  have hB₁ : 1 ≤ B := (le_max_right _ _).trans hB
  have hBp : 0 < B := zero_lt_one.trans_le hB₁
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by positivity : 0 < 2*D*B) _).trans_le hA
  have hT₁ : 1 ≤ T := (Real.one_le_rpow
    (by nlinarith [mul_le_mul hD hB₁ zero_le_one (zero_le_one.trans hD)] : 1 ≤ 2*D*B)
    (by norm_num : (0:ℝ) ≤ 1/50)).trans hT
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB₁]
  have ht (v : ℝ) :
      ‖cutoffBilinearTail P S (fun a => α a*normTwist v a)
        (fun b => β b*normTwist v b) H T X‖ ≤
        K₁*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    let αv := fun a => α a*normTwist v a
    let βv := fun b => β b*normTwist v b
    have ha : (∑ a ∈ P, ‖αv a‖^2) ≤ Mα*A*(1+Real.log B)^dα := by
      simpa only [αv,norm_mul,norm_normTwist,mul_one] using hα
    have hb : (∑ b ∈ S, ‖βv b‖^2) ≤ Mβ*B*(1+Real.log B)^dβ := by
      simpa only [βv,norm_mul,norm_normTwist,mul_one] using hβ
    have hw (t : ℝ) (htt : T ≤ t) (_htH : t < 2*Real.pi*H) :
        ‖cutoffBilinearWindow P S αv βv H t X‖ ≤
          (2*K)*(A^(5/6:ℝ)*B^(5/6:ℝ))/(1+Real.log B)^(k+1) := by
      have hm := hbound P S αv βv B A t 0 ((le_max_left _ _).trans hB) hA hAu
        (hT.trans htt) hP hS ha hb
      simp only [zero_add] at hm
      exact (primeGroupTail_window_le_mean P S αv βv H X t hX
        (zero_lt_one.trans_le (hT₁.trans htt))).trans
          ((mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring))
    simpa only [cutoffBilinearTail,K₁,mul_assoc] using
      hsum H T B (A^(5/6:ℝ)*B^(5/6:ℝ)) (2*K) k
        (fun t => cutoffBilinearWindow P S αv βv H t X)
        hH hT₁ hB₁ hHB (by positivity) (by positivity) hw
  have hm : 0 ≤ K₁*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
    dsimp [K₁]; positivity
  apply (envelopeCutoffBilinearTail_bound P S α β (fun a ha => (hP a ha).1)
    (fun b hb => (hS b hb).1) W hW hpos hsm H T hX hm ht).trans
  calc
    _ ≤ (zeroLineMellinMass W+1)*(K₁*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k) :=
      mul_le_mul_of_nonneg_right (by linarith) hm
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
