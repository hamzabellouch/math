import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedMomentsJ0
import OAI.Probability.SKRatio.Certificates.CertifiedMomentsJ1
import OAI.Probability.SKRatio.Certificates.CertifiedMomentsJ2
import OAI.Probability.SKRatio.Certificates.CertifiedMomentsJ3
import OAI.Probability.SKRatio.Certificates.CertifiedMomentsJ4
import OAI.Probability.SKRatio.Certificates.CertifiedEndpoints

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma uniform_slacks {β : ℝ} (hβ : 7/20 ≤ β) (hβh : β ≤ 1/2) :
    511/1000 ≤ U₀ β ∧ 425/1000 ≤ U₁ β ∧
      sd (fieldLaw β) (F β) ≤ 925/1000 := by
  by_cases h1 : β ≤ 2/5
  · apply certified_slacks (j := 7/20) (z := 2/5) (t := 27/25) (X := X0) (Y := X1)
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using hβ
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h1
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid0
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid1
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density0
    · exact check0
  by_cases h2 : β ≤ 89/200
  · apply certified_slacks (j := 2/5) (z := 89/200) (t := 1067/1000) (X := X1) (Y := X2)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h2
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid1
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid2
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density1
    · exact check1
  by_cases h3 : β ≤ 19/40
  · apply certified_slacks (j := 89/200) (z := 19/40) (t := 521/500) (X := X2) (Y := X3)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using h3
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid2
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid3
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using density2
    · exact check2
  · apply certified_slacks (j := 19/40) (z := 1/2) (t := 517/500) (X := X3) (Y := X4)
    · norm_num
    · simp only [Rat.cast_div,Rat.cast_ofNat]; linarith
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using hβh
    · norm_num
    · simpa only [Rat.cast_div,Rat.cast_ofNat] using valid3
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using valid4
    · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using density3
    · exact check3

theorem variational_bound {β : ℝ} (hβ : 7/20 ≤ β) (hβh : β ≤ 1/2)
    {b r : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) (hr : MemLp r 2 (fieldLaw β))
    (hnorm : (∫ h, b h^2+r h^2 ∂fieldLaw β) = 1) :
    variational β b r ≤ 9969/10000 := by
  obtain ⟨h0,h1,hs⟩ := uniform_slacks hβ hβh
  obtain ⟨hU,hdisc⟩ := discriminant_of_slacks h0 h1 hs
  have he := variational_bound_of_two_estimates β (9789/10000) (18/1000)
    (by norm_num) (diagonal_envelope (by linarith) hβh)
    (fun b hb => coherent_bound_of_slacks (by linarith) hU hdisc hb) hb hr hnorm
  convert! he using 1; norm_num

end SKRatio.Certificate

end

end OAI
