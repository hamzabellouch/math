import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedCoefficient

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma abs_sub_center {x : ℝ} {A e : ℚ} (hx : x ∈ (⟨A-e,A+e⟩ : Box)) :
    |x-(A:ℝ)| ≤ (e:ℝ) := by
  change ((A-e:ℚ):ℝ) ≤ x ∧ x ≤ ((A+e:ℚ):ℝ) at hx
  rw [Rat.cast_sub,Rat.cast_add] at hx
  exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩

lemma mem_sd_center {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ) {c B : ℚ} (hB : 0 ≤ B)
    (hc : (∫ h, (f h-(c:ℝ))^2 ∂μ) ∈ (⟨0,B^2⟩ : Box)) :
    sd μ f ∈ (⟨0,B⟩ : Box) := by
  have hi := hc.2
  change (∫ h, (f h-(c:ℝ))^2 ∂μ) ≤ ((B^2:ℚ):ℝ) at hi
  rw [Rat.cast_pow] at hi
  exact ⟨by simpa only [Rat.cast_zero] using sd_nonneg (μ := μ) f,
    sd_le_of_center hf (by exact_mod_cast hB) hi⟩

lemma mem_F_of_center {β : ℝ} {A C Q sa sf : ℚ}
    (hβ : 0 ≤ β) (hβh : β ≤ 1/2) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (ha : a β ∈ (⟨A-3/2000,A+3/2000⟩ : Box))
    (hg : G β ∈ (⟨C-3/2000,C+3/2000⟩ : Box))
    (hsa : 0 ≤ sa)
    (hc : (∫ h, (approxF β A C h-(Q:ℝ))^2 ∂fieldLaw β) ∈ (⟨0,sa^2⟩ : Box))
    (harith : sa+9/2000 ≤ sf) : sd (fieldLaw β) (F β) ∈ (⟨0,sf⟩ : Box) := by
  have hbound := approxF_error hβ hβh (A := (A:ℝ)) (C := (C:ℝ))
    (by exact_mod_cast hA) (by exact_mod_cast hA1)
  have hsd := (mem_sd_center (memLp_approxF β A C) hsa hc).2
  change sd (fieldLaw β) (approxF β A C) ≤ (sa:ℝ) at hsd
  have heA := abs_sub_center ha
  have heG := abs_sub_center hg
  have ha' : (sa:ℝ)+9/2000 ≤ (sf:ℝ) := by
    have hh : ((sa+9/2000:ℚ):ℝ) ≤ (sf:ℝ) := Rat.cast_le.mpr harith
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using hh
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at heA heG
  exact ⟨by simpa only [Rat.cast_zero] using sd_nonneg (μ := fieldLaw β) (F β),
    by linarith only [hbound,hsd,heA,heG,ha']⟩

end SKRatio.Certificate

end

end OAI
