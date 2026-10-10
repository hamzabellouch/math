import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryNineSum

namespace OAI

/-! Orthogonality on the primary coset in the exact codifferent pairing. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourier_nine_triple (h t : Eisenstein) :
    residueFourierChar 9 (by norm_num)
      (Ideal.Quotient.mk (modulus 9) (3*h*t))=
    residueFourierChar 3 (by norm_num)
      (Ideal.Quotient.mk (modulus 3) (h*t)) := by
  rw [residueFourierChar_mk,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  change (3:ℂ)*(h:ℂ)*(t:ℂ)*(1/(9*traceLambda))=
    ((h:ℂ)*(t:ℂ))*(1/(3*traceLambda))
  field_simp [traceLambda_ne_zero]
  ring

lemma cubicThetaPrimaryNineLift_fourier (h : Eisenstein) (y : Residues (3:Eisenstein)) :
    residueFourierChar 9 (by norm_num)
      (Ideal.Quotient.mk (modulus 9) h*(cubicThetaPrimaryNineLift y).val)=
    residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h)*
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h*y) := by
  change residueFourierChar 9 _
    (Ideal.Quotient.mk (modulus 9) h*
      Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y))=_
  rw [← map_mul,show h*(1+3*residueRepresentative 3 y)=
    h+3*h*residueRepresentative 3 y by ring,map_add,AddChar.map_add_eq_mul,
    cubicThetaFourier_nine_triple,map_mul,residueRepresentative_spec]

theorem cubicThetaPrimaryNine_fourier (h : Eisenstein) :
    (∑' x : Residues (9:Eisenstein),
      if primary (residueRepresentative 9 x) then
        residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h*x) else 0)=
    if (3:Eisenstein) ∣ h then
      9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) h) else 0 := by
  classical
  rw [cubicThetaPrimaryNine_sum]
  simp_rw [cubicThetaPrimaryNineLift_fourier]
  rw [tsum_mul_left]
  let : Finite (Residues (3:Eisenstein)) := finite_residues (by norm_num)
  let : Fintype (Residues (3:Eisenstein)) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hs := AddChar.sum_mulShift (Ideal.Quotient.mk (modulus (3:Eisenstein)) h)
    (residueFourierChar_isPrimitive 3 (by norm_num))
  have hs' : (∑ x : Residues (3:Eisenstein),
      residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h*x))=
      if Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 then
        (Fintype.card (Residues (3:Eisenstein)):ℂ) else 0 := by
    by_cases hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0
    · simpa only [hz,ite_true,mul_comm] using hs
    · simpa only [hz,ite_false,Nat.cast_zero,mul_comm] using hs
  rw [hs']
  have hz : Ideal.Quotient.mk (modulus (3:Eisenstein)) h=0 ↔ (3:Eisenstein) ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton
  have hc : (Fintype.card (Residues (3:Eisenstein)):ℂ)=9 := by
    rw [← Nat.card_eq_fintype_card,residues_card (by norm_num)]
    have hn : normNat (3:Eisenstein)=9 := by
      apply Nat.cast_injective (R:=ℝ)
      rw [normNat_cast]
      change Complex.normSq (3:ℂ)=(9:ℝ)
      norm_num
    rw [hn]
    norm_num
  rw [hz,hc]
  split_ifs <;> ring

end CubicFirstMoment

end

end OAI
