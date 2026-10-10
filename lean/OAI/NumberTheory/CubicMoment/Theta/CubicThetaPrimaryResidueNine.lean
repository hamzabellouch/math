import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedCharacterFourier

namespace OAI

/-! The nine primary residue classes modulo nine, parametrized without
choices of integer coordinates by the residue ring modulo three. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

abbrev CubicThetaPrimaryNine :=
  {x : Residues (9:Eisenstein) // primary (residueRepresentative 9 x)}

private lemma primary_of_nine_congr {a b : Eisenstein} (ha : primary a)
    (hab : (9:Eisenstein) ∣ a-b) : primary b := by
  obtain ⟨k,hk⟩ := ha
  obtain ⟨t,ht⟩ := hab
  exact ⟨k-3*t,by linear_combination hk-ht⟩

def cubicThetaPrimaryNineLift (y : Residues (3:Eisenstein)) : CubicThetaPrimaryNine where
  val := Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y)
  property := by
    apply primary_of_nine_congr (a:=1+3*residueRepresentative 3 y)
      ⟨residueRepresentative 3 y,by ring⟩
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr (residueRepresentative_spec 9
      (Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y))).symm

lemma cubicThetaPrimaryNineLift_injective : Function.Injective cubicThetaPrimaryNineLift := by
  intro x y h
  have he := congrArg Subtype.val h
  change Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 x)=
    Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y) at he
  have hd : (9:Eisenstein) ∣ 3*(residueRepresentative 3 x-residueRepresentative 3 y) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul,map_sub]
    change Ideal.Quotient.mk (modulus (9:Eisenstein)) 3 *
      (Ideal.Quotient.mk (modulus 9) (residueRepresentative 3 x)-
        Ideal.Quotient.mk (modulus 9) (residueRepresentative 3 y))=0
    have hz := congrArg (fun z : Residues (9:Eisenstein) =>
      z-Ideal.Quotient.mk (modulus 9) (1+3*residueRepresentative 3 y)) he
    simp only [map_add,map_mul,map_one] at hz
    linear_combination hz
  have h3 : (3:Eisenstein) ∣ residueRepresentative 3 x-residueRepresentative 3 y := by
    have h9 : (9:Eisenstein)=3*3 := by norm_num
    rw [h9,mul_dvd_mul_iff_left (by norm_num : (3:Eisenstein)≠0)] at hd
    exact hd
  have hr := residue_eq_of_dvd_sub h3
  simpa only [residueRepresentative_spec] using hr

lemma cubicThetaPrimaryNineLift_surjective : Function.Surjective cubicThetaPrimaryNineLift := by
  intro x
  obtain ⟨t,ht⟩ := x.property
  refine ⟨Ideal.Quotient.mk (modulus 3) t,?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (modulus 9)
    (1+3*residueRepresentative 3 (Ideal.Quotient.mk (modulus 3) t))=x.val
  rw [← residueRepresentative_spec 9 x.val]
  apply residue_eq_of_dvd_sub
  have hd : (3:Eisenstein) ∣
      residueRepresentative 3 (Ideal.Quotient.mk (modulus 3) t)-t := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr (residueRepresentative_spec 3 (Ideal.Quotient.mk (modulus 3) t))
  obtain ⟨v,hv⟩ := hd
  exact ⟨v,by linear_combination 3*hv-ht⟩

def cubicThetaPrimaryNineEquiv : Residues (3:Eisenstein) ≃ CubicThetaPrimaryNine :=
  Equiv.ofBijective cubicThetaPrimaryNineLift
    ⟨cubicThetaPrimaryNineLift_injective,cubicThetaPrimaryNineLift_surjective⟩

theorem cubicThetaPrimaryNine_card : Nat.card CubicThetaPrimaryNine=9 := by
  rw [← Nat.card_congr cubicThetaPrimaryNineEquiv,residues_card (by norm_num)]
  apply Nat.cast_injective (R:=ℝ)
  rw [normNat_cast]
  change Complex.normSq (3:ℂ)=(9:ℝ)
  norm_num

end CubicFirstMoment

end

end OAI
