import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGCD
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcRational
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterFourier

namespace OAI

/-! Resolving a rational phase on each gcd stratum. The coefficients are
finite unit-group Fourier coefficients, so their total mass is controlled
by the square root of the reduced modulus. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma major_arc_rational_val (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    additiveCharacter ((r:ℝ)/q) (n:ZMod q).val = additiveCharacter ((r:ℝ)/q) n := by
  rw [major_arc_rational_character,major_arc_rational_character]
  simp

lemma major_arc_character_inversion_nat (q : ℕ) [NeZero q] (r : ℤ) (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ*naturalCharacter χ n) =
      if IsUnit (n:ZMod q) then additiveCharacter ((r:ℝ)/q) n else 0 := by
  rw [show (∑ χ : DirichletCharacter ℂ q,
      mrtAdditiveCharacterCoefficient q r χ*naturalCharacter χ n) =
    ∑ χ : DirichletCharacter ℂ q, mrtAdditiveCharacterCoefficient q r χ*χ (n:ZMod q) by rfl]
  rw [mrt_additive_character_inversion,major_arc_rational_val]

lemma major_arc_divisor_quotient_pos {q : ℕ} (hq : 0 < q)
    (d : {d : ℕ // d ∈ q.divisors}) : 0 < q/d.val := by
  have hdq := (Nat.mem_divisors.mp d.property).1
  exact Nat.div_pos (Nat.le_of_dvd hq hdq) (Nat.pos_of_dvd_of_pos hdq hq)

noncomputable def majorArcDivisorTerm {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (n : ℕ) : ℂ := by
  letI : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  exact F d.val * ∑ χ : DirichletCharacter ℂ (q/d.val),
    mrtAdditiveCharacterCoefficient (q/d.val) r χ *
      dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ)) n

lemma major_arc_divisor_term {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (d : {d : ℕ // d ∈ q.divisors})
    (havoid : mrtPrimeAvoids (J.biUnion P) d.val) (n : ℕ) (hn : 0 < n) :
    majorArcDivisorTerm J P F q hq r d n =
      if n.gcd q=d.val then
        mrtTypicalCoefficient J P F n*additiveCharacter ((r:ℝ)/q) n else 0 := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  have hdq := (Nat.mem_divisors.mp d.property).1
  have hd : 0 < d.val := Nat.pos_of_dvd_of_pos hdq hq
  have he : majorArcDivisorTerm J P F q hq r d n =
      mrtTypicalCoefficient J P F n *
        ∑ χ : DirichletCharacter ℂ (q/d.val),
          mrtAdditiveCharacterCoefficient (q/d.val) r χ*dilate d.val (naturalCharacter χ) n := by
    unfold majorArcDivisorTerm
    rw [mul_sum,mul_sum]
    apply sum_congr rfl
    intro χ _
    have hh := major_arc_typical_dilation J P hP F hF hd havoid χ hn
    calc
      _ = mrtAdditiveCharacterCoefficient (q/d.val) r χ *
          (F d.val*dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ)) n) := by ring
      _ = _ := by rw [←hh]; ring
  rw [he]
  by_cases hdn : d.val∣n
  · simp only [dilate,hdn,ite_true]
    rw [major_arc_character_inversion_nat]
    by_cases hu : IsUnit ((n/d.val:ℕ):ZMod (q/d.val))
    · have hg := (major_arc_reduced_unit_iff q d.val n hq hdq hdn).mp hu
      rw [ite_eq_left hu,ite_eq_left hg]
      have hp := major_arc_gcd_phase q n hq r
      rw [hg] at hp
      rw [hp]
    · have hg : n.gcd q≠d.val := fun h => hu
        ((major_arc_reduced_unit_iff q d.val n hq hdq hdn).mpr h)
      rw [ite_eq_right hu,ite_eq_right hg,mul_zero]
  · simp only [dilate,hdn,ite_false,mul_zero,sum_const_zero]
    have hg : n.gcd q≠d.val := by
      intro hg
      exact hdn (hg ▸ Nat.gcd_dvd_left n q)
    rw [ite_eq_right hg]

theorem major_arc_divisor_expansion {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hF : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b)
    (q : ℕ) (hq : 0 < q) (r : ℤ)
    (havoid : ∀ d ∈ q.divisors, mrtPrimeAvoids (J.biUnion P) d)
    (n : ℕ) (hn : 0 < n) :
    mrtTypicalCoefficient J P F n*additiveCharacter ((r:ℝ)/q) n =
      ∑ d : {d : ℕ // d ∈ q.divisors}, majorArcDivisorTerm J P F q hq r d n := by
  simp_rw [major_arc_divisor_term J P hP F hF q hq r _ (havoid _ (Subtype.property _)) n hn]
  let dg : {d : ℕ // d ∈ q.divisors} := ⟨n.gcd q,Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q,hq.ne'⟩⟩
  rw [sum_eq_single dg]
  · simp [dg]
  · intro d _ hd
    have hg : n.gcd q≠d.val := by
      intro hg
      apply hd
      exact Subtype.ext hg.symm
    rw [ite_eq_right hg]
  · simp

end TwoPointCorrelations

end OAI
