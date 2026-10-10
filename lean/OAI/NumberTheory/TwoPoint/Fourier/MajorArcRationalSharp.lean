import OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisors
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisorBounds

namespace OAI

/-! Rational short sums with the square-root character loss. The
reciprocal gcd volume is retained before summing the strata. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def majorArcDivisorWindow {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (v H : ℕ) : ℂ := by
  letI : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  exact F d.val * ∑ χ : DirichletCharacter ℂ (q/d.val),
    mrtAdditiveCharacterCoefficient (q/d.val) r χ *
      shortExponentialSum (dilationSequence d.val (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v

lemma major_arc_divisor_window {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (r : ℤ)
    (d : {d : ℕ // d ∈ q.divisors}) (v H : ℕ) :
    (∑ n ∈ Icc (v+1) (v+H), majorArcDivisorTerm J P F q hq r d n) =
      majorArcDivisorWindow J P F q hq r d v H := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  unfold majorArcDivisorTerm majorArcDivisorWindow
  rw [←mul_sum,sum_comm]
  congr 1
  apply sum_congr rfl
  intro χ _
  rw [shortExponentialSum_at_nat]
  simp [additiveCharacter,mul_sum]

lemma major_arc_divisor_window_average {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (d : {d : ℕ // d ∈ q.divisors}) (X H : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hshort : ∀ χ : DirichletCharacter ℂ (q/d.val),
      (d.val:ℝ)*shortExponentialIntegral (mrtTypicalCoefficient J P (twistByCharacter F χ))
        (X/d.val+1) (H/d.val+1) 0  ≤  A/(d.val:ℝ)) :
    (∑ v ∈ range X, ‖majorArcDivisorWindow J P F q hq r d v H‖)  ≤
      Real.sqrt ((q/d.val:ℕ):ℝ)*(A/(d.val:ℝ)+X) := by
  let : NeZero (q/d.val) := ⟨(major_arc_divisor_quotient_pos hq d).ne'⟩
  have hd : 0 < d.val := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 hq
  have hb : ∀ v : ℕ, ‖majorArcDivisorWindow J P F q hq r d v H‖  ≤
      ∑ χ : DirichletCharacter ℂ (q/d.val), ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
        ‖shortExponentialSum (dilationSequence d.val
          (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := by
    intro v
    unfold majorArcDivisorWindow
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (hF d.val hd)).trans
    exact (norm_sum_le _ _).trans_eq (sum_congr rfl (fun χ _ => norm_mul _ _))
  calc
    _  ≤  ∑ v ∈ range X, ∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
          ‖shortExponentialSum (dilationSequence d.val
            (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖ := sum_le_sum (fun v _ => hb v)
    _ = ∑ χ : DirichletCharacter ℂ (q/d.val), ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*
        (∑ v ∈ range X, ‖shortExponentialSum (dilationSequence d.val
          (mrtTypicalCoefficient J P (twistByCharacter F χ))) H 0 v‖) := by
      rw [sum_comm]
      simp only [mul_sum]
    _  ≤  ∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖*(A/(d.val:ℝ)+X) := by
      apply sum_le_sum
      intro χ _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (major_arc_dilation_average _
        (mrtTypicalCoefficient_oneBounded J P _ (hF.twistByCharacter χ)) d.val X H hd).trans
          (add_le_add (hshort χ) le_rfl)
    _ = (∑ χ : DirichletCharacter ℂ (q/d.val),
        ‖mrtAdditiveCharacterCoefficient (q/d.val) r χ‖)*(A/(d.val:ℝ)+X) := (sum_mul _ _ _).symm
    _  ≤  _ := mul_le_mul_of_nonneg_right (mrt_additive_character_l1 (q/d.val) r) (by positivity)

theorem major_arc_typical_rational_sharp {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (F : ℕ → ℂ) (hFm : ∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) (hF : OneBounded F)
    (q : ℕ) (hq : 0 < q) (r : ℤ) (X H : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (havoid : ∀ d ∈ q.divisors, mrtPrimeAvoids (J.biUnion P) d)
    (hshort : ∀ d : {d : ℕ // d ∈ q.divisors}, ∀ χ : DirichletCharacter ℂ (q/d.val),
      (d.val:ℝ)*shortExponentialIntegral (mrtTypicalCoefficient J P (twistByCharacter F χ))
        (X/d.val+1) (H/d.val+1) 0  ≤  A/(d.val:ℝ)) :
    shortExponentialIntegral (mrtTypicalCoefficient J P F) X H ((r:ℝ)/q)  ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*A+(q:ℝ)*X) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hw (v : ℕ) : shortExponentialSum (mrtTypicalCoefficient J P F) H ((r:ℝ)/q) v =
      ∑ d : {d : ℕ // d ∈ q.divisors}, majorArcDivisorWindow J P F q hq r d v H := by
    rw [shortExponentialSum_at_nat]
    have he (n : ℕ) (hn : n ∈ Icc (v+1) (v+H)) :=
      major_arc_divisor_expansion J P hP F hFm q hq r havoid n
        (show 0 < n by have := (mem_Icc.mp hn).1; omega)
    calc
      _ = ∑ n∈Icc (v+1) (v+H), ∑ d : {d : ℕ // d∈q.divisors},
          majorArcDivisorTerm J P F q hq r d n := sum_congr rfl he
      _ = ∑ d : {d : ℕ // d∈q.divisors}, ∑ n∈Icc (v+1) (v+H),
          majorArcDivisorTerm J P F q hq r d n := sum_comm
      _ = _ := sum_congr rfl (fun d _ => major_arc_divisor_window J P F q hq r d v H)
  rw [shortExponentialIntegral_eq_sum]
  calc
    _  ≤  ∑ v ∈ range X, ∑ d : {d : ℕ // d ∈ q.divisors}, ‖majorArcDivisorWindow J P F q hq r d v H‖ := by
      apply sum_le_sum
      intro v _
      rw [hw]
      exact norm_sum_le _ _
    _ = ∑ d : {d : ℕ // d ∈ q.divisors}, ∑ v ∈ range X, ‖majorArcDivisorWindow J P F q hq r d v H‖ := sum_comm
    _  ≤  ∑ d : {d : ℕ // d ∈ q.divisors}, Real.sqrt ((q/d.val:ℕ):ℝ)*(A/(d.val:ℝ)+X) :=
      sum_le_sum (fun d _ => major_arc_divisor_window_average J P F hF q hq r d X H A hA (hshort d))
    _ = ∑ d ∈ q.divisors, Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+X) := by
      exact Finset.sum_coe_sort q.divisors (fun d : ℕ => Real.sqrt ((q/d:ℕ):ℝ)*(A/(d:ℝ)+(X:ℝ)))
    _  ≤  _ := major_arc_divisor_weighted q hq A X hA (Nat.cast_nonneg X)

end TwoPointCorrelations

end OAI
