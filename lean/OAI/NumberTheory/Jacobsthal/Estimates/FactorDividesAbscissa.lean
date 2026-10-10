import Mathlib
import OAI.NumberTheory.Jacobsthal.Harmonic.LinearPolynomialForm
import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInverseIncidence
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def bit {α β : Type*} (R : α → β → Prop) (a : α) (p : β) : ℝ := if R a p then 1 else 0
noncomputable def degree {α β : Type*} (P : Finset β) (R : α → β → Prop) (a : α) : ℕ :=
  (P.filter (R a)).card
noncomputable def multiplicity {α β : Type*} (A : Finset α) (R : α → β → Prop) (p : β) : ℝ :=
  ∑ a ∈ A, bit R a p

theorem bit_nonneg {α β : Type*} (R : α → β → Prop) (a : α) (p : β) : 0 ≤ bit R a p := by
  unfold bit
  split_ifs <;> norm_num

theorem sum_bit {α β : Type*} (P : Finset β) (R : α → β → Prop) (a : α) :
    (∑ p ∈ P,bit R a p) = (degree P R a : ℝ) := by
  exact Finset.sum_boole (R a) P

theorem sum_bit_product {α β : Type*} (P : Finset β) (R : α → β → Prop) (a b : α) :
    (∑ p ∈ P,bit R a p*bit R b p) = ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) := by
  have h (p : β) : bit R a p*bit R b p = if R a p ∧ R b p then (1 : ℝ) else 0 := by
    by_cases ha : R a p <;> by_cases hb : R b p <;> simp [bit,ha,hb]
  simp_rw [h]
  exact Finset.sum_boole _ _

theorem multiplicity_sum {α β : Type*} (A : Finset α) (P : Finset β) (R : α → β → Prop) :
    (∑ p ∈ P,multiplicity A R p) = ∑ a ∈ A,(degree P R a : ℝ) := by
  unfold multiplicity
  rw [Finset.sum_comm]
  simp_rw [sum_bit]

theorem multiplicity_square_sum {α β : Type*} (A : Finset α) (P : Finset β) (R : α → β → Prop) :
    (∑ p ∈ P,(multiplicity A R p)^2) =
      ∑ a ∈ A,∑ b ∈ A,((P.filter (fun p => R a p ∧ R b p)).card : ℝ) := by
  have h (p : β) : (multiplicity A R p)^2 = ∑ a ∈ A,∑ b ∈ A,bit R a p*bit R b p := by
    unfold multiplicity
    rw [pow_two,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp_rw [sum_bit_product]

theorem multiplicity_square_upper {α β : Type*} (A : Finset α) (P : Finset β)
    (R : α → β → Prop) {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K) :
    (∑ p ∈ P,(multiplicity A R p)^2) ≤ (A.card : ℝ)*(P.card : ℝ)+K*(A.card : ℝ)^2 := by
  rw [multiplicity_square_sum]
  calc
    _ ≤ ∑ a ∈ A,∑ b ∈ A,((if b=a then (P.card : ℝ) else 0)+K) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      by_cases hab : b=a
      · rw [ite_eq_left hab]
        have hc : ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ P.card := by
          exact_mod_cast Finset.card_filter_le P (fun p => R a p ∧ R b p)
        linarith
      · rw [ite_eq_right hab,zero_add]
        exact hpair a ha b hb (Ne.symm hab)
    _ = _ := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_const,nsmul_eq_mul]
      have he : (∑ a ∈ A,if a ∈ A then (P.card : ℝ) else 0) = (A.card : ℝ)*(P.card : ℝ) := by
        simp
      rw [he]
      ring

theorem dense_incidence_card_bound {α β : Type*} (A : Finset α) (P : Finset β)
    (R : α → β → Prop) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hP : 0 < P.card)
    (hdense : ∀ a ∈ A,c*(P.card : ℝ) ≤ (degree P R a : ℝ))
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ((P.filter (fun p => R a p ∧ R b p)).card : ℝ) ≤ K)
    (hlarge : 2*K ≤ c^2*(P.card : ℝ)) : (A.card : ℝ) ≤ 2/c^2 := by
  let M : ℝ := A.card
  let N : ℝ := P.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hP
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hlow : M*c*N ≤ ∑ p ∈ P,multiplicity A R p := by
    rw [multiplicity_sum]
    calc
      _ = ∑ _a ∈ A,c*N := by simp [M]; ring
      _ ≤ _ := Finset.sum_le_sum hdense
  have hcs : (∑ p ∈ P,multiplicity A R p)^2 ≤ N*(∑ p ∈ P,(multiplicity A R p)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ)) (multiplicity A R)
  have hup := multiplicity_square_upper A P R hK hpair
  have hchain : (M*c*N)^2 ≤ N*(M*N+K*M^2) :=
    (pow_le_pow_left₀ (by positivity) hlow 2).trans
      (hcs.trans (mul_le_mul_of_nonneg_left hup hN.le))
  have hmain : M^2*c^2*N ≤ M*N+K*M^2 := by
    have hscaled : (M^2*c^2*N)*N ≤ (M*N+K*M^2)*N := by
      convert hchain using 1 <;> ring
    exact le_of_mul_le_mul_right hscaled hN
  have hKm : 2*K*M^2 ≤ c^2*N*M^2 := mul_le_mul_of_nonneg_right hlarge (sq_nonneg M)
  have hMN : M^2*c^2 ≤ 2*M := by
    have hscaled : (M^2*c^2)*N ≤ (2*M)*N := by nlinarith only [hmain,hKm]
    exact le_of_mul_le_mul_right hscaled hN
  change M ≤ 2/c^2
  by_cases hm : M=0
  · rw [hm]
    positivity
  · have hMp : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hm)
    apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
    have hscaled : (M*c^2)*M ≤ 2*M := by convert hMN using 1; ring
    exact le_of_mul_le_mul_right hscaled hMp

end ErdosInverseIncidence

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def aligns (a : ℕ → ℤ) (q : ℚ) (p : ℕ) : Prop :=
  (q.den : ZMod p) * (a p : ZMod p) = (q.num : ZMod p)

theorem aligns_iff_modEq (a : ℕ → ℤ) (q : ℚ) (p : ℕ) :
    aligns a q p ↔ Int.ModEq (p : ℤ) ((q.den : ℤ)*a p) q.num := by
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [aligns,Int.cast_mul,Int.cast_natCast]

theorem aligned_prime_not_dvd_den (a : ℕ → ℤ) (q : ℚ) {p : ℕ}
    (hp : p.Prime) (hq : aligns a q p) : ¬p ∣ q.den := by
  intro hd
  have hd0 : (q.den : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hn0 : (q.num : ZMod p) = 0 := by
    change (q.den : ZMod p)*(a p : ZMod p) = (q.num : ZMod p) at hq
    simpa only [hd0,zero_mul] using hq.symm
  have hn : p ∣ q.num.natAbs := Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn0)
  have hg := Nat.dvd_gcd hn hd
  rw [q.reduced.gcd_eq_one] at hg
  exact hp.not_dvd_one hg

def determinant (q r : ℚ) : ℤ := q.num*(r.den : ℤ)-r.num*(q.den : ℤ)

theorem determinant_ne_zero {q r : ℚ} (hqr : q ≠ r) : determinant q r ≠ 0 := by
  intro h
  apply hqr
  apply Rat.eq_iff_mul_eq_mul.mpr
  exact sub_eq_zero.mp h

theorem common_alignment_dvd (a : ℕ → ℤ) (q r : ℚ) (p : ℕ)
    (hq : aligns a q p) (hr : aligns a r p) : (p : ℤ) ∣ determinant q r := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have he : ((determinant q r : ℤ) : ZMod p) =
      (q.num : ZMod p)*(r.den : ZMod p)-(r.num : ZMod p)*(q.den : ZMod p) := by
    simp only [determinant,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
  rw [he,← hq,← hr]
  ring

noncomputable def commonAligners (P : Finset ℕ) (a : ℕ → ℤ) (q r : ℚ) : Finset ℕ :=
  P.filter (fun p => aligns a q p ∧ aligns a r p)

theorem commonAligners_le_divisors (P : Finset ℕ) (a : ℕ → ℤ) {q r : ℚ} (hqr : q ≠ r) :
    (commonAligners P a q r).card ≤ (determinant q r).natAbs.divisors.card := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨_,hq,hr⟩ := Finset.mem_filter.mp hp
  apply Nat.mem_divisors.mpr
  exact ⟨Int.natCast_dvd.mp (common_alignment_dvd a q r p hq hr),
    Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr)⟩

theorem determinant_height (q r : ℚ) (HA HD : ℕ)
    (hqa : q.num.natAbs ≤ HA) (hra : r.num.natAbs ≤ HA)
    (hqd : q.den ≤ HD) (hrd : r.den ≤ HD) :
    (determinant q r).natAbs ≤ 2*HA*HD := by
  calc
    _ ≤ (q.num*(r.den : ℤ)).natAbs+(r.num*(q.den : ℤ)).natAbs := Int.natAbs_sub_le _ _
    _ = q.num.natAbs*r.den+r.num.natAbs*q.den := by
      rw [Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]
    _ ≤ HA*HD+HA*HD := add_le_add (Nat.mul_le_mul hqa hrd) (Nat.mul_le_mul hra hqd)
    _ = _ := by ring

theorem commonAligners_subpower {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (q r : ℚ),
      q ≠ r → q.num.natAbs ≤ HA → r.num.natAbs ≤ HA → q.den ≤ HD → r.den ≤ HD →
      ((commonAligners P a q r).card : ℝ) ≤ B*((2*HA*HD : ℕ) : ℝ)^eps := by
  obtain ⟨B,hB,hdiv⟩ := ErdosDivisorBounds.divisor_subpower heps
  refine ⟨B,hB,?_⟩
  intro P a HA HD q r hqr hqa hra hqd hrd
  have hn : 1 ≤ (determinant q r).natAbs := Nat.one_le_iff_ne_zero.mpr
    (Int.natAbs_ne_zero.mpr (determinant_ne_zero hqr))
  have hh := determinant_height q r HA HD hqa hra hqd hrd
  calc
    _ ≤ ((determinant q r).natAbs.divisors.card : ℝ) := by exact_mod_cast commonAligners_le_divisors P a hqr
    _ ≤ B*((determinant q r).natAbs : ℝ)^eps := hdiv _ hn
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hh) heps.le) hB.le

end ErdosInverseAlignment

end

section

namespace ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

noncomputable def heightCandidates (HA HD : ℕ) : Finset ℚ :=
  (((Finset.Icc (-(HA : ℤ)) (HA : ℤ)).product (Finset.Icc 1 HD)).image
    (fun z : ℤ × ℕ => (z.1 : ℚ)/(z.2 : ℚ))).filter
      (fun q => q.num.natAbs ≤ HA ∧ q.den ≤ HD)

theorem mem_heightCandidates (HA HD : ℕ) (q : ℚ) :
    q ∈ heightCandidates HA HD ↔ q.num.natAbs ≤ HA ∧ q.den ≤ HD := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨ha,hd⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,ha,hd⟩
    apply Finset.mem_image.mpr
    refine ⟨(q.num,q.den),?_,?_⟩
    · apply Finset.mem_product.mpr
      have habs : |q.num| ≤ (HA : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast ha
      exact ⟨Finset.mem_Icc.mpr (abs_le.mp habs),
        Finset.mem_Icc.mpr ⟨q.den_pos,hd⟩⟩
    · exact q.num_div_den

noncomputable def rationalList (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (c : ℝ) : Finset ℚ :=
  (heightCandidates HA HD).filter
    (fun q => c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ))

theorem mem_rationalList (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (c : ℝ) (q : ℚ) :
    q ∈ rationalList P a HA HD c ↔
      q.num.natAbs ≤ HA ∧ q.den ≤ HD ∧
      c*(P.card : ℝ) ≤ ((P.filter (aligns a q)).card : ℝ) := by
  simp only [rationalList,Finset.mem_filter,mem_heightCandidates,and_assoc]

theorem rational_list_card_subpower {eps : ℝ} (heps : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : Finset ℕ) (a : ℕ → ℤ) (HA HD : ℕ) (c : ℝ),
      0 < c → 0 < P.card →
      2*(B*((2*HA*HD : ℕ) : ℝ)^eps) ≤ c^2*(P.card : ℝ) →
      ((rationalList P a HA HD c).card : ℝ) ≤ 2/c^2 := by
  obtain ⟨B,hB,hpair⟩ := commonAligners_subpower heps
  refine ⟨B,hB,?_⟩
  intro P a HA HD c hc hP hlarge
  apply ErdosInverseIncidence.dense_incidence_card_bound
    (rationalList P a HA HD c) P (fun q p => aligns a q p)
    hc (show 0 ≤ B*((2*HA*HD : ℕ) : ℝ)^eps by positivity) hP
  · intro q hq
    exact (mem_rationalList P a HA HD c q).mp hq |>.2.2
  · intro q hq r hr hqr
    obtain ⟨hqa,hqd,_⟩ := (mem_rationalList P a HA HD c q).mp hq
    obtain ⟨hra,hrd,_⟩ := (mem_rationalList P a HA HD c r).mp hr
    exact hpair P a HA HD q r hqr hqa hra hqd hrd
  · exact hlarge

end ErdosInverseAlignment

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry

theorem linear_y_coefficient_ne_zero (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0) :
    F.coeff (Finsupp.single 1 1) ≠ 0 := by
  intro ha
  rw [linear_polynomial_eval F hdeg.le,ha,zero_mul,add_zero] at hp hq
  have hprod : F.coeff (Finsupp.single 0 1)*((p.1 : ℂ)-(q.1 : ℂ)) = 0 := by
    linear_combination hp-hq
  have hdx : (p.1 : ℂ)-(q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx)
  have hb := (mul_eq_zero.mp hprod).resolve_right hdx
  have hc : F.coeff 0 = 0 := by simpa [hb] using hp
  have hF : F = 0 := by rw [linear_polynomial_form F hdeg.le,hc,hb,ha];simp
  rw [hF,MvPolynomial.totalDegree_zero] at hdeg
  contradiction

theorem linear_integer_cross_product (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0)
    (r : ℤ × ℤ) (hr : MvPolynomial.eval ![(r.1 : ℂ),(r.2 : ℂ)] F = 0) :
    (q.1-p.1)*(r.2-p.2) = (q.2-p.2)*(r.1-p.1) := by
  have ha := linear_y_coefficient_ne_zero F hdeg p q hx hp hq
  rw [linear_polynomial_eval F hdeg.le] at hp hq hr
  have he : ((q.1 : ℂ)-(p.1 : ℂ))*((r.2 : ℂ)-(p.2 : ℂ)) =
      ((q.2 : ℂ)-(p.2 : ℂ))*((r.1 : ℂ)-(p.1 : ℂ)) := by
    apply mul_left_cancel₀ ha
    linear_combination ((q.1 : ℂ)-(p.1 : ℂ))*(hr-hp)-
      ((r.1 : ℂ)-(p.1 : ℂ))*(hq-hp)
  exact_mod_cast he

end ErdosRichLine

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry

structure PrimitiveIntegerLine where
  denominator : ℕ
  slope : ℤ
  intercept : ℤ
  denominator_pos : 0 < denominator
  reduced : Nat.Coprime slope.natAbs denominator

def PrimitiveIntegerLine.Contains (l : PrimitiveIntegerLine) (p : ℤ × ℤ) : Prop :=
  (l.denominator : ℤ)*p.2 = l.slope*p.1+l.intercept

theorem primitive_line_from_cross_products (p q : ℤ × ℤ) (hx : p.1 ≠ q.1) :
    ∃ l : PrimitiveIntegerLine, ∀ r : ℤ × ℤ,
      (q.1-p.1)*(r.2-p.2) = (q.2-p.2)*(r.1-p.1) → l.Contains r := by
  let s : ℚ := ((q.2-p.2 : ℤ) : ℚ)/((q.1-p.1 : ℤ) : ℚ)
  let l : PrimitiveIntegerLine :=
    ⟨s.den,s.num,(s.den : ℤ)*p.2-s.num*p.1,s.den_pos,s.reduced⟩
  have hdx : q.1-p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hdxQ : ((q.1-p.1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hdx
  have hdQ : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hratio : (s.num : ℚ)/(s.den : ℚ) = ((q.2-p.2 : ℤ) : ℚ)/((q.1-p.1 : ℤ) : ℚ) :=
    s.num_div_den
  have hmulQ := (div_eq_div_iff hdQ hdxQ).mp hratio
  have hmul : s.num*(q.1-p.1) = (q.2-p.2)*(s.den : ℤ) := by exact_mod_cast hmulQ
  refine ⟨l,?_⟩
  intro r hr
  change (s.den : ℤ)*r.2 = s.num*r.1+((s.den : ℤ)*p.2-s.num*p.1)
  apply mul_left_cancel₀ hdx
  linear_combination (s.den : ℤ)*hr-(r.1-p.1)*hmul

theorem primitive_line_of_polynomial (F : MV ℂ) (hdeg : F.totalDegree = 1)
    (p q : ℤ × ℤ) (hx : p.1 ≠ q.1)
    (hp : MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0)
    (hq : MvPolynomial.eval ![(q.1 : ℂ),(q.2 : ℂ)] F = 0) :
    ∃ l : PrimitiveIntegerLine, ∀ r : ℤ × ℤ,
      MvPolynomial.eval ![(r.1 : ℂ),(r.2 : ℂ)] F = 0 → l.Contains r := by
  obtain ⟨l,hl⟩ := primitive_line_from_cross_products p q hx
  exact ⟨l,fun r hr => hl r (linear_integer_cross_product F hdeg p q hx hp hq r hr)⟩

end ErdosRichLine

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine

structure InterceptReduction (l : PrimitiveIntegerLine) where
  rational : ℚ
  factor : ℕ
  factor_pos : 0 < factor
  denominator_eq : l.denominator = factor*rational.den
  intercept_eq : l.intercept = (factor : ℤ)*rational.num

theorem exists_intercept_reduction (l : PrimitiveIntegerLine) : Nonempty (InterceptReduction l) := by
  let g : ℕ := Int.gcd l.intercept (l.denominator : ℤ)
  have hd : (0 : ℤ) < l.denominator := by exact_mod_cast l.denominator_pos
  have hg : 0 < g := Int.gcd_pos_of_ne_zero_right _ (ne_of_gt hd)
  obtain ⟨A,D,hcop,hA,hD⟩ := Int.exists_gcd_one hg
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg
  have hDpos : 0 < D := by nlinarith
  have hDt : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hDpos.le
  have hDn : 0 < D.toNat := by omega
  have hred : Nat.Coprime A.natAbs D.toNat := by
    have hh : Int.gcd A (D.toNat : ℤ) = 1 := by rwa [hDt]
    simpa only [Int.gcd_def,Int.natAbs_natCast,Nat.Coprime] using hh
  let r : ℚ := Rat.mk' A D.toNat hDn.ne' hred
  have hden : l.denominator = g*r.den := by
    change l.denominator = g*D.toNat
    have hh : (l.denominator : ℤ) = (g : ℤ)*(D.toNat : ℤ) := by rw [hDt];nlinarith [hD]
    exact_mod_cast hh
  have hint : l.intercept = (g : ℤ)*r.num := by
    change l.intercept = (g : ℤ)*A
    nlinarith [hA]
  exact ⟨⟨r,g,hg,hden,hint⟩⟩

theorem InterceptReduction.rational_value {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.rational = (l.intercept : ℚ)/(l.denominator : ℚ) := by
  rw [r.intercept_eq,r.denominator_eq,Int.cast_mul,Nat.cast_mul]
  have hg : (r.factor : ℚ) ≠ 0 := by exact_mod_cast r.factor_pos.ne'
  change r.rational = (r.factor : ℚ)*(r.rational.num : ℚ)/((r.factor : ℚ)*(r.rational.den : ℚ))
  rw [mul_div_mul_left _ _ hg]
  exact r.rational.num_div_den.symm

end ErdosPrimitiveIntercept

end

section

namespace ErdosRichLine
open ErdosCriticalGeometry ErdosComplexCurveFactors

theorem exists_rich_primitive_line (P : MV ℂ) (hP : P ≠ 0) (D : ℕ) (hD : P.totalDegree ≤ D)
    (S : ℝ) (hS : 0 ≤ S) (X : Finset (ℤ × ℤ)) (hX : X ⊆ complexSquarePoints P S)
    (hinj : Set.InjOn Prod.fst (X : Set (ℤ × ℤ))) (M : ℝ) (hM : 1 ≤ M)
    (hlarge : 182*(D : ℝ)^4*(1+S^((2 : ℝ)/3))+(D : ℝ)*M < (X.card : ℝ)) :
    ∃ (F : MV ℂ) (l : PrimitiveIntegerLine),
      Irreducible F ∧ F ∣ P ∧ F.totalDegree = 1 ∧
      M < ((X ∩ complexSquarePoints F S).card : ℝ) ∧
      ∀ r ∈ X ∩ complexSquarePoints F S, l.Contains r := by
  classical
  obtain ⟨F,hF,hFP,hdeg,hcount⟩ := exists_rich_linear_factor P hP D hD S hS X hX M
    (le_trans zero_le_one hM) hlarge
  have htwo : 1 < (X ∩ complexSquarePoints F S).card := by exact_mod_cast lt_of_le_of_lt hM hcount
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp htwo
  have hx : p.1 ≠ q.1 := fun he => hpq (hinj (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1 he)
  have hpz := ((mem_complexSquarePoints F S p).mp (Finset.mem_inter.mp hp).2).2
  have hqz := ((mem_complexSquarePoints F S q).mp (Finset.mem_inter.mp hq).2).2
  obtain ⟨l,hl⟩ := primitive_line_of_polynomial F hdeg p q hx hpz hqz
  refine ⟨F,l,hF,hFP,hdeg,hcount,?_⟩
  intro r hr
  exact hl r (((mem_complexSquarePoints F S r).mp (Finset.mem_inter.mp hr).2).2)

end ErdosRichLine

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine

theorem InterceptReduction.factor_dvd_denominator {l : PrimitiveIntegerLine} (r : InterceptReduction l) :
    r.factor ∣ l.denominator := ⟨r.rational.den,r.denominator_eq⟩

theorem InterceptReduction.factor_dvd_abscissa {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (p : ℤ × ℤ) (hp : l.Contains p) : (r.factor : ℤ) ∣ p.1 := by
  have hd : (r.factor : ℤ) ∣ (l.denominator : ℤ) := by exact_mod_cast r.factor_dvd_denominator
  have hb : (r.factor : ℤ) ∣ l.intercept := ⟨r.rational.num,r.intercept_eq⟩
  have hax : (r.factor : ℤ) ∣ l.slope*p.1 := by
    have hh := dvd_sub (dvd_mul_of_dvd_left hd p.2) hb
    have he : (l.denominator : ℤ)*p.2-l.intercept = l.slope*p.1 := by
      unfold PrimitiveIntegerLine.Contains at hp
      linarith
    rwa [he] at hh
  have hcop : Nat.Coprime r.factor l.slope.natAbs :=
    l.reduced.symm.of_dvd_left r.factor_dvd_denominator
  have hg : Int.gcd (r.factor : ℤ) l.slope = 1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using hcop.gcd_eq_one
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hax hg

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI
