import Mathlib
import OAI.NumberTheory.CubicGram.Reciprocity

namespace OAI

/-! Prime, squarefree and mixed frequency Gauss evaluation. -/

section
noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def frequencyGauss (b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    cubicSymbol b (residueRepresentative b v) *
      additivePhase b (h * residueRepresentative b v)

lemma frequencyGauss_prime {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    frequencyGauss p h = star (cubicSymbol p h) * gauss p := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let χ := cubicResidueChar p hp
  let ψ := residueAddChar p hp.2.ne_zero
  let hbar := Ideal.Quotient.mk (modulus p) h
  have hsum : frequencyGauss p h = (Real.sqrt (norm p) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift hbar) := by
    unfold frequencyGauss gaussSum
    rw [tsum_fintype]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [cubicSymbol_prime hp]
    change cubicSymbolAtPrime p (residueRepresentative p v) * _ =
      cubicSymbolAtPrime p (residueRepresentative p v) * _
    congr 1
    rw [AddChar.mulShift_apply]
    change additivePhase p (h * residueRepresentative p v) =
      residueAddChar p hp.2.ne_zero (hbar * v)
    have hvbar : hbar * v = Ideal.Quotient.mk (modulus p)
        (h * residueRepresentative p v) := by
      rw [map_mul, residueRepresentative_spec]
    rw [hvbar, residueAddChar_mk]
  have hc : χ hbar = cubicSymbol p h := by
    rw [cubicSymbol_prime hp]
    exact cubicResidueChar_mk p hp h
  have hgp : gauss p = (Real.sqrt (norm p) : ℂ)⁻¹ * gaussSum χ ψ := by
    rw [gauss_prime hp, gaussAtPrime_eq_gaussSum hp]
  rw [hsum, hgp, ← hc]
  by_cases hh : hbar = 0
  · have hzero : χ (0 : Residues p) = 0 := MulChar.map_zero χ
    rw [hh, AddChar.mulShift_zero,
      gaussSum_one_right (show χ ≠ 1 from cubicResidueChar_ne_one hp),
      hzero, star_zero, zero_mul, mul_zero]
  · let u : (Residues p)ˣ := Units.mk0 hbar hh
    change (Real.sqrt (norm p) : ℂ)⁻¹ * gaussSum χ (ψ.mulShift (u : Residues p)) = _
    rw [gaussSum_mulShift_eq]
    rw [← MulChar.star_apply']
    dsimp only [u, Units.val_mk0]
    ring

lemma frequencyGauss_mul_of_isCoprime {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hab : IsCoprime a b) (h : Eisenstein) :
    frequencyGauss (a*b) h = frequencyGauss a h * frequencyGauss b h *
      (cubicSymbol a b * cubicSymbol b a) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (d : Eisenstein) (x : Residues d) : ℂ :=
    cubicSymbol d (residueRepresentative d x) *
      additivePhase d (h * residueRepresentative d x)
  have hmix (v : Residues a × Residues b) : f (a*b) (e v) =
      (cubicSymbol a b*cubicSymbol b a)*(f a v.1*f b v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h * residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      simp only [map_mul, heq]
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr (mul_ne_zero ha0 hb0) heqh,
      cubicSymbol_mix ha hb]
    rw [show h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2) =
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix ha0 hb0]
    ring
  have hsum : (∑ x : Residues (a*b), f (a*b) x) =
      (cubicSymbol a b*cubicSymbol b a)*
      ((∑ x : Residues a, f a x)*(∑ y : Residues b, f b y)) := by
    rw [← Equiv.sum_comp e (f (a*b))]
    simp_rw [hmix]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hn : (Real.sqrt (norm (a*b)) : ℂ) =
      (Real.sqrt (norm a) : ℂ)*(Real.sqrt (norm b) : ℂ) := by
    have hn : norm (a*b) = norm a*norm b := by
      simp only [norm, Subalgebra.coe_mul, Complex.normSq_mul]
    rw [hn, Real.sqrt_mul (norm_nonneg a), Complex.ofReal_mul]
  simp only [frequencyGauss, tsum_fintype]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f (a*b) x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, f a x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, f b y))*(cubicSymbol a b*cubicSymbol b a)
  ring

lemma frequencyGauss_one (h : Eisenstein) : frequencyGauss 1 h = 1 := by
  let : Finite (Residues (1 : Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1 : Eisenstein)) := Fintype.ofFinite _
  have hphase (v : Eisenstein) : additivePhase 1 v = 1 := by
    rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (v-0))),
      additivePhase_zero]
  have hc : Fintype.card (Residues (1 : Eisenstein)) = 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card one_ne_zero, normNat_one]
  simp [frequencyGauss, tsum_fintype, cubicSymbol, normalizedFactors_one, hphase, hc, norm]

lemma frequencyGauss_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) (h : Eisenstein) :
    frequencyGauss (∏ p ∈ s, p) h =
      star (cubicSymbol (∏ p ∈ s, p) h) * gauss (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frequencyGauss_one, gauss_one, cubicSymbol]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun heq => hps (heq ▸ hq))
    rw [Finset.prod_insert hps,
      frequencyGauss_mul_of_isCoprime hp'.1 hprimary hc,
      frequencyGauss_prime hp', ih hs,
      cubicSymbol_mul_lower hp'.2.ne_zero (primary_ne_zero hprimary),
      gauss_mul_of_isCoprime hp'.1 hprimary hc, star_mul']
    ring

theorem frequencyGauss_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (h : Eisenstein) :
    frequencyGauss b h = star (cubicSymbol b h) * gauss b := by
  rw [← primaryPrimeFactors_prod hb hs]
  exact frequencyGauss_prod_primaryPrimes _
    (fun p hp => (primaryPrimeFactor_spec hb hp).1) h

def conjugateFrequencyGauss (b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    star (cubicSymbol b (residueRepresentative b v)) *
      additivePhase b (h * residueRepresentative b v)

lemma conjugateFrequencyGauss_eq {b : Eisenstein} (hb : primary b)
    (h : Eisenstein) : conjugateFrequencyGauss b h = star (frequencyGauss b (-h)) := by
  let : Finite (Residues b) := finite_residues (primary_ne_zero hb)
  let : Fintype (Residues b) := Fintype.ofFinite _
  simp only [conjugateFrequencyGauss, frequencyGauss, tsum_fintype,
    star_mul', star_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro v hv
    rw [neg_mul, additivePhase_neg (primary_ne_zero hb), star_star]

lemma conjugateFrequencyGauss_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (h : Eisenstein) :
    conjugateFrequencyGauss b h = cubicSymbol b h * star (gauss b) := by
  rw [conjugateFrequencyGauss_eq hb, frequencyGauss_squarefree hb hs,
    cubicSymbol_neg hb, star_mul', star_star]

def mixedFrequencyGauss (a b h : Eisenstein) : ℂ :=
  (Real.sqrt (norm (a*b)) : ℂ)⁻¹ * ∑' v : Residues (a*b),
    (cubicSymbol a (residueRepresentative (a*b) v) *
       star (cubicSymbol b (residueRepresentative (a*b) v))) *
      additivePhase (a*b) (h * residueRepresentative (a*b) v)

lemma mixedFrequencyGauss_CRT {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hab : IsCoprime a b) (h : Eisenstein) :
    mixedFrequencyGauss a b h = frequencyGauss a h * conjugateFrequencyGauss b h *
      (cubicSymbol a b * star (cubicSymbol b a)) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (x : Residues (a*b)) : ℂ :=
    (cubicSymbol a (residueRepresentative (a*b) x) *
      star (cubicSymbol b (residueRepresentative (a*b) x))) *
      additivePhase (a*b) (h * residueRepresentative (a*b) x)
  let fa (x : Residues a) : ℂ :=
    cubicSymbol a (residueRepresentative a x) * additivePhase a (h * residueRepresentative a x)
  let fb (x : Residues b) : ℂ :=
    star (cubicSymbol b (residueRepresentative b x)) * additivePhase b (h * residueRepresentative b x)
  have hmix (v : Residues a × Residues b) : f (e v) =
      (cubicSymbol a b * star (cubicSymbol b a)) * (fa v.1 * fb v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    have hdiv : a*b ∣ residueRepresentative (a*b) (e v) -
        (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp heq)
    have heqa : Ideal.Quotient.mk (modulus a) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus a) (b*residueRepresentative a v.1) := by
      apply residue_eq_of_dvd_sub
      convert dvd_add (dvd_trans (dvd_mul_right a b) hdiv)
        (dvd_mul_right a (residueRepresentative b v.2)) using 1
      ring
    have heqb : Ideal.Quotient.mk (modulus b) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus b) (a*residueRepresentative b v.2) := by
      apply residue_eq_of_dvd_sub
      convert dvd_add (dvd_trans (dvd_mul_left b a) hdiv)
        (dvd_mul_right b (residueRepresentative a v.1)) using 1
      ring
    have heqh : Ideal.Quotient.mk (modulus (a*b)) (h * residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2)) := by
      simp only [map_mul, heq]
    dsimp only [f, fa, fb]
    rw [cubicSymbol_congr heqa, cubicSymbol_congr heqb,
      additivePhase_congr (mul_ne_zero ha0 hb0) heqh,
      cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb, star_mul']
    rw [show h * (b*residueRepresentative a v.1+a*residueRepresentative b v.2) =
      b*(h*residueRepresentative a v.1)+a*(h*residueRepresentative b v.2) by ring,
      additivePhase_mix ha0 hb0]
    ring
  have hsum : (∑ x : Residues (a*b), f x) =
      (cubicSymbol a b * star (cubicSymbol b a)) *
      ((∑ x : Residues a, fa x)*(∑ y : Residues b, fb y)) := by
    rw [← Equiv.sum_comp e f]
    simp_rw [hmix]
    rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  have hn : (Real.sqrt (norm (a*b)) : ℂ) =
      (Real.sqrt (norm a) : ℂ)*(Real.sqrt (norm b) : ℂ) := by
    have hn : norm (a*b) = norm a*norm b := by
      simp only [norm, Subalgebra.coe_mul, Complex.normSq_mul]
    rw [hn, Real.sqrt_mul (norm_nonneg a), Complex.ofReal_mul]
  simp only [mixedFrequencyGauss, frequencyGauss, conjugateFrequencyGauss, tsum_fintype]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, fa x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, fb y))*(cubicSymbol a b*star (cubicSymbol b a))
  ring

theorem mixedFrequencyGauss_squarefree {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (h : Eisenstein) :
    mixedFrequencyGauss a b h =
      (gauss a * star (gauss b)) * (star (cubicSymbol a h) * cubicSymbol b h) := by
  rw [mixedFrequencyGauss_CRT ha hb hab,
    frequencyGauss_squarefree ha hsa, conjugateFrequencyGauss_squarefree hb hsb]
  have hu : cubicSymbol a b * star (cubicSymbol b a) = 1 := by
    rw [cubic_reciprocity ha hb]
    change cubicSymbol b a * starRingEnd ℂ (cubicSymbol b a) = 1
    rw [Complex.mul_conj', norm_cubicSymbol_of_isCoprime hb hab.symm]
    norm_num
  rw [hu]
  ring

lemma mixedFrequencyGauss_zero {a b : Eisenstein} (ha : primary a)
    (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hne : a ≠ b) : mixedFrequencyGauss a b 0 = 0 := by
  rw [mixedFrequencyGauss_squarefree ha hb hsa hsb hab]
  by_cases ha1 : a = 1
  · have hb1 : b ≠ 1 := fun hb1 => hne (ha1.trans hb1.symm)
    have hnc : ¬ IsCoprime b 0 := fun hc =>
      hb1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) hb)
    rw [cubicSymbol_eq_zero_of_not_isCoprime hb hnc]
    simp
  · have hnc : ¬ IsCoprime a 0 := fun hc =>
      ha1 (primary_unit_eq_one (isCoprime_zero_right.mp hc) ha)
    rw [cubicSymbol_eq_zero_of_not_isCoprime ha hnc]
    simp

end CubicFirstMoment

end
end
end

end OAI
