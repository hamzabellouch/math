import Mathlib
import OAI.NumberTheory.CubicGram.GaussCharacters
import OAI.NumberTheory.CubicGram.PrimaryNormalization

namespace OAI

/-! Composite residue characters, Chinese remainders and squarefree Gauss norms. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
def cubicSymbol (b v : Eisenstein) : ℂ :=
  ((normalizedFactors b).map (fun p => cubicSymbolAtPrime (primaryNormalize p) v)).prod

def gauss (b : Eisenstein) : ℂ :=
  (Real.sqrt (norm b) : ℂ)⁻¹ * ∑' v : Residues b,
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)

lemma primary_ne_zero {b : Eisenstein} (hb : primary b) : b ≠ 0 := by
  let := residue_three_nontrivial
  intro heq
  have h := unit_residue_of_dvd_primary hb (dvd_refl b)
  rw [heq, map_zero] at h
  exact not_isUnit_zero h

lemma primaryNormalize_normalize {p : Eisenstein} (hp : primary p) :
    primaryNormalize (normalize p) = p := by
  apply primary_associated_eq _ hp
    ((primaryNormalize_associated _).symm.trans (normalize_associated p))
  apply primaryNormalize_primary
  exact unit_residue_of_dvd_primary hp (normalize_associated p).dvd

lemma cubicSymbol_prime {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbol p v = cubicSymbolAtPrime p v := by
  simp only [cubicSymbol, normalizedFactors_irreducible hp.2.irreducible,
    Multiset.map_singleton, Multiset.prod_singleton, primaryNormalize_normalize hp.1]

lemma gauss_prime {p : Eisenstein} (hp : primaryPrime p) : gauss p = gaussAtPrime p := by
  simp only [gauss, gaussAtPrime, cubicSymbol_prime hp]

lemma cubicSymbol_congr_prime_divisors {b v w : Eisenstein}
    (h : ∀ p ∈ normalizedFactors b, p ∣ v-w) : cubicSymbol b v = cubicSymbol b w := by
  unfold cubicSymbol
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p hp
  apply cubicSymbolAtPrime_congr
  apply Ideal.Quotient.eq.mpr
  exact Ideal.mem_span_singleton.mpr
    ((primaryNormalize_associated p).dvd_iff_dvd_left.mp (h p hp))

lemma cubicSymbol_congr {b v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus b) v = Ideal.Quotient.mk (modulus b) w) :
    cubicSymbol b v = cubicSymbol b w := by
  apply cubicSymbol_congr_prime_divisors
  intro p hp
  exact dvd_trans (dvd_of_mem_normalizedFactors hp)
    (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

lemma gauss_eq_finite_sum {b : Eisenstein} [Fintype (Residues b)] :
    gauss b = (Real.sqrt (norm b) : ℂ)⁻¹ * ∑ v : Residues b,
      cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v) := by
  rw [gauss, tsum_fintype]

lemma exists_primary_prime_square_dvd {b : Eisenstein} (hb : primary b)
    (hs : ¬Squarefree b) : ∃ p, primaryPrime p ∧ p*p ∣ b := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (primary_ne_zero hb)] at hs
  push Not at hs
  obtain ⟨q,hq,hd⟩ := hs
  have hqb : q ∣ b := dvd_trans (dvd_mul_right q q) hd
  refine ⟨primaryNormalize q, ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary hb hqb), prime_primaryNormalize hq.prime⟩, ?_⟩
  have hh := (primaryNormalize_associated q).pow_pow (n := 2)
  rw [pow_two, pow_two] at hh
  exact hh.dvd_iff_dvd_left.mp hd

lemma cubicSymbol_add_last_lift {p d v w : Eisenstein} :
    cubicSymbol (p*p*d) (v+p*d*w) = cubicSymbol (p*p*d) v := by
  apply cubicSymbol_congr_prime_divisors
  intro q hq
  have hprime := prime_of_normalized_factor q hq
  have hd := dvd_of_mem_normalizedFactors hq
  have hqd : q ∣ p*d := by
    rcases hprime.dvd_or_dvd hd with hqq | hqd
    · rcases hprime.dvd_or_dvd hqq with hqp | hqp
      · exact dvd_mul_of_dvd_left hqp _
      · exact dvd_mul_of_dvd_left hqp _
    · exact dvd_mul_of_dvd_right hqd _
  simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_left hqd w

lemma additivePhase_last_lift {p d : Eisenstein} (hp : p ≠ 0) (hd : d ≠ 0)
    (w : Eisenstein) : additivePhase (p*p*d) (p*d*w) = additivePhase p w := by
  have hp' : (p : ℂ) ≠ 0 := fun h => hp (Subtype.ext h)
  have hd' : (d : ℂ) ≠ 0 := fun h => hd (Subtype.ext h)
  have heq : ((p*d*w : Eisenstein) : ℂ) / ((p*p*d : Eisenstein) : ℂ) =
      (w : ℂ)/(p : ℂ) := by
    simp only [Subalgebra.coe_mul]
    field_simp
  simp only [additivePhase, heq]

lemma exists_nontrivial_additivePhase {p : Eisenstein} (hp : primaryPrime p) :
    ∃ w : Eisenstein, additivePhase p w ≠ 1 := by
  by_contra! h
  apply residueAddChar_ne_one hp
  ext x
  exact h _

theorem gauss_eq_zero_of_not_squarefree {b : Eisenstein} (hb : primary b)
    (hs : ¬Squarefree b) : gauss b = 0 := by
  obtain ⟨p,hp,d,hd⟩ := exists_primary_prime_square_dvd hb hs
  have hd0 : d ≠ 0 := by
    intro h
    apply primary_ne_zero hb
    simp [hd, h]
  subst b
  let b : Eisenstein := p*p*d
  have hb0 : b ≠ 0 := mul_ne_zero (mul_ne_zero hp.2.ne_zero hp.2.ne_zero) hd0
  let : Finite (Residues b) := finite_residues hb0
  let : Fintype (Residues b) := Fintype.ofFinite _
  obtain ⟨w,hw⟩ := exists_nontrivial_additivePhase hp
  let h : Residues b := Ideal.Quotient.mk (modulus b) (p*d*w)
  let f : Residues b → ℂ := fun v =>
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)
  have hf (v : Residues b) : f (v+h) = f v * additivePhase p w := by
    have heq : Ideal.Quotient.mk (modulus b) (residueRepresentative b (v+h)) =
        Ideal.Quotient.mk (modulus b) (residueRepresentative b v + p*d*w) := by
      rw [residueRepresentative_spec, map_add, residueRepresentative_spec]
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr hb0 heq,
      cubicSymbol_add_last_lift, additivePhase_add, additivePhase_last_lift hp.2.ne_zero hd0]
    ring
  have hsum := Equiv.sum_comp (Equiv.addRight h) f
  change (∑ v : Residues b, f (v+h)) = ∑ v : Residues b, f v at hsum
  simp_rw [hf] at hsum
  rw [← Finset.sum_mul] at hsum
  have hz : (∑ v : Residues b, f v) = 0 := by
    rcases mul_eq_zero.mp (show (∑ v : Residues b, f v) * (additivePhase p w - 1) = 0 by
      linear_combination hsum) with hz | hz
    · exact hz
    · exact (hw (sub_eq_zero.mp hz)).elim
  change gauss b = 0
  rw [gauss_eq_finite_sum, show (∑ v : Residues b,
    cubicSymbol b (residueRepresentative b v) * additivePhase b (residueRepresentative b v)) = 0 from hz,
    mul_zero]

lemma cubicSymbol_mul_lower {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Eisenstein) : cubicSymbol (a*b) v = cubicSymbol a v * cubicSymbol b v := by
  simp only [cubicSymbol, normalizedFactors_mul ha hb, Multiset.map_add, Multiset.prod_add]

lemma cubicSymbol_mul_upper {b : Eisenstein} (hb : primary b) (v w : Eisenstein) :
    cubicSymbol b (v*w) = cubicSymbol b v * cubicSymbol b w := by
  unfold cubicSymbol
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p hp
  exact cubicSymbolAtPrime_mul ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary hb (dvd_of_mem_normalizedFactors hp)),
    prime_primaryNormalize (prime_of_normalized_factor p hp)⟩ v w

lemma residue_eq_of_dvd_sub {b v w : Eisenstein} (h : b ∣ v-w) :
    Ideal.Quotient.mk (modulus b) v = Ideal.Quotient.mk (modulus b) w :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

def residueMix (a b : Eisenstein) (v : Residues a × Residues b) : Residues (a*b) :=
  Ideal.Quotient.mk (modulus (a*b))
    (b*residueRepresentative a v.1 + a*residueRepresentative b v.2)

lemma residueMix_injective {a b : Eisenstein} (hab : IsCoprime a b) :
    Function.Injective (residueMix a b) := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ heq
  have hdiv : a*b ∣ (b*residueRepresentative a x+a*residueRepresentative b y)-
      (b*residueRepresentative a x'+a*residueRepresentative b y') :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp heq)
  apply Prod.ext
  · have hdiva := dvd_trans (dvd_mul_right a b) hdiv
    have hdivam : a ∣ a*(residueRepresentative b y-residueRepresentative b y') := dvd_mul_right _ _
    have hdivab : a ∣ b*(residueRepresentative a x-residueRepresentative a x') := by
      convert dvd_sub hdiva hdivam using 1
      ring
    have hx := residue_eq_of_dvd_sub (hab.dvd_of_dvd_mul_left hdivab)
    simpa only [residueRepresentative_spec] using hx
  · have hdivb := dvd_trans (dvd_mul_left b a) hdiv
    have hdivbm : b ∣ b*(residueRepresentative a x-residueRepresentative a x') := dvd_mul_right _ _
    have hdivba : b ∣ a*(residueRepresentative b y-residueRepresentative b y') := by
      convert dvd_sub hdivb hdivbm using 1
      ring
    have hy := residue_eq_of_dvd_sub (hab.symm.dvd_of_dvd_mul_left hdivba)
    simpa only [residueRepresentative_spec] using hy

lemma residueMix_bijective {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : IsCoprime a b) : Function.Bijective (residueMix a b) := by
  let : Finite (Residues a) := finite_residues ha
  let : Finite (Residues b) := finite_residues hb
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha hb)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨residueMix_injective hab, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    Nat.card_prod, residues_card ha, residues_card hb, residues_card (mul_ne_zero ha hb),
    normNat_mul]

lemma additivePhase_mix {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0)
    (v w : Eisenstein) :
    additivePhase (a*b) (b*v+a*w) = additivePhase a v * additivePhase b w := by
  have ha' : (a : ℂ) ≠ 0 := fun h => ha (Subtype.ext h)
  have hb' : (b : ℂ) ≠ 0 := fun h => hb (Subtype.ext h)
  rw [additivePhase_add]
  have hv : additivePhase (a*b) (b*v) = additivePhase a v := by
    have h : ((b*v : Eisenstein) : ℂ)/((a*b : Eisenstein) : ℂ) = (v : ℂ)/(a : ℂ) := by
      simp only [Subalgebra.coe_mul]
      field_simp
    simp only [additivePhase, h]
  have hw : additivePhase (a*b) (a*w) = additivePhase b w := by
    have h : ((a*w : Eisenstein) : ℂ)/((a*b : Eisenstein) : ℂ) = (w : ℂ)/(b : ℂ) := by
      simp only [Subalgebra.coe_mul]
      field_simp
    simp only [additivePhase, h]
  rw [hv,hw]

lemma cubicSymbol_mix {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (v w : Eisenstein) : cubicSymbol (a*b) (b*v+a*w) =
      cubicSymbol a b * cubicSymbol b a * (cubicSymbol a v * cubicSymbol b w) := by
  rw [cubicSymbol_mul_lower (primary_ne_zero ha) (primary_ne_zero hb)]
  have hva : Ideal.Quotient.mk (modulus a) (b*v+a*w) = Ideal.Quotient.mk (modulus a) (b*v) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_left] using dvd_mul_right a w
  have hwb : Ideal.Quotient.mk (modulus b) (b*v+a*w) = Ideal.Quotient.mk (modulus b) (a*w) := by
    apply residue_eq_of_dvd_sub
    simpa only [add_sub_cancel_right] using dvd_mul_right b v
  rw [cubicSymbol_congr hva, cubicSymbol_congr hwb,
    cubicSymbol_mul_upper ha, cubicSymbol_mul_upper hb]
  ring

theorem gauss_mul_of_isCoprime {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (hab : IsCoprime a b) : gauss (a*b) =
      gauss a * gauss b * (cubicSymbol a b * cubicSymbol b a) := by
  have ha0 := primary_ne_zero ha
  have hb0 := primary_ne_zero hb
  let : Finite (Residues a) := finite_residues ha0
  let : Finite (Residues b) := finite_residues hb0
  let : Finite (Residues (a*b)) := finite_residues (mul_ne_zero ha0 hb0)
  let : Fintype (Residues a) := Fintype.ofFinite _
  let : Fintype (Residues b) := Fintype.ofFinite _
  let : Fintype (Residues (a*b)) := Fintype.ofFinite _
  let e := Equiv.ofBijective (residueMix a b) (residueMix_bijective ha0 hb0 hab)
  let f (b : Eisenstein) (x : Residues b) : ℂ :=
    cubicSymbol b (residueRepresentative b x) * additivePhase b (residueRepresentative b x)
  have hmix (v : Residues a × Residues b) : f (a*b) (e v) =
      (cubicSymbol a b*cubicSymbol b a)*(f a v.1*f b v.2) := by
    have heq : Ideal.Quotient.mk (modulus (a*b)) (residueRepresentative (a*b) (e v)) =
        Ideal.Quotient.mk (modulus (a*b))
          (b*residueRepresentative a v.1+a*residueRepresentative b v.2) :=
      residueRepresentative_spec _ _
    dsimp only [f]
    rw [cubicSymbol_congr heq, additivePhase_congr (mul_ne_zero ha0 hb0) heq,
      cubicSymbol_mix ha hb, additivePhase_mix ha0 hb0]
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
  simp only [gauss_eq_finite_sum]
  change (Real.sqrt (norm (a*b)) : ℂ)⁻¹*(∑ x, f (a*b) x) = _
  rw [hsum, hn, mul_inv_rev]
  change _ = ((Real.sqrt (norm a) : ℂ)⁻¹*(∑ x, f a x))*
    ((Real.sqrt (norm b) : ℂ)⁻¹*(∑ y, f b y))*(cubicSymbol a b*cubicSymbol b a)
  ring

lemma residue_isUnit_of_isCoprime {b v : Eisenstein} (h : IsCoprime b v) :
    IsUnit (Ideal.Quotient.mk (modulus b) v) := by
  have hh := h.map (Ideal.Quotient.mk (modulus b))
  have hb : Ideal.Quotient.mk (modulus b) b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl b))
  rwa [hb, isCoprime_zero_left] at hh

lemma norm_cubicSymbolAtPrime_of_isCoprime {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsCoprime p v) : ‖cubicSymbolAtPrime p v‖ = 1 := by
  have hv' := residue_isUnit_of_isCoprime hv
  obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv'
  rw [cubicSymbol_euler_value hp hv' j hj, norm_pow,
    (omega_primitive.isOfFinOrder (by norm_num)).norm_eq_one, one_pow]

lemma norm_cubicSymbol_of_isCoprime {b v : Eisenstein} (hb : primary b)
    (hv : IsCoprime b v) : ‖cubicSymbol b v‖ = 1 := by
  unfold cubicSymbol
  rw [← normHom_apply, map_multiset_prod, Multiset.map_map]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Multiset.mem_map.mp hz
  have hd : primaryNormalize p ∣ b :=
    (primaryNormalize_associated p).dvd_iff_dvd_left.mp (dvd_of_mem_normalizedFactors hp)
  exact norm_cubicSymbolAtPrime_of_isCoprime
    ⟨primaryNormalize_primary (unit_residue_of_dvd_primary hb (dvd_of_mem_normalizedFactors hp)),
      prime_primaryNormalize (prime_of_normalized_factor p hp)⟩
    (hv.of_isCoprime_of_dvd_left hd)

lemma gauss_one : gauss 1 = 1 := by
  let : Finite (Residues (1 : Eisenstein)) := finite_residues one_ne_zero
  let : Fintype (Residues (1 : Eisenstein)) := Fintype.ofFinite _
  have hphase (v : Eisenstein) : additivePhase 1 v = 1 := by
    rw [additivePhase_congr one_ne_zero (residue_eq_of_dvd_sub (one_dvd (v-0))),
      additivePhase_zero]
  have hc : Fintype.card (Residues (1 : Eisenstein)) = 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card one_ne_zero, normNat_one]
  simp [gauss_eq_finite_sum, cubicSymbol, normalizedFactors_one, hphase, hc, norm]

lemma primaryPrimes_isCoprime {p q : Eisenstein} (hp : primaryPrime p)
    (hq : primaryPrime q) (hne : p ≠ q) : IsCoprime p q := by
  apply isRelPrime_iff_isCoprime.mp
  apply hp.2.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hne (primary_associated_eq hp.1 hq.1 ((hp.2.dvd_prime_iff_associated hq.2).mp hd))

lemma norm_gauss_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) : ‖gauss (∏ p ∈ s, p)‖ = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [gauss_one]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hprimary := primary_finset_prod s (fun q => q) (fun q hq => (hs q hq).1)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, gauss_mul_of_isCoprime hp'.1 hprimary hc,
      norm_mul, norm_mul, gauss_prime hp', norm_gaussAtPrime hp', ih hs,
      norm_mul, norm_cubicSymbol_of_isCoprime hp'.1 hc,
      norm_cubicSymbol_of_isCoprime hprimary hc.symm]
    norm_num

theorem norm_gauss_of_squarefree {b : Eisenstein} (hb : primary b) (hs : Squarefree b) :
    ‖gauss b‖ = 1 := by
  rw [← primaryPrimeFactors_prod hb hs]
  exact norm_gauss_prod_primaryPrimes _ (fun p hp => (primaryPrimeFactor_spec hb hp).1)

theorem norm_gauss {b : Eisenstein} (hb : primary b) :
    ‖gauss b‖ = if Squarefree b then 1 else 0 := by
  split_ifs with hs
  · exact norm_gauss_of_squarefree hb hs
  · rw [gauss_eq_zero_of_not_squarefree hb hs, norm_zero]

end CubicFirstMoment
end
end

end OAI
