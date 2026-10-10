import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction
namespace Frobenius

variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]

abbrev Series := MvPowerSeries ι k

def powerIdeal (ell : ℕ) : Ideal (Series (ι := ι) (k := k)) :=
  Ideal.span (Set.range fun i : ι => (MvPowerSeries.X i : Series (ι := ι) (k := k))^ell)

abbrev Ring (ell : ℕ) := Series (ι := ι) (k := k) ⧸ powerIdeal (ι := ι) (k := k) ell

def Good (ell : ℕ) (e : ι →₀ ℕ) : Prop := ∀ i, e i < ell

def cut (ell : ℕ) (s : Finset ι) (f : Series (ι := ι) (k := k)) : Series (ι := ι) (k := k) :=
  fun e => if ∀ i ∈ s, e i < ell then MvPowerSeries.coeff e f else 0

@[simp] theorem coeff_cut (ell : ℕ) (s : Finset ι) (f : Series (ι := ι) (k := k)) (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (cut ell s f) =
      if ∀ i ∈ s, e i < ell then MvPowerSeries.coeff e f else 0 := rfl

@[simp] theorem cut_empty (ell : ℕ) (f : Series (ι := ι) (k := k)) :
    cut ell ∅ f = f := by
  ext e
  simp

                                                          
def tail (ell : ℕ) (i : ι) (f : Series (ι := ι) (k := k)) : Series (ι := ι) (k := k) :=
  fun e => MvPowerSeries.coeff (e + Finsupp.single i ell) f

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coeff_tail (ell : ℕ) (i : ι) (f : Series (ι := ι) (k := k)) (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (tail ell i f) =
      MvPowerSeries.coeff (e + Finsupp.single i ell) f := rfl

theorem one_coordinate_decomposition (ell : ℕ) (i : ι) (f : Series (ι := ι) (k := k)) :
    f - cut ell {i} f = (MvPowerSeries.X i)^ell * tail ell i f := by
  ext e
  simp only [map_sub, coeff_cut, Finset.mem_singleton, forall_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul, one_mul, coeff_tail]
  by_cases hi : ell ≤ e i
  · rw [ite_eq_right (by omega), ite_eq_left (Finsupp.single_le_iff.mpr hi),
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi), sub_zero]
  · rw [ite_eq_left (by omega), ite_eq_right (by simpa only [Finsupp.single_le_iff] using hi), sub_self]

theorem cut_insert (ell : ℕ) (s : Finset ι) (i : ι) (f : Series (ι := ι) (k := k)) :
    cut ell (insert i s) f = cut ell {i} (cut ell s f) := by
  ext e
  simp only [coeff_cut, Finset.mem_insert, forall_eq_or_imp, Finset.mem_singleton, forall_eq]
  by_cases hi : e i < ell <;> by_cases hs : ∀ j ∈ s, e j < ell <;> simp [hi, hs]

theorem subtract_cut_mem (ell : ℕ) (s : Finset ι) (f : Series (ι := ι) (k := k)) :
    f - cut ell s f ∈ powerIdeal (ι := ι) (k := k) ell := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [cut_insert]
      have htail : cut ell s f - cut ell {i} (cut ell s f) ∈ powerIdeal ell := by
        rw [one_coordinate_decomposition]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
      convert (powerIdeal (ι := ι) (k := k) ell).add_mem ih htail using 1
      abel

omit [DecidableEq ι] in
theorem coeff_ideal_eq_zero (ell : ℕ) (e : ι →₀ ℕ) (he : Good ell e)
    (f : Series (ι := ι) (k := k)) (hf : f ∈ powerIdeal ell) :
    MvPowerSeries.coeff e f = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]
  exact ite_eq_right (by simpa only [Finsupp.single_le_iff, not_le] using he i)

theorem mem_powerIdeal_iff (ell : ℕ) (f : Series (ι := ι) (k := k)) :
    f ∈ powerIdeal ell ↔ ∀ e, Good ell e → MvPowerSeries.coeff e f = 0 := by
  constructor
  · exact fun hf e he => coeff_ideal_eq_zero ell e he f hf
  · intro hf
    have hc : cut ell Finset.univ f = 0 := by
      ext e
      simp only [coeff_cut, Finset.mem_univ, forall_const, map_zero]
      split_ifs with he
      · exact hf e he
      · rfl
    simpa only [hc, sub_zero] using subtract_cut_mem ell Finset.univ f

                                                                            
def quotientCoeff (ell : ℕ) (e : ι →₀ ℕ) (he : Good ell e) : Ring (ι := ι) (k := k) ell →ₗ[k] k :=
  (powerIdeal (ι := ι) (k := k) ell).restrictScalars k |>.liftQ
    (MvPowerSeries.coeff e) (by
      intro f hf
      exact coeff_ideal_eq_zero ell e he f hf)

omit [DecidableEq ι] in
@[simp] theorem quotientCoeff_mk (ell : ℕ) (e : ι →₀ ℕ) (he : Good ell e)
    (f : Series (ι := ι) (k := k)) :
    quotientCoeff ell e he (Ideal.Quotient.mk _ f) = MvPowerSeries.coeff e f := rfl

theorem quotient_ext (ell : ℕ) (x y : Ring (ι := ι) (k := k) ell)
    (h : ∀ e (he : Good ell e), quotientCoeff ell e he x = quotientCoeff ell e he y) : x = y := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem, mem_powerIdeal_iff]
  intro e he
  simpa only [map_sub, sub_eq_zero, quotientCoeff_mk] using h e he

                                                   
abbrev Box (ell : ℕ) := ι → Fin ell

def exponent (ell : ℕ) (v : Box (ι := ι) ell) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).val)

omit [DecidableEq ι] in
@[simp] theorem exponent_apply (ell : ℕ) (v : Box (ι := ι) ell) (i : ι) :
    exponent ell v i = (v i).val := by simp [exponent]

omit [DecidableEq ι] in
theorem exponent_good (ell : ℕ) (v : Box (ι := ι) ell) : Good ell (exponent ell v) := by
  intro i
  simpa only [exponent_apply] using (v i).isLt

omit [DecidableEq ι] in
theorem exponent_injective (ell : ℕ) : Function.Injective (exponent (ι := ι) ell) := by
  intro v w h
  funext i
  apply Fin.ext
  have := DFunLike.congr_fun h i
  simpa only [exponent_apply] using this

def boxOfGood (ell : ℕ) (e : ι →₀ ℕ) (he : Good ell e) : Box (ι := ι) ell :=
  fun i => ⟨e i, he i⟩

omit [DecidableEq ι] in
@[simp] theorem exponent_boxOfGood (ell : ℕ) (e : ι →₀ ℕ) (he : Good ell e) :
    exponent ell (boxOfGood ell e he) = e := by
  ext i
  simp [boxOfGood]

                                                     
def monomial (ell : ℕ) (v : Box (ι := ι) ell) : Ring (ι := ι) (k := k) ell :=
  Ideal.Quotient.mk _ (MvPowerSeries.monomial (exponent ell v) 1)

@[simp] theorem quotientCoeff_monomial (ell : ℕ) (v w : Box (ι := ι) ell) :
    quotientCoeff ell (exponent ell v) (exponent_good ell v) (monomial (k := k) ell w) =
      if v = w then 1 else 0 := by
  rw [monomial, quotientCoeff_mk, MvPowerSeries.coeff_monomial]
  simp only [(exponent_injective ell).eq_iff]

def coefficients (ell : ℕ) : Ring (ι := ι) (k := k) ell →ₗ[k] (Box (ι := ι) ell → k) :=
  LinearMap.pi fun v => quotientCoeff ell (exponent ell v) (exponent_good ell v)

omit [DecidableEq ι] in
@[simp] theorem coefficients_apply (ell : ℕ) (x : Ring (ι := ι) (k := k) ell)
    (v : Box (ι := ι) ell) : coefficients ell x v =
      quotientCoeff ell (exponent ell v) (exponent_good ell v) x := rfl

theorem coefficients_injective (ell : ℕ) :
    Function.Injective (coefficients (ι := ι) (k := k) ell) := by
  intro x y h
  apply quotient_ext
  intro e he
  have hh := congrFun h (boxOfGood ell e he)
  simpa only [coefficients_apply, exponent_boxOfGood] using hh

def fromCoefficients (ell : ℕ) (c : Box (ι := ι) ell → k) : Ring (ι := ι) (k := k) ell :=
  ∑ v, c v • monomial ell v

@[simp] theorem coefficients_fromCoefficients (ell : ℕ) (c : Box (ι := ι) ell → k) :
    coefficients ell (fromCoefficients ell c) = c := by
  funext v
  simp [fromCoefficients]

                                                                                 
def coefficientEquiv (ell : ℕ) :
    Ring (ι := ι) (k := k) ell ≃ₗ[k] (Box (ι := ι) ell → k) :=
  LinearEquiv.ofBijective (coefficients ell)
    ⟨coefficients_injective ell, fun c => ⟨fromCoefficients ell c, coefficients_fromCoefficients ell c⟩⟩

instance moduleFinite_quotient (ell : ℕ) : Module.Finite k (Ring (ι := ι) (k := k) ell) :=
  Module.Finite.equiv (coefficientEquiv (ι := ι) (k := k) ell).symm

instance moduleFree_quotient (ell : ℕ) : Module.Free k (Ring (ι := ι) (k := k) ell) :=
  Module.Free.of_equiv (coefficientEquiv (ι := ι) (k := k) ell).symm

theorem monomial_expansion (ell : ℕ) (x : Ring (ι := ι) (k := k) ell) :
    x = ∑ v, coefficients ell x v • monomial ell v := by
  apply coefficients_injective ell
  exact (coefficients_fromCoefficients ell _).symm

def topExponent (ell : ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => ell - 1)

omit [DecidableEq ι] in
@[simp] theorem topExponent_apply (ell : ℕ) (i : ι) :
    topExponent (ι := ι) ell i = ell - 1 := by simp [topExponent]

omit [DecidableEq ι] in
theorem topExponent_good {ell : ℕ} (hell : 0 < ell) : Good ell (topExponent (ι := ι) ell) := by
  intro i
  simp only [topExponent_apply]
  omega

omit [DecidableEq ι] in
theorem good_le_top {ell : ℕ} (e : ι →₀ ℕ) (he : Good ell e) : e ≤ topExponent ell := by
  intro i
  simp only [topExponent_apply]
  have := he i
  omega

                                                                                
def topMonomial (ell : ℕ) : Ring (ι := ι) (k := k) ell :=
  Ideal.Quotient.mk _ (MvPowerSeries.monomial (topExponent ell) 1)

omit [DecidableEq ι] in
@[simp] theorem topMonomial_coefficient {ell : ℕ} (hell : 0 < ell) :
    quotientCoeff ell (topExponent ell) (topExponent_good hell)
      (topMonomial (ι := ι) (k := k) ell) = 1 := by
  simp [topMonomial]

omit [DecidableEq ι] in
theorem topMonomial_ne_zero [Nontrivial k] {ell : ℕ} (hell : 0 < ell) :
    topMonomial (ι := ι) (k := k) ell ≠ 0 := by
  intro h
  have hc := topMonomial_coefficient (ι := ι) (k := k) hell
  rw [h, map_zero] at hc
  exact zero_ne_one hc

def constantHom (ell : ℕ) (hell : 0 < ell) : Ring (ι := ι) (k := k) ell →+* k :=
  Ideal.Quotient.lift _ MvPowerSeries.constantCoeff (by
    intro f hf
    exact coeff_ideal_eq_zero ell 0 (fun i => by simpa using hell) f hf)

omit [DecidableEq ι] in
@[simp] theorem constantHom_mk (ell : ℕ) (hell : 0 < ell) (f : Series (ι := ι) (k := k)) :
    constantHom ell hell (Ideal.Quotient.mk _ f) = MvPowerSeries.constantCoeff f := rfl

theorem topMonomial_mul {ell : ℕ} (hell : 0 < ell) (x : Ring (ι := ι) (k := k) ell) :
    topMonomial ell * x = constantHom ell hell x • topMonomial ell := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply quotient_ext
  intro e he
  rw [map_smul, constantHom_mk]
  change quotientCoeff ell e he
    (Ideal.Quotient.mk _ (MvPowerSeries.monomial (topExponent ell) 1) *
      Ideal.Quotient.mk _ f) = _
  rw [← map_mul, quotientCoeff_mk, MvPowerSeries.coeff_monomial_mul]
  rw [topMonomial, quotientCoeff_mk, MvPowerSeries.coeff_monomial]
  by_cases ht : e = topExponent ell
  · subst e
    simp only [le_refl, ite_true, tsub_self, one_mul, smul_eq_mul, mul_one]
    rfl
  · have hnot : ¬ topExponent ell ≤ e := fun h => ht (le_antisymm (good_le_top e he) h)
    simp [hnot, ht]

omit [DecidableEq ι] in
@[simp] theorem constantHom_algebraMap (ell : ℕ) (hell : 0 < ell) (a : k) :
    constantHom (ι := ι) ell hell (algebraMap k (Ring (ι := ι) (k := k) ell) a) = a := by
  rw [← Ideal.Quotient.mk_algebraMap k (powerIdeal (ι := ι) (k := k) ell),
    constantHom_mk, ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C]

omit [DecidableEq ι] in
theorem algebraMap_injective (ell : ℕ) (hell : 0 < ell) :
    Function.Injective (algebraMap k (Ring (ι := ι) (k := k) ell)) :=
  Function.LeftInverse.injective (constantHom_algebraMap ell hell)

omit [DecidableEq ι] in
theorem quotient_charP {ell : ℕ} (hell : 0 < ell) [CharP k ell] :
    CharP (Ring (ι := ι) (k := k) ell) ell :=
  charP_of_injective_algebraMap (algebraMap_injective ell hell) ell

                                                                                   
theorem monomial_power_zero {ell : ℕ} (e : ι →₀ ℕ) (he : e ≠ 0) :
    (Ideal.Quotient.mk (powerIdeal (ι := ι) (k := k) ell)
      (MvPowerSeries.monomial e (1 : k))) ^ ell = 0 := by
  rw [← map_pow, MvPowerSeries.monomial_pow, one_pow, Ideal.Quotient.eq_zero_iff_mem,
    mem_powerIdeal_iff]
  intro a ha
  rw [MvPowerSeries.coeff_monomial]
  apply ite_eq_right
  intro h
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := Function.ne_iff.mp (by
    intro heq
    exact he (DFunLike.ext _ _ (congrFun heq)))
  have hh := ha i
  rw [h, Finsupp.nsmul_apply, smul_eq_mul] at hh
  have : ell ≤ ell * e i := by
    nth_rw 1 [← mul_one ell]
    exact Nat.mul_le_mul_left ell (by omega)
  omega

                                                                          
                                                                                 
theorem frobenius_zero_of_constant {ell : ℕ} [CharP k ell] [Fact ell.Prime]
    (x : Ring (ι := ι) (k := k) ell)
    (hx : (constantHom ell (Nat.Prime.pos Fact.out) x)^ell = 0) : x^ell = 0 := by
  let : CharP (Ring (ι := ι) (k := k) ell) ell := quotient_charP (Nat.Prime.pos Fact.out)
  rw [monomial_expansion ell x, sum_pow_char]
  apply Finset.sum_eq_zero
  intro v _
  rw [smul_pow]
  by_cases he : exponent ell v = 0
  · have hc : coefficients ell x v = constantHom ell (Nat.Prime.pos Fact.out) x := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      change MvPowerSeries.coeff (exponent ell v) f = MvPowerSeries.constantCoeff f
      rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff]
    rw [hc, hx, zero_smul]
  · rw [monomial, monomial_power_zero _ he, smul_zero]

theorem series_frobenius_mem {ell : ℕ} [CharP k ell] [Fact ell.Prime]
    (f : Series (ι := ι) (k := k)) (hf : (MvPowerSeries.constantCoeff f)^ell = 0) :
    f^ell ∈ powerIdeal ell := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_pow]
  exact frobenius_zero_of_constant _ hf

section Evaluation

variable {S : Type*} [CommRing S] [Algebra k S]

                                                                           
                                                                        
def nilpotentSubst (b : ι → S) : ι → MvPowerSeries Unit S :=
  fun i => MvPowerSeries.C (b i)

omit [DecidableEq ι] in
theorem has_nilpotentSubst (b : ι → S) (hb : ∀ i, IsNilpotent (b i)) :
    MvPowerSeries.HasSubst (nilpotentSubst b) := {
    const_coeff := fun i => by simpa [nilpotentSubst] using hb i
    coeff_zero := fun _ => Set.toFinite _ }

def nilpotentEval (b : ι → S) (hb : ∀ i, IsNilpotent (b i)) : Series (ι := ι) (k := k) →ₐ[k] S :=
  { toRingHom := MvPowerSeries.constantCoeff.comp
      (MvPowerSeries.substAlgHom (R := k) (has_nilpotentSubst b hb)).toRingHom
    commutes' := fun r => by
      change MvPowerSeries.constantCoeff
        ((MvPowerSeries.substAlgHom (R := k) (has_nilpotentSubst b hb))
          (algebraMap k (Series (ι := ι) (k := k)) r)) = _
      rw [AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C] }

omit [DecidableEq ι] in
@[simp] theorem nilpotentEval_X (b : ι → S) (hb : ∀ i, IsNilpotent (b i)) (i : ι) :
    nilpotentEval (k := k) b hb (MvPowerSeries.X i) = b i := by
  change MvPowerSeries.constantCoeff
    ((MvPowerSeries.substAlgHom (R := k) (has_nilpotentSubst b hb)) (MvPowerSeries.X i)) = _
  rw [MvPowerSeries.substAlgHom_X]
  exact MvPowerSeries.constantCoeff_C _

omit [Fintype ι] [DecidableEq ι] in
theorem isNilpotent_of_powers (ell : ℕ) (b : ι → S) (hb : ∀ i, b i ^ ell = 0) :
    ∀ i, IsNilpotent (b i) := fun i => ⟨ell, hb i⟩

omit [DecidableEq ι] in
theorem nilpotentEval_zero_on_powerIdeal (ell : ℕ) (b : ι → S) (hb : ∀ i, b i ^ ell = 0)
    (f : Series (ι := ι) (k := k)) (hf : f ∈ powerIdeal ell) :
    nilpotentEval (k := k) b (isNilpotent_of_powers ell b hb) f = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, map_pow, nilpotentEval_X, hb, mul_zero]

                                                                          
def eval (ell : ℕ) (b : ι → S) (hb : ∀ i, b i ^ ell = 0) : Ring (ι := ι) (k := k) ell →ₐ[k] S :=
  Ideal.Quotient.liftₐ (powerIdeal (ι := ι) (k := k) ell)
    (nilpotentEval (k := k) b (isNilpotent_of_powers ell b hb))
    (nilpotentEval_zero_on_powerIdeal (k := k) ell b hb)

def coordinate (ell : ℕ) (i : ι) : Ring (ι := ι) (k := k) ell :=
  Ideal.Quotient.mk _ (MvPowerSeries.X i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coordinate_pow (ell : ℕ) (i : ι) :
    coordinate (k := k) ell i ^ ell = 0 := by
  rw [coordinate, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [DecidableEq ι] in
@[simp] theorem eval_coordinate (ell : ℕ) (b : ι → S) (hb : ∀ i, b i ^ ell = 0) (i : ι) :
    eval (k := k) ell b hb (coordinate ell i) = b i := by
  change nilpotentEval (k := k) b (isNilpotent_of_powers ell b hb) (MvPowerSeries.X i) = b i
  exact nilpotentEval_X b (isNilpotent_of_powers ell b hb) i

omit [DecidableEq ι] in
theorem monomial_eq_prod (ell : ℕ) (v : Box (ι := ι) ell) :
    monomial (k := k) ell v = (exponent ell v).prod (fun i n => coordinate ell i ^ n) := by
  rw [monomial, MvPowerSeries.monomial_one_eq]
  simp only [Finsupp.prod, map_prod, map_pow, coordinate]

                                                                                    
theorem algHom_ext (ell : ℕ) (f g : Ring (ι := ι) (k := k) ell →ₐ[k] S)
    (h : ∀ i, f (coordinate ell i) = g (coordinate ell i)) : f = g := by
  ext x
  rw [monomial_expansion ell x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, map_smul, monomial_eq_prod]
  congr 1
  simp only [Finsupp.prod, map_prod, map_pow, h]

@[simp] theorem eval_self (ell : ℕ) :
    eval ell (coordinate (ι := ι) (k := k) ell) (coordinate_pow ell) = AlgHom.id k _ := by
  apply algHom_ext
  intro i
  simp

end Evaluation

section Derivatives

variable (ell : ℕ) [CharP k ell]

omit [DecidableEq ι] in
theorem pderiv_powerIdeal (i : ι) (f : Series (ι := ι) (k := k)) (hf : f ∈ powerIdeal ell) :
    MvPowerSeries.pderiv i f ∈ powerIdeal ell := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  apply Ideal.sum_mem
  intro j _
  have hz : (ell : Series (ι := ι) (k := k)) = 0 := by
    simpa only [map_natCast, map_zero] using
      congrArg (MvPowerSeries.C : k →+* Series (ι := ι) (k := k)) (CharP.cast_eq_zero k ell)
  rw [Derivation.leibniz, MvPowerSeries.pderiv_pow]
  simp only [smul_eq_mul, hz, zero_mul, mul_zero, zero_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

def partialDeriv (i : ι) : Derivation k (Ring (ι := ι) (k := k) ell) (Ring (ι := ι) (k := k) ell) :=
  Derivation.liftOfSurjective (f := Ideal.Quotient.mkₐ k (powerIdeal ell))
    Ideal.Quotient.mk_surjective (d := MvPowerSeries.pderiv i) (by
      intro f hf
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact pderiv_powerIdeal ell i f (Ideal.Quotient.eq_zero_iff_mem.mp hf))

omit [DecidableEq ι] in
@[simp] theorem partial_mk (i : ι) (f : Series (ι := ι) (k := k)) :
    partialDeriv ell i (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (MvPowerSeries.pderiv i f) := by
  unfold partialDeriv
  apply Derivation.liftOfSurjective_apply

@[simp] theorem partial_coordinate (i j : ι) :
    partialDeriv (k := k) ell i (Ideal.Quotient.mk _ (MvPowerSeries.X j)) = if i = j then 1 else 0 := by
  rw [partial_mk]
  by_cases h : i = j
  · subst j; simp
  · simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm h), h]

omit [Fintype ι] in
theorem series_pderiv_commute (i j : ι) (f : Series (ι := ι) (k := k)) :
    MvPowerSeries.pderiv i (MvPowerSeries.pderiv j f) =
      MvPowerSeries.pderiv j (MvPowerSeries.pderiv i f) := by
  by_cases hij : i = j
  · subst j; rfl
  ext e
  simp only [MvPowerSeries.coeff_pderiv, Finsupp.add_apply]
  simp only [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij), add_zero]
  rw [add_assoc, add_comm (Finsupp.single i 1) (Finsupp.single j 1), ← add_assoc]
  ring

theorem partial_commute (i j : ι) (x : Ring (ι := ι) (k := k) ell) :
    partialDeriv ell i (partialDeriv ell j x) = partialDeriv ell j (partialDeriv ell i x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [partial_mk, series_pderiv_commute i j]

                                                                                   
omit [DecidableEq ι] in
theorem residue_partial_zero (hell : 0 < ell) (i : ι)
    (x : Ring (ι := ι) (k := k) ell) :
    quotientCoeff ell (topExponent ell) (topExponent_good hell) (partialDeriv ell i x) = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [partial_mk, quotientCoeff_mk, MvPowerSeries.coeff_pderiv, topExponent_apply]
  have hn : (ell - 1 : ℕ) + 1 = ell := by omega
  have hc : ((ell - 1 : ℕ) : k) + 1 = 0 := by
    calc
      ((ell - 1 : ℕ) : k) + 1 = ((ell - 1 + 1 : ℕ) : k) := by simp only [Nat.cast_add, Nat.cast_one]
      _ = 0 := by rw [hn]; exact CharP.cast_eq_zero k ell
  rw [hc, mul_zero]

end Derivatives

end Frobenius
end BoundaryOnly.FormalObstruction

end

end OAI
