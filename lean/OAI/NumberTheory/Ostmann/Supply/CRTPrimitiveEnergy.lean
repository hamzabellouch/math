import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.ExponentialSum

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate

def crtUnitsEquiv {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) :
    (ZMod (∏ i, p i))ˣ ≃* (∀ i, (ZMod (p i))ˣ) :=
  (Units.mapEquiv (ZMod.prodEquivPi p hcop).toMulEquiv).trans MulEquiv.piUnits

@[simp] theorem crtUnitsEquiv_apply {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (u : (ZMod (∏ i, p i))ˣ) (i : ι) :
    (crtUnitsEquiv p hcop u i : ZMod (p i)) =
      ZMod.castHom (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) (ZMod (p i))
        (u : ZMod (∏ i, p i)) := by
  change ZMod.prodEquivPi p hcop (u : ZMod (∏ i, p i)) i = _
  exact ZMod.prodEquivPi_apply p hcop _ i

theorem addChar_sum_eq_prod {R : Type*} [AddCommMonoid R] {ι : Type*}
    (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

def coordinateChar {ι : Type*} [DecidableEq ι] {R : ι → Type*}
    [∀ i, AddCommMonoid (R i)] (ψ : AddChar (∀ i, R i) ℂ) (i : ι) :
    AddChar (R i) ℂ where
  toFun x := ψ (Pi.single i x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [Pi.single_add, AddChar.map_add_eq_mul]

@[simp] theorem coordinateChar_apply {ι : Type*} [DecidableEq ι] {R : ι → Type*}
    [∀ i, AddCommMonoid (R i)] (ψ : AddChar (∀ i, R i) ℂ) (i : ι) (x : R i) :
    coordinateChar ψ i x = ψ (Pi.single i x) := rfl

theorem coordinateChar_isPrimitive {ι : Type*} [DecidableEq ι] {R : ι → Type*}
    [∀ i, Field (R i)] (ψ : AddChar (∀ i, R i) ℂ)
    (hψ : Function.Injective ψ) (i : ι) : (coordinateChar ψ i).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h
  have hval := DFunLike.congr_fun h (1 : R i)
  have heq : ψ (Pi.single i (1 : R i)) = ψ 0 := by simpa using hval
  have hzero := congrFun (hψ heq) i
  simp at hzero

theorem addChar_pi_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, AddCommMonoid (R i)]
    (ψ : AddChar (∀ i, R i) ℂ) (x : ∀ i, R i) :
    ψ x = ∏ i, coordinateChar ψ i (x i) := by
  calc
    ψ x = ψ (∑ i, Pi.single i (x i)) := by rw [Finset.univ_sum_single]
    _ = _ := addChar_sum_eq_prod ψ _ _

theorem primitive_sum_units_field {R : Type*} [Field R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    ∑ u : Rˣ, ψ ((u : R) * a) =
      (Fintype.card R : ℂ) * (if a = 0 then 1 else 0) - 1 := by
  classical
  have hu : ∑ u : Rˣ, ψ ((u : R) * a) =
      ∑ x ∈ (Finset.univ : Finset R).erase 0, ψ (x * a) := by
    calc
      ∑ u : Rˣ, ψ ((u : R) * a) = ∑ x : {x : R // x ≠ 0}, ψ ((x : R) * a) :=
        Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
      _ = _ := (Finset.sum_subtype ((Finset.univ : Finset R).erase 0)
        (fun x => by simp) (fun x => ψ (x * a))).symm
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset R))
    (f := fun x => ψ (x * a)) (by simp : (0 : R) ∈ Finset.univ)
  rw [← hu, zero_mul, AddChar.map_zero_eq_one, AddChar.sum_mulShift a hψ] at hs
  split_ifs with ha
  · rw [ite_eq_left ha] at hs
    simpa only [mul_one] using eq_sub_of_add_eq hs
  · rw [ite_eq_right ha] at hs
    simpa only [mul_zero, Nat.cast_zero] using eq_sub_of_add_eq hs

theorem primitive_sum_units_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Field (R i)] [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    (ψ : AddChar (∀ i, R i) ℂ) (hψ : Function.Injective ψ) (a : ∀ i, R i) :
    ∑ u : (∀ i, R i)ˣ, ψ ((u : ∀ i, R i) * a) =
      ∏ i, ((Fintype.card (R i) : ℂ) * (if a i = 0 then 1 else 0) - 1) := by
  classical
  calc
    ∑ u : (∀ i, R i)ˣ, ψ ((u : ∀ i, R i) * a) =
        ∑ u : ∀ i, (R i)ˣ, ∏ i, coordinateChar ψ i ((u i : R i) * a i) := by
      refine Fintype.sum_equiv MulEquiv.piUnits.toEquiv _ _ ?_
      intro u
      exact addChar_pi_eq_prod ψ _
    _ = ∏ i, ∑ u : (R i)ˣ, coordinateChar ψ i ((u : R i) * a i) :=
      (Fintype.prod_sum (κ := fun i => (R i)ˣ)
        (fun i (u : (R i)ˣ) => coordinateChar ψ i ((u : R i) * a i))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact primitive_sum_units_field _ (coordinateChar_isPrimitive ψ hψ i) _

theorem stdAddChar_sum_units_equiv {q : ℕ} [NeZero q]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (e : ZMod q ≃+* (∀ i, ZMod (p i))) (a b : ℕ) :
    ∑ u : (ZMod q)ˣ,
      ZMod.stdAddChar ((u : ZMod q) * ((a : ZMod q) - (b : ZMod q))) =
      ∏ i, ((p i : ℂ) * (if (a : ZMod (p i)) = (b : ZMod (p i)) then 1 else 0) - 1) := by
  classical
  let : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  let ψ : AddChar (∀ i, ZMod (p i)) ℂ :=
    ZMod.stdAddChar.compAddMonoidHom e.symm.toAddMonoidHom
  have hψ : Function.Injective ψ := ZMod.injective_stdAddChar.comp e.symm.injective
  have hsum :
      (∑ u : (ZMod q)ˣ,
        ZMod.stdAddChar ((u : ZMod q) * ((a : ZMod q) - (b : ZMod q)))) =
      ∑ u : (∀ i, ZMod (p i))ˣ,
        ψ ((u : ∀ i, ZMod (p i)) * e ((a : ZMod q) - (b : ZMod q))) := by
    refine Fintype.sum_equiv (Units.mapEquiv e.toMulEquiv).toEquiv _ _ ?_
    intro u
    simp [ψ]
  rw [hsum, primitive_sum_units_pi ψ hψ]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_sub, map_natCast, Pi.sub_apply, Pi.natCast_apply, ZMod.card, sub_eq_zero]

theorem stdAddChar_sum_units_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (a b : ℕ) :
    letI : NeZero (∏ i, p i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)⟩
    ∑ u : (ZMod (∏ i, p i))ˣ,
      ZMod.stdAddChar ((u : ZMod (∏ i, p i)) *
        ((a : ZMod (∏ i, p i)) - (b : ZMod (∏ i, p i)))) =
      ∏ i, ((p i : ℂ) * (if (a : ZMod (p i)) = (b : ZMod (p i)) then 1 else 0) - 1) := by
  let : NeZero (∏ i, p i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)⟩
  exact stdAddChar_sum_units_equiv p hp (ZMod.prodEquivPi p hcop) a b

theorem stdAddChar_sum_units_squarefree {q : ℕ} [NeZero q]
    (hq : Squarefree q) (a b : ℕ) :
    ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * ((a : ZMod q) - (b : ZMod q))) =
      ∏ p ∈ q.primeFactors,
        ((p : ℂ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1) := by
  classical
  have hp : ∀ p : q.primeFactors, (p : ℕ).Prime :=
    fun p => Nat.prime_of_mem_primeFactors p.property
  have hcop : Pairwise (fun p r : q.primeFactors => (p : ℕ).Coprime (r : ℕ)) := by
    intro p r hpr
    exact (Nat.coprime_primes (hp p) (hp r)).mpr (fun h => hpr (Subtype.ext h))
  have hprod : ∏ p : q.primeFactors, (p : ℕ) = q := by
    exact (Finset.prod_coe_sort q.primeFactors (fun p => p)).trans
      (Nat.prod_primeFactors_of_squarefree hq)
  let e : ZMod q ≃+* (∀ p : q.primeFactors, ZMod (p : ℕ)) :=
    (ZMod.ringEquivCongr hprod.symm).trans (ZMod.prodEquivPi (fun p : q.primeFactors => (p : ℕ)) hcop)
  rw [← Finset.prod_coe_sort]
  exact stdAddChar_sum_units_equiv _ hp e a b

def normalizedCharSum {q : ℕ} [NeZero q] (U : Finset ℕ) (h : ZMod q) : ℂ :=
  (∑ n ∈ U, ZMod.stdAddChar (h * (n : ZMod q))) / (U.card : ℂ)

theorem norm_stdAddChar_sum_sq {q : ℕ} [NeZero q] (U : Finset ℕ) (h : ZMod q) :
    ((‖∑ n ∈ U, ZMod.stdAddChar (h * (n : ZMod q))‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ U, ∑ b ∈ U, ZMod.stdAddChar (h * ((a : ZMod q) - (b : ZMod q))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [map_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hc (z : ZMod q) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  rw [hc, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem norm_normalizedCharSum_sq {q : ℕ} [NeZero q] (U : Finset ℕ) (h : ZMod q) :
    ((‖normalizedCharSum U h‖ ^ 2 : ℝ) : ℂ) =
      (∑ a ∈ U, ∑ b ∈ U, ZMod.stdAddChar (h * ((a : ZMod q) - (b : ZMod q)))) /
        (U.card : ℂ) ^ 2 := by
  rw [normalizedCharSum, norm_div, div_pow, Complex.ofReal_div, norm_stdAddChar_sum_sq]
  simp only [Complex.norm_natCast, Complex.ofReal_pow, Complex.ofReal_natCast]

theorem normalizedCharSum_primitive_energy_complex {q : ℕ} [NeZero q]
    (hq : Squarefree q) (U : Finset ℕ) :
    ((∑ u : (ZMod q)ˣ, ‖normalizedCharSum U (u : ZMod q)‖ ^ 2 : ℝ) : ℂ) =
      (∑ a ∈ U, ∑ b ∈ U, ∏ p ∈ q.primeFactors,
        ((p : ℂ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1)) /
          (U.card : ℂ) ^ 2 := by
  simp only [Complex.ofReal_sum, norm_normalizedCharSum_sq]
  rw [← Finset.sum_div]
  congr 1
  calc
    (∑ u : (ZMod q)ˣ, ∑ a ∈ U, ∑ b ∈ U,
      ZMod.stdAddChar ((u : ZMod q) * ((a : ZMod q) - (b : ZMod q)))) =
        ∑ a ∈ U, ∑ b ∈ U, ∑ u : (ZMod q)ˣ,
          ZMod.stdAddChar ((u : ZMod q) * ((a : ZMod q) - (b : ZMod q))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact stdAddChar_sum_units_squarefree hq a b

theorem normalizedCharSum_primitive_energy {q : ℕ} [NeZero q]
    (hq : Squarefree q) (U : Finset ℕ) :
    (∑ u : (ZMod q)ˣ, ‖normalizedCharSum U (u : ZMod q)‖ ^ 2) =
      (∑ a ∈ U, ∑ b ∈ U, ∏ p ∈ q.primeFactors,
        ((p : ℝ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1)) /
          (U.card : ℝ) ^ 2 := by
  apply Complex.ofReal_injective
  rw [normalizedCharSum_primitive_energy_complex hq U]
  simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_one, apply_ite, Complex.ofReal_zero]

theorem stdAddChar_mul_nat_eq_exp {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (h * (n : ZMod q)) =
      Complex.exp (2 * Real.pi * Complex.I * n * ((h.val : ℝ) / q)) := by
  have hc : (((h.val : ℤ) * (n : ℤ) : ℤ) : ZMod q) = h * (n : ZMod q) := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.stdAddChar_coe]
  congr 1
  simp only [Int.cast_mul, Int.cast_natCast, Complex.ofReal_natCast]
  ring

theorem normalizedExpSum_eq_normalizedCharSum {q : ℕ} [NeZero q]
    (U : Finset ℕ) (h : ZMod q) :
    normalizedExpSum U ((h.val : ℝ) / q) = normalizedCharSum U h := by
  unfold normalizedExpSum normalizedCharSum
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
    (stdAddChar_mul_nat_eq_exp h n).symm

theorem normalizedExpSum_primitive_energy {q : ℕ} [NeZero q]
    (hq : Squarefree q) (U : Finset ℕ) :
    (∑ u : (ZMod q)ˣ,
      ‖normalizedExpSum U (((u : ZMod q).val : ℝ) / q)‖ ^ 2) =
      (∑ a ∈ U, ∑ b ∈ U, ∏ p ∈ q.primeFactors,
        ((p : ℝ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1)) /
          (U.card : ℝ) ^ 2 := by
  simpa only [normalizedExpSum_eq_normalizedCharSum] using
    normalizedCharSum_primitive_energy hq U

theorem normalizedExpSum_primitive_energy_complex {q : ℕ} [NeZero q]
    (hq : Squarefree q) (U : Finset ℕ) :
    ((∑ u : (ZMod q)ˣ,
      ‖normalizedExpSum U (((u : ZMod q).val : ℝ) / q)‖ ^ 2 : ℝ) : ℂ) =
      (∑ a ∈ U, ∑ b ∈ U, ∏ p ∈ q.primeFactors,
        ((p : ℂ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1)) /
          (U.card : ℂ) ^ 2 := by
  simpa only [normalizedExpSum_eq_normalizedCharSum] using
    normalizedCharSum_primitive_energy_complex hq U

end Ostmann.Supply

end

end OAI
