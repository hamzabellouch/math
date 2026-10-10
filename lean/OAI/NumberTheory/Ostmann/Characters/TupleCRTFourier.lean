import OAI.NumberTheory.Ostmann.Arithmetic.CRTResidueAverage
import OAI.NumberTheory.Ostmann.Characters.CRTFourier

namespace OAI

/-! # Exact cofactor arguments for the Fourier transform of a prime tuple -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def tupleCofactor {I : Type*} [Fintype I] (p : I → ℕ) (i : I) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, p j

theorem tupleCofactor_mul {I : Type*} [Fintype I] (p : I → ℕ) (i : I) :
    p i * tupleCofactor p i = ∏ j, p j :=
  Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

theorem tupleCofactor_coprime {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (i : I) :
    (tupleCofactor p i).Coprime (p i) := by
  apply Nat.Coprime.symm
  exact Nat.coprime_prod_right_iff.mpr (fun j hj => hc (Finset.mem_erase.mp hj).1.symm)

private theorem stdAddChar_factor {a b M : ℕ} [NeZero a] [NeZero b] [NeZero M]
    (hM : a * b = M) (n : ℕ) :
    ZMod.stdAddChar ((b * n : ℕ) : ZMod M) =
      ZMod.stdAddChar (n : ZMod a) := by
  have hl : ((b * n : ℕ) : ZMod M) = ((b * n : ℕ) : ℤ) := by simp
  have hr : (n : ZMod a) = (n : ℤ) := by simp
  rw [hl, hr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [← hM, Nat.cast_mul]
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne b
  field_simp

theorem tuple_stdAddChar {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (x : ZMod (∏ i, p i)) :
    ZMod.stdAddChar x = ∏ i, ZMod.stdAddChar
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i) := by
  let a (i : I) : ZMod (p i) :=
    (tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc x i
  have hx : x = ∑ i, (tupleCofactor p i : ZMod (∏ i, p i)) * (a i).val := by
    apply (ZMod.prodEquivPi p hc).injective
    ext j
    simp only [map_sum, map_mul, map_natCast, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    rw [Finset.sum_eq_single j]
    · have hu := (ZMod.isUnit_iff_coprime (tupleCofactor p j) (p j)).mpr
        (tupleCofactor_coprime p hc j)
      simp only [ZMod.natCast_zmod_val, a]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul]
    · intro i _ hij
      have hd : p j ∣ tupleCofactor p i :=
        Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
      have hz : (tupleCofactor p i : ZMod (p j)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      simp only [hz, zero_mul]
    · simp
  have hsum (s : Finset I) :
      ZMod.stdAddChar (∑ i ∈ s, (tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) =
        ∏ i ∈ s, ZMod.stdAddChar ((tupleCofactor p i : ZMod (∏ i, p i)) * ((a i).val : ZMod (∏ i, p i))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]
  conv_lhs => rw [hx, hsum]
  apply Finset.prod_congr rfl
  intro i _
  have hpos : 0 < tupleCofactor p i :=
    Finset.prod_pos (fun j _ => NeZero.pos (p j))
  let : NeZero (tupleCofactor p i) := ⟨hpos.ne'⟩
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using
    (stdAddChar_factor (tupleCofactor_mul p i) (a i).val)

noncomputable def tupleCRTFunction {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (x : ZMod (∏ i, p i)) : ℂ :=
  ∏ i, F i (ZMod.prodEquivPi p hc x i)

theorem tupleCRTFunction_intCast {I : Type*} [Fintype I] (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (n : ℤ) :
    tupleCRTFunction p hc F (n : ZMod (∏ i, p i)) = ∏ i, F i (n : ZMod (p i)) := by
  simp only [tupleCRTFunction, map_intCast, Pi.intCast_apply]

theorem tupleCRTFunction_fourier {I : Type*} [Fintype I] (p : I → ℕ)
    [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (u : ZMod (∏ i, p i)) :
    additiveFourier (tupleCRTFunction p hc F) u = ∏ i,
      additiveFourier (F i)
        ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i) := by
  have hphase (x : ZMod (∏ i, p i)) : ZMod.stdAddChar (-(x * u)) =
      ∏ i, ZMod.stdAddChar (-(ZMod.prodEquivPi p hc x i *
        ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i))) := by
    rw [tuple_stdAddChar p hc]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_neg, map_mul, Pi.neg_apply, Pi.mul_apply]
    congr 1
    ring
  simp only [additiveFourier_apply, tupleCRTFunction, hphase]
  simp only [← Finset.prod_mul_distrib]
  have hs := (ZMod.prodEquivPi p hc).toEquiv.sum_comp (fun x : ∀ i, ZMod (p i) =>
    ∏ i, F i (x i) * ZMod.stdAddChar (-(x i *
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i))))
  change (∑ x : ZMod (∏ i, p i), ∏ i, F i (ZMod.prodEquivPi p hc x i) *
    ZMod.stdAddChar (-(ZMod.prodEquivPi p hc x i *
      ((tupleCofactor p i : ZMod (p i))⁻¹ * ZMod.prodEquivPi p hc u i)))) = _ at hs
  rw [hs]
  rw [← Fintype.prod_sum (fun i (x : ZMod (p i)) => F i x *
    ZMod.stdAddChar (-(x * ((tupleCofactor p i : ZMod (p i))⁻¹ *
      ZMod.prodEquivPi p hc u i))))]
  simp only [Nat.cast_prod, Finset.prod_inv_distrib, Finset.prod_mul_distrib]

end Ostmann

end OAI
