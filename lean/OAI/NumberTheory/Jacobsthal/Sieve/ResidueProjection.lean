import OAI.NumberTheory.Jacobsthal.Primes.PrimeEventCounting

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceMoments
open ErdosVarianceSmallModel

theorem cast_nat_residue (M t n : ℕ) [NeZero M] (htM : t ∣ M) :
    (((n : ZMod M).val : ℕ) : ZMod t) = (n : ZMod t) := by
  have hh : Nat.ModEq M (n : ZMod M).val n := (ZMod.natCast_eq_natCast_iff _ _ _).mp
    (ZMod.natCast_zmod_val (n : ZMod M))
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd htM hh)

theorem int_isCoprime_of_natAbs (m : ℤ) (H : ℕ) (hm : m.natAbs.Coprime H) : IsCoprime m (H : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  simpa only [Int.gcd_def,Int.natAbs_natCast] using hm.gcd_eq_one

noncomputable def divisorPhase (C0 m : ℤ) (t : ℕ) : ZMod t := (C0 : ZMod t)*(m : ZMod t)⁻¹

noncomputable def patternPValue (w : ℝ) (H : ℕ) (s : Pattern w H) (t : ℕ) : ZMod t :=
  (s.1.val.val : ZMod t)
noncomputable def patternKValue (w : ℝ) (H : ℕ) (s : Pattern w H) (t : ℕ) : ZMod t :=
  (s.2.val : ZMod t)

noncomputable def divisorPhaseUnit (H : ℕ) (C0 m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hm : m.natAbs.Coprime H) (t : ℕ) (htH : t ∣ H) : (ZMod t)ˣ :=
  (ZMod.unitOfIsCoprime C0 (int_isCoprime_of_natAbs C0 t (by
    have hc : C0.natAbs.Coprime H := by
      rw [Nat.coprime_iff_gcd_eq_one]
      simpa only [Int.gcd_def,Int.natAbs_natCast] using hC0
    exact hc.of_dvd_right htH))) *
    (ZMod.unitOfIsCoprime m (int_isCoprime_of_natAbs m t (hm.of_dvd_right htH)))⁻¹

theorem divisorPhaseUnit_coe (H : ℕ) (C0 m : ℤ) (hC0 : Int.gcd C0 (H : ℤ) = 1)
    (hm : m.natAbs.Coprime H) (t : ℕ) (htH : t ∣ H) :
    (divisorPhaseUnit H C0 m hC0 hm t htH : ZMod t) = divisorPhase C0 m t := rfl

theorem prime_divisorPhase_eq (P : Finset ℕ) (H : ℕ) (C0 : ℤ) (hP : ∀ p ∈ P,p.Prime)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (p : goodPrimes P H) (t : ℕ) (htH : t ∣ H) :
    (p.val : ZMod t) = divisorPhase C0 (primeM P H C0 hP p) t := by
  have hm := (primeM_coprime P H C0 hP hC0 p).of_dvd_right htH
  have hminv := ZMod.coe_int_mul_inv_eq_one (int_isCoprime_of_natAbs _ t hm)
  have hH0 : (H : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr htH
  have he := congrArg (fun n : ℤ => (n : ZMod t)) (primeMK_identity P H C0 hP p)
  have hEq : (p.val : ZMod t)*(primeM P H C0 hP p : ZMod t) = (C0 : ZMod t) := by
    simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_add,hH0,zero_mul,add_zero] using he
  have hh := congrArg (fun x : ZMod t => x*(primeM P H C0 hP p : ZMod t)⁻¹) hEq
  simpa only [mul_assoc,hminv,mul_one,divisorPhase] using hh

theorem primePoint_pValue (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ coprimeModulus w H) :
    patternPValue w H (primePoint P w H C0 hw hP hlarge p).2 t = (p.val : ZMod t) := by
  exact cast_nat_residue (coprimeModulus w H) t p.val ht

theorem primePoint_kValue (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (p : goodPrimes P H) (t : ℕ) (ht : t ∣ divisorModulus w H) :
    patternKValue w H (primePoint P w H C0 hw hP hlarge p).2 t = (primeK P H C0 hP p : ZMod t) := by
  exact cast_nat_residue (divisorModulus w H) t (primeK P H C0 hP p) ht

end ErdosVarianceMoments

end

end Erdos970

end OAI
