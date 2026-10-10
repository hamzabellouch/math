import OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortEnergy
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPowerTranslation

namespace OAI

/-! A common short-variable residue is represented as p*u-a with
0<=a<p. Translating the whole system by a leaves positive long variables
and short variables divisible by p. -/
namespace TwoPointCorrelations

open Finset Polynomial
open scoped Classical

def halaszShiftedLongShortFrequency {s k N Q : ℕ} (p a : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ℕ :=
  fun j => (∑ i, ((x.1 i).val+1+a)^(j.val+1)) +
    p^(j.val+1)*halaszNatPowerFrequency k x.2 j

def halaszCommonResidueFrequency {s k N Q : ℕ} (p a : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) : Fin k → ℕ :=
  fun j => halaszNatPowerFrequency k x.1 j +
    ∑ i, (p*((x.2 i).val+1)-a)^(j.val+1)

lemma halasz_common_residue_translate {s k N Q p a : ℕ} (ha : a<p)
    (x y : (Fin k → Fin N) × (Fin s → Fin Q)) :
    halaszCommonResidueFrequency p a x = halaszCommonResidueFrequency p a y ↔
      halaszShiftedLongShortFrequency p a x = halaszShiftedLongShortFrequency p a y := by
  let v (z : (Fin k → Fin N) × (Fin s → Fin Q)) : (Fin k ⊕ Fin s) → ℕ :=
    Sum.elim (fun i => (z.1 i).val+1) (fun i => p*((z.2 i).val+1)-a)
  have hadd (z : (Fin k → Fin N) × (Fin s → Fin Q)) (i : Fin s) :
      p*((z.2 i).val+1)-a+a=p*((z.2 i).val+1) := by
    apply Nat.sub_add_cancel
    exact ha.le.trans (Nat.le_mul_of_pos_right p (by omega))
  have h := halasz_power_vector_translate_iff (k := k) (v x) (v y) a
  have hraw (z : (Fin k → Fin N) × (Fin s → Fin Q)) :
      (fun j : Fin k => ∑ i, v z i^(j.val+1)) = halaszCommonResidueFrequency p a z := by
    funext j
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      halaszCommonResidueFrequency,halaszNatPowerFrequency]
  have hshift (z : (Fin k → Fin N) × (Fin s → Fin Q)) :
      (fun j : Fin k => ∑ i, (v z i+a)^(j.val+1)) =
        halaszShiftedLongShortFrequency p a z := by
    funext j
    simp only [v,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hadd,mul_pow,
      ← mul_sum,halaszShiftedLongShortFrequency,halaszNatPowerFrequency]
  rw [hraw,hraw,hshift,hshift] at h
  exact h

lemma halasz_shifted_long_short_congruence {s k N Q : ℕ} (p a r : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin Q)) (j : Fin k) :
    (∑ i, (((X+C (a : ZMod (p^(r+1))))^(j.val+1)).eval
      (halaszLongResidues p r x i))).val % p^(min (j.val+1) (r+1)) =
        halaszShiftedLongShortFrequency p a x j % p^(min (j.val+1) (r+1)) := by
  have hcast : (∑ i, (((X+C (a : ZMod (p^(r+1))))^(j.val+1)).eval
      (halaszLongResidues p r x i))) =
      ((∑ i, ((x.1 i).val+1+a)^(j.val+1) : ℕ) : ZMod (p^(r+1))) := by
    simp only [eval_pow,eval_add,eval_X,eval_C,halaszLongResidues,Nat.cast_sum,
      Nat.cast_pow,Nat.cast_add]
  rw [hcast,ZMod.val_natCast,Nat.mod_mod_of_dvd _
    (pow_dvd_pow p (Nat.min_le_right _ _))]
  have hd : p^(min (j.val+1) (r+1)) ∣
      p^(j.val+1)*halaszNatPowerFrequency k x.2 j :=
    dvd_mul_of_dvd_left (pow_dvd_pow p (Nat.min_le_left _ _)) _
  simp only [halaszShiftedLongShortFrequency,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,
    add_zero,Nat.mod_mod]

theorem halasz_shifted_long_short_congruence_energy {s k N Q p r : ℕ} [Fact p.Prime]
    (hkp : k<p) (hrk : r+1≤k) (a : ℕ)
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszShiftedLongShortFrequency p a) ≤
      (k^k*p^((r+1)*r/2)) * halaszFiberEnergy F
        (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) := by
  apply halasz_mixed_congruence_energy_triangular hkp hrk
    (fun j => (X+C (a : ZMod (p^(r+1))))^(j.val+1))
  · intro j
    have hb : (X+C (a : ZMod (p^(r+1)))).natDegree≤1 :=
      (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le (j.val+1) hb
  · intro j
    simp only [coeff_X_add_C_pow,Nat.choose_self,Nat.sub_self,pow_zero,
      Nat.cast_one,mul_one,isUnit_one]
  · intro x hx
    simpa only [halaszLongResidues,map_natCast] using hF x hx
  · exact fun x _ j => halasz_shifted_long_short_congruence p a r x j

lemma halasz_shifted_long_short_refined_energy {s k N Q p r : ℕ}
    (hp : 0<p) (a : ℕ) (hN : N<p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q))) :
    halaszFiberEnergy F
      (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) ≤
        N^k * halaszVinogradovCount s k Q := by
  have he : halaszFiberEnergy F
      (fun x => (halaszShiftedLongShortFrequency p a x,halaszLongResidues p r x)) =
      halaszFiberEnergy F (fun x => (x.1,halaszNatPowerFrequency k x.2)) := by
    apply halasz_fiber_energy_congr
    intro x _ y _
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hf,hz⟩
      have hxy := halasz_long_residues_injective hN y x hz
      refine ⟨hxy,?_⟩
      funext j
      have hj := congrFun hf j
      simp only [halaszShiftedLongShortFrequency,hxy] at hj
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp _) (Nat.add_left_cancel hj)
    · rintro ⟨hz,hf⟩
      constructor
      · funext j
        simp only [halaszShiftedLongShortFrequency,hz,hf]
      · funext i
        simp only [halaszLongResidues,hz]
  rw [he]
  calc
    _ ≤ halaszFiberEnergy
        ((univ : Finset (Fin k → Fin N)) ×ˢ (univ : Finset (Fin s → Fin Q)))
        (fun x => (x.1,halaszNatPowerFrequency k x.2)) :=
      halasz_fiber_energy_mono (fun _ _ => mem_product.mpr ⟨mem_univ _,mem_univ _⟩) _
    _ = _ := by
      rw [halasz_fiber_energy_product,halasz_nat_power_energy]
      simp

theorem halasz_common_residue_energy {s k N Q p r a : ℕ} [Fact p.Prime]
    (hkp : k<p) (hrk : r+1≤k) (ha : a<p) (hN : N<p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszCommonResidueFrequency p a) ≤
      (k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k Q) := by
  have he : halaszFiberEnergy F (halaszCommonResidueFrequency p a) =
      halaszFiberEnergy F (halaszShiftedLongShortFrequency p a) := by
    exact halasz_fiber_energy_congr F _ _ (fun x _ y _ =>
      halasz_common_residue_translate ha y x)
  rw [he]
  exact (halasz_shifted_long_short_congruence_energy hkp hrk a F hF).trans
    (Nat.mul_le_mul_left _ (halasz_shifted_long_short_refined_energy
      (Fact.out : p.Prime).pos a hN F))

end TwoPointCorrelations

end OAI
