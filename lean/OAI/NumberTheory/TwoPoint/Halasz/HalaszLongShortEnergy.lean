import OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortCongruences

namespace OAI

/-! Once the long variables agree modulo a prime power exceeding their
range, the remaining energy is the ordinary complete-system moment. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_nat_power_frequency_eq {s k N : ℕ} (x y : Fin s → Fin N) :
    halaszNatPowerFrequency k y = halaszNatPowerFrequency k x ↔
      y ∈ halaszVinogradovFiber x k := by
  rw [mem_halaszVinogradovFiber]
  constructor
  · intro h j hj
    have hj1 := (mem_Icc.mp hj).1
    have hjk := (mem_Icc.mp hj).2
    have he := congrFun h (⟨j-1,by omega⟩ : Fin k)
    simpa only [halaszNatPowerFrequency,Nat.sub_add_cancel hj1] using he.symm
  · intro h
    funext j
    exact (h (j.val+1) (mem_Icc.mpr ⟨by omega,by omega⟩)).symm

lemma halasz_nat_power_energy (s k N : ℕ) :
    halaszFiberEnergy (univ : Finset (Fin s → Fin N)) (halaszNatPowerFrequency k) =
      halaszVinogradovCount s k N := by
  rw [halasz_fiber_energy_rows,halaszVinogradovCount]
  apply sum_congr rfl
  intro x _
  congr 1
  ext y
  simp only [mem_filter,mem_univ,true_and,halasz_nat_power_frequency_eq]

lemma halasz_long_residues_injective {s k N Q p r : ℕ} (hN : N<p^(r+1))
    (x y : (Fin k → Fin N) × (Fin s → Fin Q))
    (h : halaszLongResidues p r x = halaszLongResidues p r y) : x.1=y.1 := by
  funext i
  apply Fin.ext
  have he := congrArg ZMod.val (congrFun h i)
  have hx : (x.1 i).val+1<p^(r+1) := lt_of_le_of_lt (by omega) hN
  have hy : (y.1 i).val+1<p^(r+1) := lt_of_le_of_lt (by omega) hN
  simp only [halaszLongResidues,ZMod.val_natCast_of_lt hx,
    ZMod.val_natCast_of_lt hy] at he
  omega

theorem halasz_long_short_refined_energy {s k N Q p r : ℕ}
    (hp : 0<p) (q : ℕ) (hq : 0<q) (hN : N<p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q))) :
    halaszFiberEnergy F
      (fun x => (halaszLongShortFrequency p q x,halaszLongResidues p r x)) ≤
        N^k * halaszVinogradovCount s k Q := by
  have he : halaszFiberEnergy F
      (fun x => (halaszLongShortFrequency p q x,halaszLongResidues p r x)) =
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
      simp only [halaszLongShortFrequency,hxy] at hj
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.mul_pos hp hq) _)
        (Nat.add_left_cancel hj)
    · rintro ⟨hz,hf⟩
      constructor
      · funext j
        simp only [halaszLongShortFrequency,hz,hf]
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

theorem halasz_nonsingular_long_short_energy {s k N Q p r : ℕ} [Fact p.Prime]
    (hkp : k<p) (hrk : r+1≤k) (q : ℕ) (hq : 0<q) (hN : N<p^(r+1))
    (F : Finset ((Fin k → Fin N) × (Fin s → Fin Q)))
    (hF : ∀ x∈F, Function.Injective
      (fun i => (((x.1 i).val+1:ℕ) : ZMod p))) :
    halaszFiberEnergy F (halaszLongShortFrequency p q) ≤
      (k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k Q) := by
  exact (halasz_long_short_congruence_energy hkp hrk q F hF).trans
    (Nat.mul_le_mul_left _ (halasz_long_short_refined_energy
      (Fact.out : p.Prime).pos q hq hN F))

end TwoPointCorrelations

end OAI
