import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovJacobian

namespace OAI

/-! A split polynomial with distinct roots modulo p has no additional
roots modulo a power of p. This is the uniqueness part needed in the
nonsingular congruence count. -/
namespace TwoPointCorrelations

open Finset

noncomputable def halaszPrimePowerReduction (p r : ℕ) :
    ZMod (p^(r+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : r+1≠0)) (ZMod p)

lemma halasz_prime_power_unit_iff {p r : ℕ} [Fact p.Prime] (z : ZMod (p^(r+1))) :
    IsUnit z ↔ halaszPrimePowerReduction p r z≠0 := by
  have hp : p.Prime := Fact.out
  have : NeZero (p^(r+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hz : (z.val : ZMod (p^(r+1))) = z := ZMod.natCast_zmod_val z
  calc
    IsUnit z ↔ IsUnit (z.val : ZMod (p^(r+1))) := by rw [hz]
    _ ↔ ¬p∣z.val := ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)
    _ ↔ halaszPrimePowerReduction p r z≠0 := by
      have he : halaszPrimePowerReduction p r z = (z.val:ZMod p) := by
        calc
          _ = halaszPrimePowerReduction p r (z.val:ZMod (p^(r+1))) := congrArg _ hz.symm
          _ = _ := map_natCast _ _
      rw [he]
      exact (ZMod.natCast_eq_zero_iff _ _).not.symm

theorem halasz_prime_power_split_roots {p r k : ℕ} [Fact p.Prime]
    (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (z : ZMod (p^(r+1))) (hz : ∏ i, (z-x i)=0) : ∃ i, z=x i := by
  classical
  let φ := halaszPrimePowerReduction p r
  have hred : ∏ i, (φ z-φ (x i))=0 := by
    simpa only [map_prod,map_sub,map_zero] using congrArg φ hz
  obtain ⟨i,_,hi⟩ := prod_eq_zero_iff.mp hred
  have hi' : φ z=φ (x i) := sub_eq_zero.mp hi
  have hu : IsUnit (∏ j ∈ (univ:Finset (Fin k)).erase i, (z-x j)) := by
    apply IsUnit.prod_iff.mpr
    intro j hj
    apply (halasz_prime_power_unit_iff _).mpr
    change φ (z-x j)≠0
    rw [map_sub,hi',sub_ne_zero]
    intro he
    exact (mem_erase.mp hj).1 (hx he).symm
  have hfactor : (z-x i)*(∏ j ∈ (univ:Finset (Fin k)).erase i, (z-x j))=0 := by
    rw [mul_prod_erase univ (fun j => z-x j) (mem_univ i)]
    exact hz
  exact ⟨i,sub_eq_zero.mp (hu.mul_left_eq_zero.mp hfactor)⟩

end TwoPointCorrelations

end OAI
