import OAI.Algebra.OddKaplansky.SectorOrbit

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.LocalAlgebra
noncomputable section
open scoped Classical BigOperators
variable {K : Type portUniverse1} {T : Type portUniverse2} [Field K] [CommGroup T]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (hT : ∀ t : T, t^p=1)
def augment : MonoidAlgebra K T →ₐ[K] K := MonoidAlgebra.lift K K T 1
lemma augment_single (t : T) (c : K) : augment (MonoidAlgebra.single t c) = c := by simp [augment]

include hT in
lemma power_scalar (a : MonoidAlgebra K T) : a^p = algebraMap K (MonoidAlgebra K T) ((augment a)^p) := by
  let : CharP (MonoidAlgebra K T) p := CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero
  induction a using MonoidAlgebra.induction_on with
  | of t => simp [MonoidAlgebra.of_apply,MonoidAlgebra.single_pow,hT,augment_single]
  | add a b ha hb => rw [add_pow_char,ha,hb,map_add,add_pow_char,map_add]
  | smul c a ha =>
    rw [smul_pow,ha,map_smul]
    simp only [smul_eq_mul,mul_pow,map_mul,Algebra.smul_def]

include hT in
lemma isUnit_iff (a : MonoidAlgebra K T) : IsUnit a ↔ augment a ≠ 0 := by
  constructor
  · intro h; exact isUnit_iff_ne_zero.mp (h.map (augment (K := K) (T := T)))
  · intro h
    have hp : IsUnit (a^p) := by
      rw [power_scalar p hT]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ h)).map (algebraMap K (MonoidAlgebra K T))
    exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp hp

include hT in
lemma isLocal : IsLocalRing (MonoidAlgebra K T) := by
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  simp only [mem_nonunits_iff, isUnit_iff p hT,not_not] at ha hb ⊢
  rw [map_add,ha,hb,add_zero]
end
end OddKaplansky.LocalAlgebra

end

end OAI
