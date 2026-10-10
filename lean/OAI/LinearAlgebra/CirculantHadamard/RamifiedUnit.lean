import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

namespace OAI

universe uR uS

/-!
# The unit factor in a ramified polynomial relation

The exact constant coefficient, together with divisibility of the other
nonleading coefficients, gives a factor with constant coefficient one.
At a root in the maximal ideal this factor is a unit.
-/

noncomputable section

namespace CirculantHadamard.RamifiedUnit

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [IsDomain R]

/-- The polynomial form of the unit factor in an Eisenstein relation. -/
theorem exists_polynomial_unit_factor (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i) :
    ∃ q : R[X], f = X ^ f.natDegree + C a * (1 + X * q) := by
  have hdvd : C a ∣ f.eraseLead := by
    apply (C_dvd_iff_dvd_coeff _ _).2
    intro i
    by_cases hi : i = f.natDegree
    · simp [eraseLead_coeff, hi]
    · rw [eraseLead_coeff_of_ne _ hi]
      by_cases hilt : i < f.natDegree
      · exact hcoeff i hilt
      · rw [coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt hilt) (Ne.symm hi))]
        exact dvd_zero a
  obtain ⟨q, hq⟩ := hdvd
  have hqzero : q.coeff 0 = 1 := by
    apply mul_left_cancel₀ ha
    have hh := congrArg (fun g : R[X] => g.coeff 0) hq
    simpa [eraseLead_coeff_of_ne _ (Nat.ne_of_lt hdeg), hzero] using hh.symm
  have hqrepr : 1 + X * q.divX = q := by
    simpa [hqzero, add_comm] using X_mul_divX_add q
  refine ⟨q.divX, ?_⟩
  calc
    f = f.eraseLead + X ^ f.natDegree := by
      simpa [hf] using (eraseLead_add_C_mul_X_pow f).symm
    _ = X ^ f.natDegree + C a * (1 + X * q.divX) := by
      rw [hq, hqrepr]
      exact add_comm _ _

variable [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A root in the maximal ideal turns the normalized polynomial factor into
a unit, and therefore expresses the constant coefficient as a unit times
the ramified power. -/
theorem exists_unit_mul_root_pow (f : R[X]) (a : R) (ha : a ≠ 0)
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hzero : f.coeff 0 = a)
    (hcoeff : ∀ i < f.natDegree, a ∣ f.coeff i)
    (z : S) (hz : z ∈ IsLocalRing.maximalIdeal S) (hroot : aeval z f = 0) :
    ∃ u : Sˣ, algebraMap R S a = (u : S) * z ^ f.natDegree := by
  obtain ⟨q, hq⟩ := exists_polynomial_unit_factor f a ha hf hdeg hzero hcoeff
  have hrel : z ^ f.natDegree + algebraMap R S a * (1 + z * aeval z q) = 0 := by
    rw [hq] at hroot
    simpa only [map_add, map_mul, map_pow, aeval_X, map_one, aeval_C] using hroot
  have hn : -(z * aeval z q) ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.maximalIdeal S).neg_mem
      ((IsLocalRing.maximalIdeal S).mul_mem_right _ hz)
  have hu : IsUnit (1 + z * aeval z q) := by
    simpa only [sub_neg_eq_add] using
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(z * aeval z q)) hn
  obtain ⟨v, hv⟩ := hu
  have hpow : z ^ f.natDegree = -(algebraMap R S a * (v : S)) := by
    rw [← hv] at hrel
    exact eq_neg_of_add_eq_zero_left hrel
  refine ⟨-v⁻¹, ?_⟩
  rw [Units.val_neg, hpow, neg_mul_neg]
  calc
    algebraMap R S a = algebraMap R S a * ((v : S) * ↑v⁻¹) := by simp
    _ = ↑v⁻¹ * (algebraMap R S a * (v : S)) := by ac_rfl

end CirculantHadamard.RamifiedUnit

end

end OAI
