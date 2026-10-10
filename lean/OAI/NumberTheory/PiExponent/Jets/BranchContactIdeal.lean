import OAI.NumberTheory.PiExponent.Jets.BranchContact
import OAI.NumberTheory.PiExponent.Jets.DVRBranch

namespace OAI

noncomputable section
namespace PiExponent.BranchContactIdeal
open IsDiscreteValuationRing

variable {A ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

def powerIdeal (z : ι → A) (e : ι → ℕ) : Ideal A :=
  Ideal.span (Set.range (fun i => z i ^ e i))

theorem powerIdeal_eq_singleton (z : ι → A) (e : ι → ℕ) (i : ι)
    (hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j)) :
    powerIdeal z e = Ideal.span {z i ^ e i} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨j,rfl⟩
    exact Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (hmin j))
  · rw [Ideal.span_le]
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact Ideal.subset_span (Set.mem_range_self i)

theorem addVal_pow_toNat {a : A} (ha : a ≠ 0) (n : ℕ) :
    (addVal A (a ^ n)).toNat = n * (addVal A a).toNat := by
  have ht : addVal A a ≠ ⊤ := addVal_eq_top_iff.not.mpr ha
  rw [(addVal A).map_pow, ← ENat.natCast_toNat ht]
  simp [nsmul_eq_mul]

variable [Fintype ι] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def contact (v : ι → ℚ) (z : ι → A) (hne : ∃ i, z i ≠ 0) : ℚ :=
  BranchContact.contact v (fun i => DVRBranch.expansion ℂ A (z i)) (by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩)

theorem exists_generator_colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ∃ i, z i ≠ 0 ∧ powerIdeal z e = Ideal.span {z i ^ e i} ∧
      ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  classical
  let a : ι → PowerSeries ℂ := fun i => DVRBranch.expansion ℂ A (z i)
  have han : ∃ i, a i ≠ 0 := by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩
  obtain ⟨i,hi,hatt⟩ := BranchContact.exists_attains v a han
  have hzi : z i ≠ 0 := fun hz => hi (by simp [a,hz])
  have hival : (contact v z hne) * v i = ((addVal A (z i)).toNat : ℚ) := by
    have h := (eq_div_iff (ne_of_gt (hv i))).mp hatt
    simpa only [contact, a, DVRBranch.expansion_order] using h
  have hiR : ((addVal A (z i ^ e i)).toNat : ℚ) = R * contact v z hne := by
    rw [addVal_pow_toNat hzi, Nat.cast_mul, ← hival, ← he i]
    ring
  have hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j) := by
    intro j
    by_cases hzj : z j = 0
    · by_cases hej : e j = 0
      · have hR : R = 0 := by simpa [hej] using (he j).symm
        have hi0 : e i = 0 := by
          have hh := he i
          rw [hR, mul_eq_zero] at hh
          exact_mod_cast hh.resolve_left (ne_of_gt (hv i))
        simp [hej,hi0]
      · simp [hzj,zero_pow hej]
    · have haj : a j ≠ 0 := (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hzj
      have hb := BranchContact.contact_bound v hv a han j (a j).order.toNat
        (PowerSeries.coe_toNat_order haj).symm
      have hb' : contact v z hne * v j ≤ ((addVal A (z j)).toNat : ℚ) := by
        simpa only [contact, a, DVRBranch.expansion_order] using hb
      have hrat : ((addVal A (z i ^ e i)).toNat : ℚ) ≤
          ((addVal A (z j ^ e j)).toNat : ℚ) := by
        rw [hiR, addVal_pow_toNat hzj, Nat.cast_mul, ← he j]
        nlinarith [mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg (e j) : (0:ℚ) ≤ e j)]
      have hnat : (addVal A (z i ^ e i)).toNat ≤ (addVal A (z j ^ e j)).toNat := by
        exact_mod_cast hrat
      rw [← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzi)),
        ← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzj))]
      exact_mod_cast hnat
  have heq := powerIdeal_eq_singleton z e i hmin
  refine ⟨i,hzi,heq,?_⟩
  rw [heq, CurveLocalOrder.length_quotient_span_eq_addVal (pow_ne_zero _ hzi)]
  exact hiR

theorem colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  obtain ⟨_,_,_,h⟩ := exists_generator_colength_eq_contact v hv z hne R e he
  exact h

end PiExponent.BranchContactIdeal

end

end OAI
