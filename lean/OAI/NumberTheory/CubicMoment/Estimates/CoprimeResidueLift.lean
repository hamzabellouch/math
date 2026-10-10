import OAI.NumberTheory.CubicMoment.Estimates.ConductorLocal

namespace OAI

/-! Lift a prime-to-modulus residue while avoiding any prescribed nonzero
factor. This keeps the actual cubic-character witness away from the cube
part of its numerator. -/
noncomputable section
namespace CubicFirstMoment

lemma isCoprime_of_residue_congr {q x y : Eisenstein}
    (hxy : q ∣ x-y) (hy : IsCoprime q y) : IsCoprime q x := by
  apply isCoprime_of_residue_isUnit
  rw [residue_eq_of_dvd_sub hxy]
  exact residue_isUnit_of_isCoprime hy

/-- Every residue prime to `q` has a representative prime to `q*c`. -/
theorem exists_coprime_residue_lift {q a c : Eisenstein}
    (hc : c ≠ 0) (ha : IsCoprime q a) :
    ∃ x : Eisenstein, q ∣ x-a ∧ IsCoprime (q*c) x := by
  have H : ∀ c : Eisenstein, c ≠ 0 →
      ∃ x : Eisenstein, q ∣ x-a ∧ IsCoprime (q*c) x := by
    intro c
    refine UniqueFactorizationMonoid.induction_on_prime c ?_ ?_ ?_
    · intro h
      exact (h rfl).elim
    · intro u hu _
      exact ⟨a,by simp,(isCoprime_mul_unit_right_left hu q a).mpr ha⟩
    · intro b p hb hp ih _
      obtain ⟨y,hy,hcop⟩ := ih hb
      by_cases hpq : p ∣ q
      · refine ⟨y,hy,?_⟩
        have hpy := hcop.of_mul_left_left.of_isCoprime_of_dvd_left hpq
        simpa only [mul_left_comm q p b] using hpy.mul_left hcop
      · by_cases hpb : p ∣ b
        · refine ⟨y,hy,?_⟩
          have hpy := hcop.of_mul_left_right.of_isCoprime_of_dvd_left hpb
          simpa only [mul_left_comm q p b] using hpy.mul_left hcop
        · have hpqb : IsCoprime (q*b) p :=
            ((hp.coprime_iff_not_dvd.mpr hpq).mul_right
              (hp.coprime_iff_not_dvd.mpr hpb)).symm
          obtain ⟨x,hxy,hxp⟩ := residue_crt_one hpqb y
          refine ⟨x,?_,?_⟩
          · have hqx : q ∣ x-y := (dvd_mul_right q b).trans hxy
            convert dvd_add hqx hy using 1
            ring
          · have hcop' := isCoprime_of_residue_congr hxy hcop
            have hpx := isCoprime_of_dvd_sub_one hxp
            simpa only [mul_left_comm q p b] using hpx.mul_left hcop'
  exact H c hc

end CubicFirstMoment

end

end OAI
