import OAI.NumberTheory.Ostmann.Characters.ReducedCongruence

namespace OAI

noncomputable section
namespace Ostmann.Characters

def rawSplitConstraint (n : ℕ) (v w : ℤ) (A B P M : (ZMod n)ˣ) : Prop :=
  (v:ZMod n)*(B:ZMod n)*((P/M : (ZMod n)ˣ):ZMod n)=
    (w:ZMod n)*(A:ZMod n)*(M:ZMod n)

theorem exists_reduced_square_target (n : ℕ) [NeZero n] (v w : ℤ)
    (A B P : (ZMod n)ˣ)
    (hex : ∃ M,rawSplitConstraint n v w A B P M) :
    ∃ a : (ZMod (n/(v.natAbs.gcd n)))ˣ, ∀ M : (ZMod n)ˣ,
      rawSplitConstraint n v w A B P M →
      (ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v.natAbs n)) M)^2=a := by
  obtain ⟨M₀,hM₀⟩ := hex
  have h₀ : (v:ZMod n)*(B*(P/M₀) : (ZMod n)ˣ)=
      (w:ZMod n)*(A*M₀ : (ZMod n)ˣ) := by
    simpa only [rawSplitConstraint, Units.val_mul, mul_assoc] using hM₀
  have he := gcd_eq_of_unit_congruence n v w _ _ h₀
  let g := v.natAbs.gcd n
  let f := ZMod.unitsMap (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right v.natAbs n))
  have hv : IsUnit ((v/(g:ℤ):ℤ):ZMod (n/g)) := reduced_frequency_isUnit n v
  have hw : IsUnit ((w/(g:ℤ):ℤ):ZMod (n/g)) := by
    exact (reduce_unit_congruence n v w _ _ h₀).2.1
  refine ⟨(hw.unit*f A)⁻¹*(hv.unit*f B*f P),?_⟩
  intro M hM
  have hM' : (v:ZMod n)*(B*(P/M) : (ZMod n)ˣ)=
      (w:ZMod n)*(A*M : (ZMod n)ˣ) := by
    simpa only [rawSplitConstraint, Units.val_mul, mul_assoc] using hM
  have hc := unit_congruence_div n g
    (Nat.gcd_pos_of_pos_right _ (NeZero.pos n)) (Nat.gcd_dvd_right _ _)
    v w (Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _))
    (by rw [show g=w.natAbs.gcd n from he]; exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _))
    (B*(P/M)) (A*M) hM'
  have hu : hv.unit*f B*f (P/M)=hw.unit*f A*f M := by
    apply Units.ext
    simpa only [IsUnit.unit_spec, Units.val_mul, map_mul, mul_assoc] using hc
  exact (transfer_congruence_iff_square hv.unit hw.unit (f A) (f B)
    (f P) (f M) (f (P/M)) (by simp [map_div, mul_div_cancel])).mp hu

end Ostmann.Characters

end

end OAI
