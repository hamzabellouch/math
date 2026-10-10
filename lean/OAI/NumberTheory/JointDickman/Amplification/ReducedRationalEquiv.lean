import OAI.NumberTheory.JointDickman.Amplification.RationalUnitRepresentatives
import Mathlib.Data.PNat.Basic

namespace OAI

/-! # Reindexing rational arcs by denominator, unit residue and integer translate -/

namespace JointDickman

abbrev ReducedRationalData := Σ q : ℕ+, (ZMod (q : ℕ))ˣ × ℤ

noncomputable def reducedRationalValue (d : ReducedRationalData) : ℚ :=
  (((d.2.1 : ZMod (d.1 : ℕ)).val : ℚ)/(d.1 : ℕ))+(d.2.2 : ℚ)

theorem reducedRationalValue_den (d : ReducedRationalData) :
    (reducedRationalValue d).den = (d.1 : ℕ) :=
  unit_fraction_add_int_den d.2.1 d.2.2

theorem reducedRationalValue_injective : Function.Injective reducedRationalValue := by
  rintro ⟨q,⟨u,k⟩⟩ ⟨q',⟨v,l⟩⟩ he
  have hq : q = q' := by
    apply Subtype.ext
    have h := congrArg Rat.den he
    rw [reducedRationalValue_den,reducedRationalValue_den] at h
    exact h
  subst q'
  have he' : ((u : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+k =
      ((v : ZMod (q : ℕ)).val : ℝ)/(q : ℕ)+l := by
    have h := congrArg (fun r : ℚ => (r : ℝ)) he
    simpa only [reducedRationalValue,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] using h
  obtain ⟨hu,hk⟩ := unit_fraction_add_int_injective u v k l he'
  subst v
  subst l
  rfl

theorem reducedRationalValue_surjective : Function.Surjective reducedRationalValue := by
  intro r
  obtain ⟨u,k,he⟩ := rational_eq_unit_fraction_add_int r
  refine ⟨⟨⟨r.den,r.pos⟩,⟨u,k⟩⟩,?_⟩
  change (((u : ZMod r.den).val : ℚ)/r.den)+(k : ℚ) = r
  apply (Rat.cast_injective (α := ℝ))
  simpa only [reducedRationalValue,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast]
    using he.symm

noncomputable def reducedRationalEquiv : ReducedRationalData ≃ ℚ :=
  Equiv.ofBijective reducedRationalValue
    ⟨reducedRationalValue_injective,reducedRationalValue_surjective⟩

end JointDickman

end OAI
