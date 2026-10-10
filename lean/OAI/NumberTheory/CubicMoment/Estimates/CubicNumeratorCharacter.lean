import OAI.NumberTheory.CubicMoment.Estimates.ResidueProducts

namespace OAI

/-! The finite numerator character needed for arbitrary v in the
exceptional moments. The only conditional input here is the periodicity
consequence of cubic reciprocity and the unit/ramified supplementary laws:
Dunn–Radziwiłł (2024), equations (1.4)–(1.5). -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Cubic reciprocity plus its supplementary laws, specialized to
periodicity of the actual cubic symbol on primary denominators. -/
def CubicSupplementaryPeriodicity : Prop :=
  ∀ v : Eisenstein, v ≠ 0 → ∀ a b : Eisenstein,
    primary a → primary b → (9*v) ∣ a-b → cubicSymbol a v = cubicSymbol b v

def cubicNumeratorLift (v x : Eisenstein) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (modulus 3) x) then
    cubicSymbol (primaryNormalize x) v else 0

lemma cubicNumeratorLift_primary (v : Eisenstein) {x : Eisenstein} (hx : primary x) :
    cubicNumeratorLift v x = cubicSymbol x v := by
  rw [cubicNumeratorLift,ite_eq_left (unit_residue_of_dvd_primary hx (dvd_refl x)),
    primaryNormalize_eq_self hx]

lemma cubicNumeratorLift_mul (v x y : Eisenstein) :
    cubicNumeratorLift v (x*y) = cubicNumeratorLift v x*cubicNumeratorLift v y := by
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · by_cases hy : IsUnit (Ideal.Quotient.mk (modulus 3) y)
    · simp only [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx,hy,true_and,ite_true]
      rw [primaryNormalize_mul_of_residue_units hx hy,
        cubicSymbol_mul_lower (primary_ne_zero (primaryNormalize_primary hx))
          (primary_ne_zero (primaryNormalize_primary hy))]
    · simp [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx,hy]
  · simp [cubicNumeratorLift,map_mul,IsUnit.mul_iff,hx]

lemma cubicNumeratorLift_one (v : Eisenstein) : cubicNumeratorLift v 1 = 1 := by
  rw [cubicNumeratorLift_primary v primary_one,cubicSymbol_one_lower]

lemma cubicNumeratorLift_unit (v : Eisenstein) {x : Eisenstein} (hx : IsUnit x) :
    cubicNumeratorLift v x = 1 := by
  rw [cubicNumeratorLift,ite_eq_left (hx.map (Ideal.Quotient.mk (modulus 3))),
    primaryNormalize_unit hx,cubicSymbol_one_lower]

lemma cubicNumeratorLift_congr (hpub : CubicSupplementaryPeriodicity)
    {v x y : Eisenstein} (hv : v ≠ 0)
    (h : Ideal.Quotient.mk (modulus (9*v)) x = Ideal.Quotient.mk (modulus (9*v)) y) :
    cubicNumeratorLift v x = cubicNumeratorLift v y := by
  have hd : 9*v ∣ x-y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have h3d : (3:Eisenstein) ∣ 9*v := ⟨3*v,by ring⟩
  have h3 := residue_eq_of_dvd_sub (h3d.trans hd)
  by_cases hx : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · have hy : IsUnit (Ideal.Quotient.mk (modulus 3) y) := h3 ▸ hx
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hprim : primary (y*(u:Eisenstein)) := by
      apply (primary_iff_residue_one _).mpr
      rw [map_mul,← h3,← map_mul,hu]
      exact (primary_iff_residue_one _).mp (primaryNormalize_primary hx)
    have hnorm : primaryNormalize y = y*(u:Eisenstein) :=
      primary_associated_eq (primaryNormalize_primary hy) hprim
        ((primaryNormalize_associated y).symm.trans ⟨u,rfl⟩)
    simp only [cubicNumeratorLift,ite_eq_left hx,ite_eq_left hy]
    apply hpub v hv _ _ (primaryNormalize_primary hx) (primaryNormalize_primary hy)
    rw [hnorm,← hu,← sub_mul]
    exact dvd_mul_of_dvd_left hd _
  · have hy : ¬IsUnit (Ideal.Quotient.mk (modulus 3) y) := by simpa only [← h3] using hx
    simp only [cubicNumeratorLift,ite_eq_right hx,ite_eq_right hy]

lemma cubicNumeratorLift_nonunit {v x : Eisenstein}
    (hx : ¬IsUnit (Ideal.Quotient.mk (modulus (9*v)) x)) : cubicNumeratorLift v x = 0 := by
  by_cases h3 : IsUnit (Ideal.Quotient.mk (modulus 3) x)
  · rw [cubicNumeratorLift,ite_eq_left h3]
    apply cubicSymbol_eq_zero_of_not_isCoprime (primaryNormalize_primary h3)
    intro hcop
    obtain ⟨u,hu⟩ := primaryNormalize_associated x
    have hvx : IsCoprime v x := by
      rw [← hu] at hcop
      exact hcop.of_mul_left_left.symm
    have h9x : IsCoprime (9:Eisenstein) x := by
      convert (isCoprime_of_residue_isUnit h3).pow_left (m := 2) using 1
      norm_num
    exact hx (residue_isUnit_of_isCoprime (h9x.mul_left hvx))
  · simp only [cubicNumeratorLift,ite_eq_right h3]

def cubicNumeratorChar (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) : MulChar (Residues (9*v)) ℂ where
  toFun x := cubicNumeratorLift v (residueRepresentative (9*v) x)
  map_one' := by
    rw [cubicNumeratorLift_congr hpub hv (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) 1) =
        Ideal.Quotient.mk (modulus (9*v)) 1 by rw [residueRepresentative_spec,map_one])]
    exact cubicNumeratorLift_one v
  map_mul' x y := by
    rw [cubicNumeratorLift_congr hpub hv (show
      Ideal.Quotient.mk (modulus (9*v)) (residueRepresentative (9*v) (x*y)) =
        Ideal.Quotient.mk (modulus (9*v))
          (residueRepresentative (9*v) x*residueRepresentative (9*v) y) by
            rw [map_mul,residueRepresentative_spec,residueRepresentative_spec,residueRepresentative_spec])]
    exact cubicNumeratorLift_mul v _ _
  map_nonunit' x hx := cubicNumeratorLift_nonunit (by rwa [residueRepresentative_spec])

lemma cubicNumeratorChar_mk (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (x : Eisenstein) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) x) =
      cubicNumeratorLift v x := cubicNumeratorLift_congr hpub hv (residueRepresentative_spec _ _)

lemma cubicNumeratorChar_primary (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) {x : Eisenstein} (hx : primary x) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) x) = cubicSymbol x v := by
  rw [cubicNumeratorChar_mk,cubicNumeratorLift_primary v hx]

lemma cubicNumeratorChar_units (hpub : CubicSupplementaryPeriodicity)
    (v : Eisenstein) (hv : v ≠ 0) (u : Eisensteinˣ) :
    cubicNumeratorChar hpub v hv (Ideal.Quotient.mk (modulus (9*v)) u) = 1 := by
  rw [cubicNumeratorChar_mk,cubicNumeratorLift_unit v u.isUnit]

end CubicFirstMoment

end

end OAI
