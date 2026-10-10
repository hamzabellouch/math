import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaLattice

namespace OAI

/-! The complete Eisenstein theta sum, including its zero term, equals the
ideal theta sum with its exact unit multiplicity. -/
noncomputable section
namespace CubicFirstMoment

def residueLatticeTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (A t : ℝ) : ℂ :=
  ∑' a : Eisenstein, χ (Ideal.Quotient.mk (modulus q) a)*(Real.exp (-norm a*t/A):ℝ)

lemma residueLatticeTheta_eq {q : Eisenstein} (hq : q ≠ 0)
    [Nontrivial (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    residueLatticeTheta q χ A t =
      (Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q χ) t := by
  rw [← idealTheta_lattice hq χ hu hA ht]
  symm
  unfold residueLatticeTheta
  exact tsum_subtype_eq_of_support_subset (s := {a : Eisenstein | a ≠ 0})
    (f := fun a : Eisenstein => χ (Ideal.Quotient.mk (modulus q) a)*(Real.exp (-norm a*t/A):ℝ)) (by
    intro a ha
    by_contra he
    have hz : a = 0 := not_not.mp he
    subst a
    simp only [Function.mem_support,map_zero,MulChar.map_zero,zero_mul,ne_eq,not_true_eq_false] at ha)

lemma residue_nontrivial_of_nonprincipal {q : Eisenstein} (χ : MulChar (Residues q) ℂ)
    (hn : χ ≠ 1) : Nontrivial (Residues q) := by
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hn
  apply nontrivial_of_ne (u : Residues q) 1
  intro he
  apply hu
  rw [he,map_one]

lemma residueTheta_unit_multiplicity_ne_zero : (Nat.card (Eisensteinˣ):ℂ) ≠ 0 := by
  let : Finite (Eisensteinˣ) := idealTheta_units_finite
  exact_mod_cast Nat.card_pos.ne'

lemma residueTheta_inversion_of_lattice {q : Eisenstein} (hq : q ≠ 0)
    [Nontrivial (Residues q)] (χ : MulChar (Residues q) ℂ)
    (hu : ∀ u : Eisensteinˣ, χ (Ideal.Quotient.mk (modulus q) u) = 1)
    (hd : ∀ u : Eisensteinˣ, (star χ) (Ideal.Quotient.mk (modulus q) u) = 1)
    {A : ℝ} (hA : 0 < A) {root : ℂ}
    (hFE : ∀ t : ℝ, 0 < t → residueLatticeTheta q χ A (1/t) =
      root*(t:ℂ)*residueLatticeTheta q (star χ) A t) :
    ∀ t : ℝ, 0 < t → idealTheta A (residueIdealChar q χ) (1/t) =
      root*(t:ℂ)*idealTheta A (residueIdealChar q (star χ)) t := by
  intro t ht
  have h := hFE t ht
  rw [residueLatticeTheta_eq hq χ hu hA (one_div_pos.mpr ht),
    residueLatticeTheta_eq hq (star χ) hd hA ht] at h
  apply mul_left_cancel₀ residueTheta_unit_multiplicity_ne_zero
  calc
    _ = root*(t:ℂ)*((Nat.card (Eisensteinˣ):ℂ)*idealTheta A (residueIdealChar q (star χ)) t) := h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
