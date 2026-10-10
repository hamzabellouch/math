import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.Coordinates
import OAI.AlgebraicGeometry.RelativeTriviality.Charts

namespace OAI

namespace CampanaPeternellSix.RelativeLineGlobalFunctions
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped Polynomial LaurentPolynomial
open RelativeLineCharts
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma laurent_coeff_nat (p : R[X]) (n : ℕ) : p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

lemma laurent_coeff_neg (p : R[X]) (n : ℕ) (hn : 0 < n) :
    p.toLaurent.coeff (-(n : ℤ)) = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  change (i : ℤ) = -(n : ℤ) at hi
  omega

lemma polynomial_overlap_constants (p q : R[X])
    (h : p.toLaurent = LaurentPolynomial.invert q.toLaurent) :
    ∃ a : R, p = Polynomial.C a ∧ q = Polynomial.C a := by
  have hc : p.coeff 0 = q.coeff 0 := by
    have := congrArg (fun z : R[T;T⁻¹] => z.coeff 0) h
    change p.toLaurent.coeff (↑(0 : ℕ)) = (LaurentPolynomial.invert q.toLaurent).coeff (↑(0 : ℕ)) at this
    rw [laurent_coeff_nat, LaurentPolynomial.invert_apply] at this
    rw [Nat.cast_zero, neg_zero] at this
    exact this.trans (laurent_coeff_nat R q 0)
  have cp : p = Polynomial.C (p.coeff 0) := by
    ext k
    by_cases hk : k = 0
    · subst k; simp
    · have he := congrArg (fun z : R[T;T⁻¹] => z.coeff (k : ℤ)) h
      rw [laurent_coeff_nat, LaurentPolynomial.invert_apply,
        laurent_coeff_neg R q k (Nat.pos_of_ne_zero hk)] at he
      simpa only [Polynomial.coeff_C, ite_eq_right hk] using he
  have cq : q = Polynomial.C (q.coeff 0) := by
    ext k
    by_cases hk : k = 0
    · subst k; simp
    · have he := congrArg (fun z : R[T;T⁻¹] => z.coeff (-(k : ℤ))) h
      rw [laurent_coeff_neg R p k (Nat.pos_of_ne_zero hk),
        LaurentPolynomial.invert_apply, neg_neg, laurent_coeff_nat] at he
      simpa only [Polynomial.coeff_C, ite_eq_right hk] using he.symm
  exact ⟨p.coeff 0, cp, by simpa [hc] using cq⟩

def scalars : R →+* Γ(RelativePolynomialEvaluation.space R 1, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (RelativePolynomialEvaluation.toBase R 1).appTop).hom

lemma scalars_restrict_X (i : Fin 2) (a : R) :
    (scheme R).presheaf.map (homOfLE (show Proj.basicOpen (grading R) (MvPolynomial.X i) ≤ ⊤ from le_top)).op
        (scalars R a) =
      Proj.awayToSection (grading R) (MvPolynomial.X i)
        (HomogeneousLocalization.fromZeroRingHom (grading R) _ (constants R a)) := by
  apply Subtype.ext
  funext p
  apply HomogeneousLocalization.val_injective
  change ((((Scheme.ΓSpecIso (.of R)).inv ≫
    (RelativePolynomialEvaluation.toBase R 1).appTop) a).val ⟨p.1, trivial⟩).val = _
  rw [RelativePolynomialEvaluation.toBase_section R 1 a p.1]
  rfl

lemma scalars_left (a : R) :
    leftSectionEquiv R ((scheme R).presheaf.map (homOfLE le_top : leftOpen R ⟶ ⊤).op
      (scalars R a)) = Polynomial.C a := by
  refine (congrArg (leftSectionEquiv R) (scalars_restrict_X R 0 a)).trans ?_
  change chartEquiv R ((leftSectionsIso R).inv ((leftSectionsIso R).hom
    (algebraMap R (ChartRing R) a))) = _
  simpa using chartEquiv_constant R a

lemma scalars_right (a : R) :
    rightSectionEquiv R ((scheme R).presheaf.map (homOfLE le_top : rightOpen R ⟶ ⊤).op
      (scalars R a)) = Polynomial.C a := by
  refine (congrArg (rightSectionEquiv R) (scalars_restrict_X R 1 a)).trans ?_
  change rightChartEquiv R ((rightSectionsIso R).inv ((rightSectionsIso R).hom
    (HomogeneousLocalization.fromZeroRingHom (grading R) _ (constants R a)))) = _
  simp only [Iso.hom_inv_id_apply]
  rw [← chartSwap_constant R a]
  change chartEquiv R ((chartSwap R).symm ((chartSwap R) (algebraMap R (ChartRing R) a))) = _
  rw [RingEquiv.symm_apply_apply, chartEquiv_constant]

lemma polynomial_restrictions_agree (s : Γ(scheme R, ⊤)) :
    (leftSectionEquiv R ((scheme R).presheaf.map
      (homOfLE le_top : leftOpen R ⟶ ⊤).op s)).toLaurent =
    LaurentPolynomial.invert (rightSectionEquiv R ((scheme R).presheaf.map
      (homOfLE le_top : rightOpen R ⟶ ⊤).op s)).toLaurent := by
  rw [← (standard_section_restrictions R).1, ← (standard_section_restrictions R).2]
  congr 1

theorem scalars_bijective : Function.Bijective (scalars R) := by
  constructor
  · intro a b h
    apply Polynomial.C_injective (R := R)
    have he := congrArg (fun s => leftSectionEquiv R ((scheme R).presheaf.map
      (homOfLE le_top : leftOpen R ⟶ ⊤).op s)) h
    exact (scalars_left R a).symm.trans (he.trans (scalars_left R b))
  · intro s
    obtain ⟨a, ha, hb⟩ := polynomial_overlap_constants R _ _
      (polynomial_restrictions_agree R s)
    refine ⟨a, ?_⟩
    refine (scheme R).sheaf.eq_of_locally_eq₂
      (homOfLE le_top : leftOpen R ⟶ ⊤) (homOfLE le_top : rightOpen R ⟶ ⊤)
      (by rw [standard_cover R]) _ _ ?_ ?_
    · apply (leftSectionEquiv R).injective
      exact (scalars_left R a).trans ha.symm
    · apply (rightSectionEquiv R).injective
      exact (scalars_right R a).trans hb.symm
end
end CampanaPeternellSix.RelativeLineGlobalFunctions

end OAI
