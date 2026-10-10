import OAI.NumberTheory.PiExponent.LocalAlgebra.ConePrimeLocalization
import OAI.NumberTheory.PiExponent.Polynomials.Homogenization

namespace OAI

noncomputable section
open scoped BigOperators

namespace PiExponentSiegel.W17.ConeLocalLength

section Scaling

variable {k B σ : Type*} [CommRing k] [CommRing B]

theorem eval₂_scale_of_isHomogeneous (F : MvPolynomial σ k) (d : ℕ)
    (hF : F.IsHomogeneous d) (c : k →+* B) (x : σ → B) (t : B) :
    MvPolynomial.eval₂ c (fun i => x i * t) F =
      MvPolynomial.eval₂ c x F * t ^ d := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hF.degree_eq_sum_deg_support hm, mul_assoc]

end Scaling

variable (k σ : Type*) [CommRing k]

private theorem coneToLaurent_scaled_eval (F : ConeRing k σ) :
    coneToLaurent k σ F =
      MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
        (fun i : Option σ =>
          LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
            (LaurentPolynomial.T 1 : LaurentChart k σ)) F := by
  have hv : (fun i : Option σ => i.elim (LaurentPolynomial.T 1 : LaurentChart k σ)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) =
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
        (LaurentPolynomial.T 1 : LaurentChart k σ)) := by
    funext i
    cases i <;> simp only [Option.elim_none, Option.elim_some, map_one, one_mul]
  change MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i : Option σ => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) F = _
  rw [hv]

private theorem laurent_eval_dehomogenize (F : ConeRing k σ) :
    MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X)) F =
      (LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) : LaurentChart k σ) :=
  (MvPolynomial.map_eval₂Hom MvPolynomial.C
    (fun i : Option σ => i.elim 1 MvPolynomial.X) LaurentPolynomial.C F).symm

theorem coneToLaurent_homogeneous (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    coneToLaurent k σ F =
      LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) *
        (LaurentPolynomial.T 1 : LaurentChart k σ) ^ d := by
  rw [coneToLaurent_scaled_eval]
  rw [eval₂_scale_of_isHomogeneous F d hF, laurent_eval_dehomogenize]

theorem coneToLaurent_homogenize (f : AffineRing k σ) :
    coneToLaurent k σ (PiExponentJets.W22.homogenize f) =
      LaurentPolynomial.C f * (LaurentPolynomial.T 1 : LaurentChart k σ) ^ f.totalDegree := by
  simpa using coneToLaurent_homogeneous k σ (PiExponentJets.W22.homogenize f)
    f.totalDegree (PiExponentJets.W22.homogenize_isHomogeneous f)

theorem map_homogenized_span_eq_laurent_span {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
      (coneToLaurent k σ) =
    (Ideal.span (Set.range f)).map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change coneToLaurent k σ (PiExponentJets.W22.homogenize (f i)) ∈
      (Ideal.span (Set.range f)).map
        (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)
    rw [coneToLaurent_homogenize]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
      (Ideal.subset_span (Set.mem_range_self i)))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (LaurentPolynomial.C (f i) : LaurentChart k σ) ∈
      (Ideal.span (Set.range (fun j => PiExponentJets.W22.homogenize (f j)))).map
        (coneToLaurent k σ)
    apply (Ideal.mul_unit_mem_iff_mem _
      ((LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).pow (f i).totalDegree)).mp
    rw [← coneToLaurent_homogenize]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem homogeneous_mem_conePrime_iff (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    F ∈ conePrime k σ P ↔ PiExponentJets.W22.dehomogenize F ∈ P := by
  change coneAwayToLaurent k σ (algebraMap (ConeRing k σ) (ConeAway k σ) F) ∈
    laurentPrime (AffineRing k σ) P ↔ _
  rw [coneAwayToLaurent_algebraMap, coneToLaurent_homogeneous k σ F d hF,
    Ideal.mul_unit_mem_iff_mem _ ((LaurentPolynomial.isUnit_T 1).pow d)]
  change PiExponentJets.W22.dehomogenize F ∈
    (laurentPrime (AffineRing k σ) P).comap (algebraMap (AffineRing k σ) (LaurentChart k σ)) ↔ _
  rw [laurentPrime_comap]

theorem homogenize_mem_conePrime_iff (f : AffineRing k σ) :
    PiExponentJets.W22.homogenize f ∈ conePrime k σ P ↔ f ∈ P := by
  simpa using homogeneous_mem_conePrime_iff k σ P
    (PiExponentJets.W22.homogenize f) f.totalDegree
    (PiExponentJets.W22.homogenize_isHomogeneous f)

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
