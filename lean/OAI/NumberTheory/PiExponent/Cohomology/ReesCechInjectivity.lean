import OAI.NumberTheory.PiExponent.Ampleness.ReesGradedModule
import OAI.NumberTheory.PiExponent.Cohomology.GradedCech

namespace OAI

namespace PiExponent.ReesCechInjectivity
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [IsNoetherianRing R]

theorem exists_ideal_power_annihilating (I : Ideal R) (a : J → R)
    (ha : Ideal.span (Set.range a) = I) (x : R)
    (hx : ∀ j, ∃ k : ℕ, a j ^ k * x = 0) :
    ∃ k : ℕ, ∀ b ∈ I ^ k, b * x = 0 := by
  let A : Ideal R := (Ideal.span {x}).annihilator
  have hIA : I ≤ A.radical := by
    rw [← ha]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hx j
    apply Ideal.mem_radical_iff.mpr
    refine ⟨k, ?_⟩
    change a j ^ k ∈ (Submodule.span R {x}).annihilator
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using hk
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIA (IsNoetherian.noetherian I)
  refine ⟨k, ?_⟩
  intro b hb
  have h := hk hb
  change b ∈ (Submodule.span R {x}).annihilator at h
  simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using h

variable [Fintype J] [DecidableEq J] (I : Ideal R) (a : J → I)

theorem eventually_augmentation_injective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Injective
      (augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesPushdown.eventually_no_power_torsion I
  refine ⟨N, ?_⟩
  intro n hn z w hzw
  have hzero : augmentation (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  let m : reesAlgebra I := (z - w).val
  let x : R := ((m : reesAlgebra I) : Polynomial R).coeff n
  have hm : m ∈ piece I n := (z - w).property
  have heval : evaluation I m = x := evaluation_piece I ⟨m, hm⟩
  have hx : x ∈ I ^ n := m.property n
  have hloc (j : J) : ∃ k : ℕ, (a j).val ^ k * x = 0 := by
    have ht := congrArg Subtype.val (congrFun hzero (fun _ : Fin 1 => j))
    change fraction (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0 = 0 at ht
    have htuple : tupleSet (fun _ : Fin 1 => j) = {j} := by
      ext k
      simp [tupleSet, eq_comm]
    obtain ⟨k, hk⟩ := (fraction_eq_zero
      (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0).mp ht
    have hprod : coverProduct (MvPolynomial.X : J → MvPolynomial J R)
        (tupleSet (fun _ : Fin 1 => j)) = MvPolynomial.X j := by
      rw [htuple, coverProduct, Finset.prod_singleton]
    rw [hprod] at hk
    refine ⟨k, ?_⟩
    have h := congrArg (evaluation I) hk
    change evaluation I (presentation I a (MvPolynomial.X j ^ k) * m) = evaluation I 0 at h
    simpa only [map_mul, map_pow, presentation_X, evaluation_generator, heval, map_zero] using h
  have hxzero : x = 0 := hN n hn x hx (exists_ideal_power_annihilating I
    (fun j => (a j).val) ha x hloc)
  apply Subtype.ext
  apply sub_eq_zero.mp
  change m = 0
  apply Subtype.ext
  rw [(mem_piece I n m).mp hm]
  change Polynomial.monomial n x = 0
  rw [hxzero, map_zero]

end
end PiExponent.ReesCechInjectivity

end OAI
