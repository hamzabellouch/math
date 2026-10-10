import Mathlib.Data.Fintype.Option
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDenominatorReduction
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertZeroVariables
import OAI.NumberTheory.PiExponent.LocalAlgebra.StabilizedColonPowers
import OAI.NumberTheory.PiExponent.Polynomials.CoordinateQuotientGrading

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem iteratedColon_eq_colon_power {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) (n : ℕ) :
    iteratedColon I f n = I.colon {f^n} := by
  induction n with
  | zero => simp only [iteratedColon_zero, PiExponentJets.W06.colon_pow_zero]
  | succ n ih => rw [iteratedColon_succ, ih, PiExponentJets.W06.colon_pow_succ]

theorem sectionHilbertSeries_rename {σ τ : Type u} [Finite σ] [Finite τ]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I =
      sectionHilbertSeries (I.map (MvPolynomial.rename e).toRingHom) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.renameQuotientSection_finrank e I n]

theorem sectionHilbertSeries_coordinate {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial (Option σ) k)) (hX : MvPolynomial.X none ∈ I) :
    sectionHilbertSeries I =
      sectionHilbertSeries (PiExponentSiegel.W08.coordinateImageIdeal I) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.coordinateQuotientSection_finrank I hX n]

theorem exists_homogeneous_hilbert_numerator
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ _ => ∀ J : Ideal (MvPolynomial τ k),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) →
      ∃ P : Polynomial ℤ, sectionHilbertSeries J =
        (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card τ)).val)
    ?_ ?_ ?_ σ I hI
  · intro α β _ e ih J hJ
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨P, hP⟩ := ih (J.map (MvPolynomial.rename e.symm).toRingHom)
      (PiExponentSiegel.W08.renameImageIdeal_homogeneous e.symm J hJ)
    refine ⟨P, ?_⟩
    rw [sectionHilbertSeries_rename e.symm J]
    simpa only [Fintype.card_congr e] using hP
  · intro J _
    exact exists_hilbert_numerator_no_variables (by simp) J
  · intro α _ ih J hJ
    let f : MvPolynomial (Option α) k := MvPolynomial.X none
    have hf : f.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X k none
    obtain ⟨m, hm⟩ := PiExponentJets.W06.exists_colon_pow_stable J f
    have hstable : iteratedColon J f (m+1) = iteratedColon J f m := by
      simpa only [iteratedColon_eq_colon_power] using hm
    let Jlower : ℕ → Ideal (MvPolynomial (Option α) k) :=
      fun j => Ideal.span {f} ⊔ iteratedColon J f j
    have hlower : ∀ j, (Jlower j).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Option α) k) := by
      intro j
      apply Ideal.IsHomogeneous.sup
      · apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option α) k)
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, hf⟩
      · exact iteratedColon_homogeneous J hJ f hf j
    have hX : ∀ j, MvPolynomial.X none ∈ Jlower j := by
      intro j
      have hinc : Ideal.span {f} ≤ Jlower j := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    choose P hP using fun j => ih (PiExponentSiegel.W08.coordinateImageIdeal (Jlower j))
      (PiExponentSiegel.W08.coordinateImageIdeal_homogeneous (Jlower j) (hlower j))
    have hseries : ∀ j, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon J f j) =
        (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card α)).val := by
      intro j
      rw [show Ideal.span {f} ⊔ iteratedColon J f j = Jlower j from rfl,
        sectionHilbertSeries_coordinate (Jlower j) (hX j)]
      exact hP j
    refine ⟨colonHilbertNumerator P m, ?_⟩
    simpa only [Fintype.card_option] using
      stabilized_colon_polynomial_numerator J hJ f hf m (Fintype.card α) hstable P hseries

end PiExponentJets.W64

end OAI
