import OAI.AlgebraicGeometry.StableCoordinate.FilteredReesDerivation
import OAI.AlgebraicGeometry.StableCoordinate.FiltrationDerivationShift
import OAI.AlgebraicGeometry.StableCoordinate.CoordinateDerivation

namespace OAI

/-!
# A coordinate system produces a leading locally nilpotent derivation

This is the first half of the source's coordinate obstruction, through the
construction of a nonzero homogeneous locally nilpotent derivation on the
actual associated graded ring.  Its distinguished invariant has negative
degree; its second invariant has strictly positive degree and is nonzero.
The derivation and its shift are constructed, not postulated.
-/

namespace StableCoordinate.FilteredRees

open MvPolynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The degree-at-most-zero part of a multiplicative integer filtration is a
subalgebra. -/
def degreeZeroSubalgebra (F : ℤ → Submodule k A) [SetLike.GradedMonoid F] :
    Subalgebra k A where
  carrier := F 0
  zero_mem' := (F 0).zero_mem
  one_mem' := SetLike.one_mem_graded F
  add_mem' := (F 0).add_mem
  mul_mem' ha hb := by
    change _ ∈ F 0
    exact SetLike.mul_mem_graded ha hb
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (F 0).smul_mem r (SetLike.one_mem_graded F)

@[simp] theorem mem_degreeZeroSubalgebra
    (F : ℤ → Submodule k A) [SetLike.GradedMonoid F] (a : A) :
    a ∈ degreeZeroSubalgebra F ↔ a ∈ F 0 := Iff.rfl

/-- A nonzero positive-degree initial form witnesses that the degree-zero
subalgebra is proper.  This lets a presentation of the graded ring supply the
properness input without a separate argument about coordinates. -/
theorem degreeZeroSubalgebra_ne_top_of_initial_ne_zero
    (F : ℤ → Submodule k A) [SetLike.GradedMonoid F] (hmono : Monotone F)
    {d : ℤ} (hd : 0 < d) (a : F d)
    (ha : initial F hmono d a ≠ 0) : degreeZeroSubalgebra F ≠ ⊤ := by
  intro htop
  have ha0 : (a : A) ∈ F 0 := by
    change (a : A) ∈ degreeZeroSubalgebra F
    rw [htop]
    trivial
  exact ha ((initial_eq_zero_iff F hmono d a).mpr
    (hmono (by omega : 0 ≤ d - 1) ha0))

/-- A nonzero locally nilpotent derivation on a separated five-generator
presentation has an actual nonzero homogeneous leading derivation.  All
invariant initial forms remain invariant. -/
theorem exists_leading_lnd
    (φ : MvPolynomial (Fin 5) k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hsep : (⨅ d : ℤ, Filtration.imagePiece φ d) = ⊥)
    (D : Derivation k A A) (hD : D ≠ 0)
    (hln : ∀ a, ∃ n : ℕ, ((D : A → A)^[n]) a = 0) :
    ∃ (m : ℤ) (δ : Derivation k
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))),
      δ ≠ 0 ∧
      (∀ a, ∃ n : ℕ, ((δ : _ → _)^[n]) a = 0) ∧
      (∀ (d : ℤ) (a : Filtration.imagePiece φ d),
        ∃ b : Filtration.imagePiece φ (d + m),
          δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (d + m) b) ∧
      (∀ (d : ℤ) (a : Filtration.imagePiece φ d),
        D a = 0 → δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = 0) := by
  obtain ⟨m, i, _, _, hDi, hshift⟩ :=
    Filtration.exists_attained_derivation_imagePiece_shift φ hφ hsep D hD
  let shift : ∀ d (a : A), a ∈ Filtration.imagePiece φ d →
      D a ∈ Filtration.imagePiece φ (d + m) := fun d a ha => hshift d ha
  refine ⟨m, gradedDerivation _ D m shift (Filtration.imagePiece_mono φ), ?_,
    gradedDerivation_locallyNilpotent _ D m shift _ hln, ?_, ?_⟩
  · exact gradedDerivation_ne_zero _ D m shift _
      (Filtration.monomialWeight (Finsupp.single i 1))
      ⟨φ (X i), Filtration.image_monomial_mem φ (Finsupp.single i 1) 1⟩ hDi
  · intro d a
    exact ⟨⟨D a, shift d a a.property⟩,
      gradedDerivation_initial _ D m shift _ d a⟩
  · intro d a ha
    exact gradedDerivation_initial_eq_zero _ D m shift _ d a ha

/-- A nonzero element outside the degree-zero part has a nonzero initial form
of strictly positive integer degree. -/
theorem exists_positive_initial
    (F : ℤ → Submodule k A) [SetLike.GradedMonoid F] (hmono : Monotone F)
    (hext : ∀ a : A, ∃ d : ℤ, a ∈ F d) (hsep : (⨅ d : ℤ, F d) = ⊥)
    {a : A} (ha : a ∉ F 0) :
    ∃ (d : ℤ) (hd : a ∈ F d), 0 < d ∧
      initial F hmono d ⟨a, hd⟩ ≠ 0 := by
  have hane : a ≠ 0 := by
    intro h
    exact ha (h ▸ (F 0).zero_mem)
  obtain ⟨d, hd, hprev⟩ := IntegerFiltration.exists_initial_index
    (fun d => (F d : Set A)) (fun _ _ h => hmono h) hext
    (IntegerFiltration.separated_of_iInf_eq_bot F hsep) hane
  have hdpos : 0 < d := by
    by_contra hn
    exact ha (hmono (by omega : d ≤ 0) hd)
  exact ⟨d, hd, hdpos, fun h => hprev ((initial_eq_zero_iff F hmono d _).mp h)⟩

/-- The first obstruction step for a polynomial coordinate system containing
the distinguished negative-weight generator.  It supplies, on the actual
Rees associated graded ring, a nonzero homogeneous locally nilpotent derivation
annihilating that generator's initial form and a nonzero positive-degree
initial form. -/
theorem coordinate_produces_leading_lnd
    [Nontrivial A]
    (φ : MvPolynomial (Fin 5) k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hsep : (⨅ d : ℤ, Filtration.imagePiece φ d) = ⊥)
    (hproper : degreeZeroSubalgebra (Filtration.imagePiece φ) ≠ ⊤)
    (e : MvPolynomial (Fin 4) k ≃ₐ[k] A) (hp : e (X 0) = φ (X 0)) :
    ∃ (m : ℤ) (δ : Derivation k
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))),
      δ ≠ 0 ∧
      (∀ a, ∃ n : ℕ, ((δ : _ → _)^[n]) a = 0) ∧
      (∀ (d : ℤ) (a : Filtration.imagePiece φ d),
        ∃ b : Filtration.imagePiece φ (d + m),
          δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (d + m) b) ∧
      δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (-1)
        ⟨φ (X 0), Filtration.image_X_zero_mem_neg_one φ⟩) = 0 ∧
      ∃ (d : ℤ) (a : Filtration.imagePiece φ d), 0 < d ∧
        initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a ≠ 0 ∧ δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = 0 := by
  have hp0 : e (X 0) ∈ degreeZeroSubalgebra (Filtration.imagePiece φ) := by
    rw [hp]
    exact Filtration.imagePiece_mono φ (by decide : (-1 : ℤ) ≤ 0)
      (Filtration.image_X_zero_mem_neg_one φ)
  obtain ⟨D, hD, hln, hDp, j, _, hj, hDj⟩ :=
    CoordinateDerivation.exists_lnd_invariant_outside (by decide : 2 < 4)
      e (degreeZeroSubalgebra (Filtration.imagePiece φ)) hproper 0 hp0
  obtain ⟨m, δ, hδ, hδln, hhom, hinv⟩ := exists_leading_lnd φ hφ hsep D hD hln
  obtain ⟨d, hd, hdpos, hinit⟩ := exists_positive_initial
    (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ)
    (Filtration.exists_mem_imagePiece φ hφ) hsep hj
  refine ⟨m, δ, hδ, hδln, hhom, ?_, d, ⟨e (X j), hd⟩, hdpos, hinit, ?_⟩
  · apply hinv
    simpa only [hp] using hDp
  · exact hinv d ⟨e (X j), hd⟩ hDj

/-- In the noetherian-domain source setting, separation is a proved consequence
of the nonunit negative-weight generator, not an extra obstruction assumption. -/
theorem coordinate_produces_leading_lnd_of_nonunit
    [IsNoetherianRing A] [IsDomain A]
    (φ : MvPolynomial (Fin 5) k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hpunit : ¬ IsUnit (φ (X 0)))
    (hproper : degreeZeroSubalgebra (Filtration.imagePiece φ) ≠ ⊤)
    (e : MvPolynomial (Fin 4) k ≃ₐ[k] A) (hp : e (X 0) = φ (X 0)) :
    ∃ (m : ℤ) (δ : Derivation k
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))),
      δ ≠ 0 ∧
      (∀ a, ∃ n : ℕ, ((δ : _ → _)^[n]) a = 0) ∧
      (∀ (d : ℤ) (a : Filtration.imagePiece φ d),
        ∃ b : Filtration.imagePiece φ (d + m),
          δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (d + m) b) ∧
      δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (-1)
        ⟨φ (X 0), Filtration.image_X_zero_mem_neg_one φ⟩) = 0 ∧
      ∃ (d : ℤ) (a : Filtration.imagePiece φ d), 0 < d ∧
        initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a ≠ 0 ∧ δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = 0 :=
  coordinate_produces_leading_lnd φ hφ
    (Filtration.iInf_imagePiece_eq_bot φ hpunit) hproper e hp

/-- When coordinates are supplied, the noetherian-domain and nonunit facts
required for separation follow from that coordinate equivalence.  Thus the
only filtration input still needed is properness of its degree-zero part,
which the graded-presentation theorem supplies. -/
theorem coordinate_produces_leading_lnd_of_noetherian_domain
    [IsNoetherianRing k] [IsDomain k]
    (φ : MvPolynomial (Fin 5) k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hproper : degreeZeroSubalgebra (Filtration.imagePiece φ) ≠ ⊤)
    (e : MvPolynomial (Fin 4) k ≃ₐ[k] A) (hp : e (X 0) = φ (X 0)) :
    ∃ (m : ℤ) (δ : Derivation k
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))
      (Gr (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ))),
      δ ≠ 0 ∧
      (∀ a, ∃ n : ℕ, ((δ : _ → _)^[n]) a = 0) ∧
      (∀ (d : ℤ) (a : Filtration.imagePiece φ d),
        ∃ b : Filtration.imagePiece φ (d + m),
          δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) =
            initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (d + m) b) ∧
      δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) (-1)
        ⟨φ (X 0), Filtration.image_X_zero_mem_neg_one φ⟩) = 0 ∧
      ∃ (d : ℤ) (a : Filtration.imagePiece φ d), 0 < d ∧
        initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a ≠ 0 ∧
        δ (initial (Filtration.imagePiece φ) (Filtration.imagePiece_mono φ) d a) = 0 := by
  let : IsDomain A := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  let : IsNoetherianRing A :=
    isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 4) k) e.toRingEquiv
  have hpunit : ¬ IsUnit (φ (X 0)) := by
    intro hu
    have hX : IsUnit (X (0 : Fin 4) : MvPolynomial (Fin 4) k) := by
      have hu' := hu.map e.symm
      simpa only [← hp, AlgEquiv.symm_apply_apply] using hu'
    exact not_isUnit_zero (by simpa only [eval_X] using hX.map (eval (fun _ => (0 : k))))
  exact coordinate_produces_leading_lnd_of_nonunit φ hφ hpunit hproper e hp

end StableCoordinate.FilteredRees

end OAI
