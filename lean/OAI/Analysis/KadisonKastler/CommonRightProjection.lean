import OAI.Analysis.KadisonKastler.CommonRightAction
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # Right actions and the common subalgebra projection

The right action of a common unitary reduces the closed subspace generated
by the common algebra and the standard vector. Thus equality of the two
basic constructions gives the cross-commutant membership required for the
common right-action argument, without identifying the whole commutant.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugating a unitary by an involutive conjugation is unitary. -/
def conjugationUnitary (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (u : unitary (H →L[ℂ] H)) : unitary (H →L[ℂ] H) :=
  Unitary.linearIsometryEquiv.symm
    { (conjugationOperator J u).toLinearMap with
      norm_map' := by
        intro ξ
        change ‖J ((u : H →L[ℂ] H) (J ξ))‖ = ‖ξ‖
        rw [J.norm_map, Unitary.norm_map, J.norm_map]
      invFun := conjugationOperator J (star (u : H →L[ℂ] H))
      left_inv := by
        intro ξ
        change J (star (u : H →L[ℂ] H) (J (J ((u : H →L[ℂ] H) (J ξ))))) = ξ
        rw [hJ ((u : H →L[ℂ] H) (J ξ))]
        change J ((star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) (J ξ)) = ξ
        rw [Unitary.star_mul_self_of_mem u.property, one_apply_eq_self, hJ ξ]
      right_inv := by
        intro ξ
        change J ((u : H →L[ℂ] H) (J (J (star (u : H →L[ℂ] H) (J ξ))))) = ξ
        rw [hJ (star (u : H →L[ℂ] H) (J ξ))]
        change J (((u : H →L[ℂ] H) * star (u : H →L[ℂ] H)) (J ξ)) = ξ
        rw [Unitary.mul_star_self_of_mem u.property, one_apply_eq_self, hJ ξ] }

@[simp]
theorem conjugationUnitary_coe (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (u : unitary (H →L[ℂ] H)) :
    (conjugationUnitary J hJ u : H →L[ℂ] H) = conjugationOperator J u := rfl

theorem conjugationOperator_star_unitary (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (u : unitary (H →L[ℂ] H)) :
    star (conjugationOperator J u) = conjugationOperator J (star (u : H →L[ℂ] H)) := by
  let q := conjugationUnitary J hJ u
  have hi : conjugationOperator J (star (u : H →L[ℂ] H)) * (q : H →L[ℂ] H) = 1 := by
    ext ξ
    change J (star (u : H →L[ℂ] H) (J (J ((u : H →L[ℂ] H) (J ξ))))) = ξ
    rw [hJ ((u : H →L[ℂ] H) (J ξ))]
    change J ((star (u : H →L[ℂ] H) * (u : H →L[ℂ] H)) (J ξ)) = ξ
    rw [Unitary.star_mul_self_of_mem u.property, one_apply_eq_self, hJ ξ]
  change star (q : H →L[ℂ] H) = _
  calc
    star (q : H →L[ℂ] H) =
        (conjugationOperator J (star (u : H →L[ℂ] H)) * (q : H →L[ℂ] H)) *
          star (q : H →L[ℂ] H) := by rw [hi, one_mul]
    _ = conjugationOperator J (star (u : H →L[ℂ] H)) := by
      rw [mul_assoc, Unitary.mul_star_self_of_mem q.property, mul_one]

/-- A bounded operator preserving the algebra orbit also preserves its
closed linear span. -/
theorem vectorOrbitClosure_invariant_of_orbit
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (T : H →L[ℂ] H)
    (hT : ∀ x : R, ∃ y : R, T (x.val Ω) = y.val Ω)
    {ξ : H} (hξ : ξ ∈ Generator.vectorOrbitClosure R Ω) :
    T ξ ∈ Generator.vectorOrbitClosure R Ω := by
  have h : (Generator.vectorOrbitMap R Ω).range.topologicalClosure ≤
      (Generator.vectorOrbitClosure R Ω).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hT x
      exact Submodule.le_topologicalClosure _ ⟨y, hy.symm⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact h hξ

/-- Right multiplication by a common unitary commutes with the orthogonal
projection onto the common algebra's cyclic subspace. -/
theorem conjugationOperator_commute_orbitProjection
    (N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRN : R ≤ N.toStarSubalgebra) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJinv : Function.Involutive J) (Ω : H)
    (hJ : ∀ x : Algebra N, J (x.val Ω) = (star x).val Ω)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ R) :
    (Generator.vectorOrbitClosure R Ω).starProjection * conjugationOperator J u =
      conjugationOperator J u * (Generator.vectorOrbitClosure R Ω).starProjection := by
  apply Generator.starProjection_commutes_of_invariant
  · apply vectorOrbitClosure_invariant_of_orbit
    intro x
    let a : Algebra N := ⟨u, hRN hu⟩
    let b : Algebra N := ⟨x, hRN x.property⟩
    refine ⟨x * star (⟨u, hu⟩ : R), ?_⟩
    exact conjugationOperator_algebraVector N J Ω hJ a b
  · rw [conjugationOperator_star_unitary J hJinv u]
    apply vectorOrbitClosure_invariant_of_orbit
    intro x
    let a : Algebra N := ⟨star (u : H →L[ℂ] H), hRN (R.star_mem' hu)⟩
    let b : Algebra N := ⟨x, hRN x.property⟩
    refine ⟨x * (⟨u, hu⟩ : R), ?_⟩
    change conjugationOperator J (star (u : H →L[ℂ] H)) (x.val Ω) =
      (x.val * (u : H →L[ℂ] H)) Ω
    have h := conjugationOperator_algebraVector N J Ω hJ a b
    change conjugationOperator J (star (u : H →L[ℂ] H)) (x.val Ω) =
      (x.val * star (star (u : H →L[ℂ] H))) Ω at h
    simpa only [star_star] using h

/-- Equality of the two basic constructions transports a commutant member
which also commutes with their common projection. -/
theorem mem_commutant_of_equal_basicConstruction
    (M N : VonNeumannAlgebra H) (e q : H →L[ℂ] H)
    (hbasic : Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪ {e})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪ {e})))
    (hq : q ∈ N.commutant) (he : e * q = q * e) : q ∈ M.commutant := by
  have hqN : q ∈ Set.centralizer ((N : Set (H →L[ℂ] H)) ∪ {e}) := by
    intro x hx
    rcases hx with hx | hx
    · exact VonNeumannAlgebra.mem_commutant_iff.mp hq x hx
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact he
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  have hxM : x ∈ Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪ {e})) := by
    intro b hb
    exact (hb x (Or.inl hx)).symm
  rw [hbasic] at hxM
  exact (hxM q hqN).symm

/-- The basic-construction equality gives the common right action for
every unitary of the common algebra, with no description of either full
commutant required. -/
theorem common_rightAction_of_equal_basicConstruction
    (M N : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRM : R ≤ M.toStarSubalgebra) (hRN : R ≤ N.toStarSubalgebra)
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₂ : Function.Involutive J₂) (Ω : H)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω))
    (hcyclicN : DenseRange (fun x : Algebra N => x.val Ω))
    (hbasic :
      Set.centralizer (Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R Ω).starProjection})) =
      Set.centralizer (Set.centralizer ((N : Set (H →L[ℂ] H)) ∪
        {(Generator.vectorOrbitClosure R Ω).starProjection})))
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ R) :
    conjugationOperator J₁ u = conjugationOperator J₂ u := by
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector M Ω hcyclic
  · exact conjugationOperator_mem_commutant M J₁ Ω hM hcyclic ⟨u, hRM hu⟩
  · apply mem_commutant_of_equal_basicConstruction M N
      (Generator.vectorOrbitClosure R Ω).starProjection _ hbasic
    · exact conjugationOperator_mem_commutant N J₂ Ω hN hcyclicN ⟨u, hRN hu⟩
    · exact conjugationOperator_commute_orbitProjection N R hRN J₂ hJ₂ Ω hN u hu
  · exact conjugationOperator_common_vector M N J₁ J₂ Ω hM hN u (hRM hu) (hRN hu)

end

end KadisonKastler

end OAI
