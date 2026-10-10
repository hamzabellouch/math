import OAI.Analysis.KadisonKastler.MatrixCentralProjection

namespace OAI

/-! # The support projection of a represented vector state

The support is the projection onto the closed commutant orbit. The orbit
construction proves its minimality and faithfulness on the supported corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutantOrbitProjection_mem (M : VonNeumannAlgebra H) (ξ : H) :
    (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection ∈ M := by
  have h : (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection ∈
      M.commutant.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (vectorOrbitProjection_commutes M.commutant.toStarSubalgebra ξ ⟨a,ha⟩).symm
  simpa only [M.commutant_commutant] using h

def vectorSupportProjection (M : VonNeumannAlgebra H) (ξ : H) : AlgebraProjection M :=
  ⟨⟨(vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection,
    commutantOrbitProjection_mem M ξ⟩,
    ⟨Subtype.ext (Submodule.isIdempotentElem_starProjection _).eq,
      Subtype.ext (isSelfAdjoint_starProjection _).star_eq⟩⟩

@[simp] theorem vectorSupportProjection_apply (M : VonNeumannAlgebra H) (ξ : H) :
    (vectorSupportProjection M ξ).val.val ξ = ξ :=
  Submodule.starProjection_eq_self_iff.mpr (mem_vectorOrbitClosure _ _)

/-- An operator killing the vector kills its supported corner. -/
theorem mul_vectorSupport_eq_zero (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val ξ = 0) :
    a.val * (vectorSupportProjection M ξ).val.val = 0 := by
  have hker : vectorOrbitClosure M.commutant.toStarSubalgebra ξ ≤ a.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro y ⟨b,rfl⟩
      change a.val (b.val ξ) = 0
      have hc := congrArg (fun T : H →L[ℂ] H => T ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp b.property a.val a.property)
      change a.val (b.val ξ) = b.val (a.val ξ) at hc
      rw [hc,ha,map_zero]
    · exact a.val.isClosed_ker
  ext η
  exact hker (Submodule.starProjection_apply_mem _ η)

theorem vectorSupport_faithful_corner (M : VonNeumannAlgebra H) (ξ : H)
    (a : Algebra M) (ha : a.val * (vectorSupportProjection M ξ).val.val = a.val)
    (hξ : a.val ξ = 0) : a = 0 := by
  apply Subtype.ext
  exact ha.symm.trans (mul_vectorSupport_eq_zero M ξ a hξ)

/-- A projection fixing the vector dominates its support. -/
theorem vectorSupport_minimal (M : VonNeumannAlgebra H) (ξ : H)
    (p : AlgebraProjection M) (hp : p.val.val ξ = ξ) :
    (vectorSupportProjection M ξ).val.val * p.val.val =
      (vectorSupportProjection M ξ).val.val := by
  have h := mul_vectorSupport_eq_zero M ξ (1 - p.val) (by
    change ξ - p.val.val ξ = 0
    rw [hp,sub_self])
  change (1 - p.val.val) * (vectorSupportProjection M ξ).val.val = 0 at h
  rw [sub_mul,one_mul,sub_eq_zero] at h
  have hs := congrArg star h
  have hpstar : star p.val.val = p.val.val :=
    congrArg (fun a : Algebra M => a.val) p.property.isSelfAdjoint.star_eq
  have hqstar : star (vectorSupportProjection M ξ).val.val =
      (vectorSupportProjection M ξ).val.val :=
    congrArg (fun a : Algebra M => a.val)
      (vectorSupportProjection M ξ).property.isSelfAdjoint.star_eq
  simpa only [star_mul, hpstar, hqstar] using hs.symm

/-- Central vectors have supports commuting with their left algebra. -/
theorem vectorSupport_commutes_of_right_vectors (M N : VonNeumannAlgebra H)
    (hNM : N ≤ M) (ξ : H)
    (hright : ∀ a : Algebra N, ∃ b : Algebra M.commutant, a.val ξ = b.val ξ)
    (a : Algebra N) :
    (vectorSupportProjection M ξ).val.val * a.val =
      a.val * (vectorSupportProjection M ξ).val.val := by
  have hinv (a : Algebra N) : ∀ y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ,
      a.val y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ := by
    apply vectorOrbitClosure_invariant_of_orbit
    intro c
    obtain ⟨b,hb⟩ := hright a
    refine ⟨c * b, ?_⟩
    have hc := congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp c.property a.val (hNM a.property))
    change a.val (c.val ξ) = c.val (a.val ξ) at hc
    simpa only [MulMemClass.coe_mul, mul_apply_eq_comp, hb] using hc
  exact starProjection_commutes_of_invariant
    (vectorOrbitClosure M.commutant.toStarSubalgebra ξ) a.val (hinv a) (by
    simpa only [StarMemClass.coe_star] using hinv (star a))

end

end KadisonKastler

end OAI
