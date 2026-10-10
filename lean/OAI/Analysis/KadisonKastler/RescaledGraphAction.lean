import OAI.Analysis.KadisonKastler.RescaledGraphSignal
import OAI.Analysis.KadisonKastler.ProductBoundaryCocycle

namespace OAI

/-! # The common unitary action on rescaled graphs

Left and right multiplication by common unitaries acts on graph vectors
through one unitary of the fixed two-coordinate Hilbert space. Thus each
closed graph reduces this unitary whenever the right action belongs to
the relevant commutant and has the prescribed value on the common vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Two unitary coordinate actions form an actual Hilbert-space unitary. -/
def graphDiagonalUnitary (u v : unitary (H →L[ℂ] H)) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => Unitary.linearIsometryEquiv (if i = 0 then u else v)))

@[simp] theorem graphDiagonalUnitary_apply_zero
    (u v : unitary (H →L[ℂ] H)) (ξ : TomitaGraphHilbert H) :
    (graphDiagonalUnitary u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ 0 =
      (u : H →L[ℂ] H) (ξ 0) := by
  change (Unitary.linearIsometryEquiv (if (0 : Fin 2) = 0 then u else v)) (ξ 0) = _
  rw [ite_eq_left rfl]
  rfl

@[simp] theorem graphDiagonalUnitary_apply_one
    (u v : unitary (H →L[ℂ] H)) (ξ : TomitaGraphHilbert H) :
    (graphDiagonalUnitary u v : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ 1 =
      (v : H →L[ℂ] H) (ξ 1) := by
  change (Unitary.linearIsometryEquiv (if (1 : Fin 2) = 0 then u else v)) (ξ 1) = _
  rw [ite_eq_right (by decide)]
  rfl

/-- The common graph action implementing `x ↦ r*x*s`. -/
def rescaledGraphAction (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (r s : unitary (H →L[ℂ] H)) :
    unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
  graphDiagonalUnitary (r * conjugationUnitary J hJ (star s))
    (conjugationUnitary J hJ ((star s) * conjugationUnitary J hJ r))

private theorem right_operator_on_algebra_vector
    (P : VonNeumannAlgebra H) (Ω : H) (a b : H →L[ℂ] H)
    (ha : a ∈ P.commutant) (x : Algebra P) (hΩ : a Ω = b Ω) :
    a (x.val Ω) = x.val (b Ω) := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp ha x.val x.property
  calc
    a (x.val Ω) = x.val (a Ω) :=
      (congrArg (fun T : H →L[ℂ] H => T Ω) hc).symm
    _ = x.val (b Ω) := by rw [hΩ]

/-- Exact action on graph vectors, before any closure argument. -/
theorem rescaledGraphAction_vector
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (c : ℝ) (r s : unitary (H →L[ℂ] H))
    (hsright : conjugationOperator J (star (s : H →L[ℂ] H)) ∈ P.commutant)
    (hrright : conjugationOperator J (r : H →L[ℂ] H) ∈ P.commutant)
    (hsΩ : conjugationOperator J (star (s : H →L[ℂ] H)) Ω = (s : H →L[ℂ] H) Ω)
    (hrΩ : conjugationOperator J (r : H →L[ℂ] H) Ω = star (r : H →L[ℂ] H) Ω)
    (x : Algebra P) :
    (rescaledGraphAction J hJ r s :
      TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
      (rescaledGraphVector J Ω c x.val) =
        rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 0 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 0
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_zero,
      rescaledGraphVector_zero, Submonoid.coe_mul, mul_apply_eq_comp,
      conjugationUnitary_coe, Unitary.coe_star]
    rw [right_operator_on_algebra_vector P Ω _ _ hsright x hsΩ]
  · change (rescaledGraphAction J hJ r s :
        TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) 1 =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) 1
    simp only [rescaledGraphAction, graphDiagonalUnitary_apply_one,
      rescaledGraphVector_one, conjugationUnitary_coe]
    rw [LinearMapClass.map_smul_of_tower]
    congr 1
    change J (star (s : H →L[ℂ] H)
      (conjugationOperator J (r : H →L[ℂ] H) (J (J (star x.val Ω))))) =
        J (star ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) Ω)
    rw [hJ]
    have hc := right_operator_on_algebra_vector P Ω _ _ hrright (star x) hrΩ
    change conjugationOperator J (r : H →L[ℂ] H) (star x.val Ω) =
      star x.val (star (r : H →L[ℂ] H) Ω) at hc
    rw [hc]
    simp only [star_mul, mul_apply_eq_comp]

/-- A bounded operator preserving defining graph vectors preserves the
closed graph subspace. -/
theorem rescaledGraphSubspace_invariant_of_vectors
    (P : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (hT : ∀ x : Algebra P, ∃ y : Algebra P,
      T (rescaledGraphVector J Ω c x.val) = rescaledGraphVector J Ω c y.val)
    {ξ : TomitaGraphHilbert H} (hξ : ξ ∈ rescaledGraphSubspace P J Ω c) :
    T ξ ∈ rescaledGraphSubspace P J Ω c := by
  have h : (rescaledGraphMap P J Ω c).range.topologicalClosure ≤
      (rescaledGraphSubspace P J Ω c).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hT x
      exact Submodule.le_topologicalClosure _ ⟨y, hy.symm⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact h hξ

/-- The common right-action identities make the graph reduce the
unitary implementing simultaneous left and right multiplication. -/
theorem rescaledGraphProjection_commutes
    (P : VonNeumannAlgebra H) (R : StarSubalgebra ℂ (H →L[ℂ] H))
    (hRP : R ≤ P.toStarSubalgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) (Ω : H) (c : ℝ)
    (hcomm : ∀ a ∈ R, conjugationOperator J (star a) ∈ P.commutant)
    (hvector : ∀ a ∈ R, conjugationOperator J (star a) Ω = a Ω)
    (r s : unitary (H →L[ℂ] H))
    (hr : (r : H →L[ℂ] H) ∈ R) (hs : (s : H →L[ℂ] H) ∈ R) :
    rescaledGraphProjection P J Ω c *
        (rescaledGraphAction J hJ r s : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) =
      (rescaledGraphAction J hJ r s : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
        rescaledGraphProjection P J Ω c := by
  let U : unitary (TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) :=
    rescaledGraphAction J hJ r s
  have hformula (x : Algebra P) :
      (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
        (rescaledGraphVector J Ω c x.val) =
      rescaledGraphVector J Ω c ((r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H)) :=
    rescaledGraphAction_vector P J hJ Ω c r s (hcomm _ hs)
      (by simpa only [star_star] using hcomm _ (R.star_mem' hr)) (hvector _ hs)
      (by simpa only [star_star] using hvector _ (R.star_mem' hr)) x
  apply Generator.starProjection_commutes_of_invariant
  · apply rescaledGraphSubspace_invariant_of_vectors
    intro x
    exact ⟨⟨(r : H →L[ℂ] H) * x.val * (s : H →L[ℂ] H),
      P.mul_mem (P.mul_mem (hRP hr) x.property) (hRP hs)⟩, hformula x⟩
  · apply rescaledGraphSubspace_invariant_of_vectors
    intro x
    let y : Algebra P := ⟨star (r : H →L[ℂ] H) * x.val * star (s : H →L[ℂ] H),
      P.mul_mem (P.mul_mem (hRP (R.star_mem' hr)) x.property) (hRP (R.star_mem' hs))⟩
    have hm : (r : H →L[ℂ] H) * y.val * (s : H →L[ℂ] H) = x.val := by
      change (r : H →L[ℂ] H) *
        (star (r : H →L[ℂ] H) * x.val * star (s : H →L[ℂ] H)) *
          (s : H →L[ℂ] H) = x.val
      calc
        _ = ((r : H →L[ℂ] H) * star (r : H →L[ℂ] H)) * x.val *
            (star (s : H →L[ℂ] H) * (s : H →L[ℂ] H)) := by noncomm_ring
        _ = x.val := by rw [Unitary.mul_star_self_of_mem r.property,
          Unitary.star_mul_self_of_mem s.property, one_mul, mul_one]
    have hf := hformula y
    rw [hm] at hf
    have he := congrArg (fun ξ : TomitaGraphHilbert H =>
      star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) ξ) hf
    change (star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H) *
      (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H))
        (rescaledGraphVector J Ω c y.val) =
          star (U : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
            (rescaledGraphVector J Ω c x.val) at he
    rw [Unitary.star_mul_self_of_mem U.property, one_apply_eq_self] at he
    exact ⟨y, he.symm⟩

end

end KadisonKastler

end OAI
