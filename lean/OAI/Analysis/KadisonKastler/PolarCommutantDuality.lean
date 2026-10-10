import OAI.Analysis.KadisonKastler.TomitaPolarCorePairing
import OAI.Analysis.KadisonKastler.TomitaVectorFixed

namespace OAI

/-! # The reverse polar-commutant inclusion

The vector-state identity and the inclusion of the conjugated commutant into
M already force the reverse inclusion. Density upgrades the vector identity
to operator commutation. This is the last algebraic step in the modular proof.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem polar_commutant_reverse (C : H ≃ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C)
    (Ω : H) (hΩ : C Ω = Ω) (hcyc : DenseRange (algebraVectorMap M Ω))
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hstate : ∀ a b : Algebra M, inner ℂ Ω (b.val (C (a.val Ω))) =
      inner ℂ (a.val (C (b.val Ω))) Ω)
    (hincl : ∀ b : Algebra M.commutant, conjugationOperator C b.val ∈ M) :
    ∀ a : Algebra M, conjugationOperator C a.val ∈ M.commutant := by
  have hd : DenseRange (fun b : Algebra M.commutant => b.val Ω) :=
    Generator.commutant_orbit_dense M Ω (fun a ha => hsep ha)
  have hvector (a y : Algebra M) :
      a.val (C (y.val Ω)) = conjugationOperator C y.val (a.val Ω) := by
    apply ext_inner_left ℂ
    intro v
    apply hd.induction_on (p := fun v =>
      inner ℂ v (a.val (C (y.val Ω))) =
        inner ℂ v (conjugationOperator C y.val (a.val Ω))) v
      (isClosed_eq (by fun_prop) (by fun_prop))
    intro b
    let c : Algebra M := ⟨conjugationOperator C (star b.val), hincl (star b)⟩
    have hbc : star b.val * a.val = a.val * star b.val := by
      have h := (star b).property a.val (Set.mem_union_left _ a.property)
      exact h.symm
    have hcs : star c.val = conjugationOperator C b.val := by
      dsimp only [c]
      rw [← conjugationOperator_star C hC, star_star]
    have hbC : star b.val (C (y.val Ω)) = C (c.val (y.val Ω)) := by
      dsimp only [c]
      simp only [conjugationOperator_apply]
      rw [hC]
    calc
      inner ℂ (b.val Ω) (a.val (C (y.val Ω))) =
          inner ℂ Ω ((star b.val * a.val) (C (y.val Ω))) := by
        change inner ℂ (b.val Ω) (a.val (C (y.val Ω))) =
          inner ℂ Ω (b.val.adjoint (a.val (C (y.val Ω))))
        exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
      _ = inner ℂ Ω (a.val (C ((c * y).val Ω))) := by
        rw [hbc]
        change inner ℂ Ω (a.val (star b.val (C (y.val Ω)))) = _
        rw [hbC]
        rfl
      _ = inner ℂ ((c * y).val (C (a.val Ω))) Ω := hstate (c * y) a
      _ = inner ℂ (C (a.val Ω)) (y.val.adjoint (conjugationOperator C b.val Ω)) := by
        change inner ℂ (c.val (y.val (C (a.val Ω)))) Ω = _
        rw [← ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.adjoint_inner_right]
        rw [← ContinuousLinearMap.star_eq_adjoint c.val, hcs]
      _ = inner ℂ (y.val (C (a.val Ω))) (C (b.val Ω)) := by
        rw [ContinuousLinearMap.adjoint_inner_right, conjugationOperator_apply, hΩ]
      _ = inner ℂ (b.val Ω) (conjugationOperator C y.val (a.val Ω)) := by
        rw [conjugationOperator_apply]
        have he := conjugateIsometry_inner C (y.val (C (a.val Ω))) (C (b.val Ω))
        rw [hC] at he
        have hs := congrArg star he
        rw [star_star] at hs
        calc
          _ = star (inner ℂ (C (y.val (C (a.val Ω)))) (b.val Ω)) := hs.symm
          _ = _ := by
            change (starRingEnd ℂ) _ = _
            rw [inner_conj_symm]
  intro a
  change conjugationOperator C a.val ∈ (M.commutant : Set (H →L[ℂ] H))
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro y hy
  let d : Algebra M := ⟨y, hy⟩
  apply ContinuousLinearMap.ext
  intro v
  apply hcyc.induction_on (p := fun v =>
    (y * conjugationOperator C a.val) v = (conjugationOperator C a.val * y) v) v
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro z
  have hdz := hvector (d * z) a
  have hz := hvector z a
  change y (conjugationOperator C a.val (z.val Ω)) =
    conjugationOperator C a.val (y (z.val Ω))
  rw [← hz]
  exact hdz

end

end KadisonKastler

end OAI
