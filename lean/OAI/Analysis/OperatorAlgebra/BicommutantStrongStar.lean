import OAI.Analysis.IrrationalRotation.Operators.BicommutantDensity

namespace OAI

/-! Finite simultaneous strong approximation of an operator and its adjoint.
Only the algebraic star subalgebra is used; no norm bound is asserted. -/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace WeakPureInfiniteness
open Invariant233.BicommutantDensity

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype I]

private def pairedOrbit (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x y : I → H) :
    A →ₗ[ℝ] PiLp 2 (fun _ : I ⊕ I => H) where
  toFun a := WithLp.toLp 2 (Sum.elim (fun i => (a : H →L[ℂ] H) (x i))
    (fun i => (star (a : H →L[ℂ] H)) (y i)))
  map_add' a b := by ext i; cases i <;> simp
  map_smul' t a := by
    ext i
    cases i <;> simp [StarModule.star_smul]

theorem pairedOrbit_mem_closure
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (x y : I → H) :
    WithLp.toLp 2 (Sum.elim (fun i => T (x i)) (fun i => star T (y i))) ∈
      closure (Set.range (fun a : A => pairedOrbit A x y a)) := by
  classical
  let : InnerProductSpace ℝ (PiLp 2 (fun _ : I ⊕ I => H)) :=
    InnerProductSpace.rclikeToReal ℂ _
  let R := (pairedOrbit A x y).range
  change _ ∈ R.topologicalClosure
  rw [← R.orthogonal_orthogonal_eq_closure]
  apply (Rᗮ.mem_orthogonal _).mpr
  intro η hη
  let ζ : PiLp 2 (fun _ : I ⊕ I => H) :=
    WithLp.toLp 2 (Sum.elim x (fun i => η (.inr i)))
  let g : PiLp 2 (fun _ : I ⊕ I => H) → ℝ := fun z =>
    ∑ i, (inner ℂ (η (.inl i)) (z (.inl i))).re +
    ∑ i, (inner ℂ (z (.inr i)) (y i)).re
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hadj (a : H →L[ℂ] H) (i : I) :
      inner ℂ (η (.inr i)) (star a (y i)) = inner ℂ (a (η (.inr i))) (y i) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hzero (a : A) : g (amplify (I ⊕ I) (a : H →L[ℂ] H) ζ) = 0 := by
    have hz := (R.mem_orthogonal' η).mp hη (pairedOrbit A x y a) ⟨a, rfl⟩
    rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply] at hz
    simpa [g, ζ, pairedOrbit, Fintype.sum_sum_type, Complex.re_sum, hadj] using hz
  have hcl : amplify (I ⊕ I) T ζ ∈
      closure (Set.range (fun a : A => amplify (I ⊕ I) (a : H →L[ℂ] H) ζ)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨a, ha, hclose⟩ := exists_amplified_approximation A hT ζ hε
    exact ⟨_, ⟨⟨a, ha⟩, rfl⟩, by simpa [dist_eq_norm, norm_sub_rev] using hclose⟩
  have hclosed : IsClosed {z : PiLp 2 (fun _ : I ⊕ I => H) | g z = 0} :=
    isClosed_eq hg continuous_const
  have ht : g (amplify (I ⊕ I) T ζ) = 0 :=
    hclosed.closure_subset_iff.mpr (by rintro _ ⟨a, rfl⟩; exact hzero a) hcl
  rw [real_inner_eq_re_inner ℂ, PiLp.inner_apply]
  simpa [g, ζ, Fintype.sum_sum_type, Complex.re_sum, hadj] using ht

theorem exists_finite_strongStar_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (x y : I → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : H →L[ℂ] H, a ∈ A ∧
      (∀ i, ‖a (x i) - T (x i)‖ < ε) ∧
      (∀ i, ‖star a (y i) - star T (y i)‖ < ε) := by
  obtain ⟨z, ⟨a, rfl⟩, hclose⟩ := Metric.mem_closure_iff.mp
    (pairedOrbit_mem_closure A hT x y) ε hε
  rw [dist_eq_norm] at hclose
  rw [norm_sub_rev] at hclose
  refine ⟨a, a.property, ?_, ?_⟩
  · intro i
    have h := PiLp.norm_apply_le
      (pairedOrbit A x y a - WithLp.toLp 2
        (Sum.elim (fun i => T (x i)) (fun i => star T (y i)))) (.inl i)
    exact h.trans_lt hclose
  · intro i
    have h := PiLp.norm_apply_le
      (pairedOrbit A x y a - WithLp.toLp 2
        (Sum.elim (fun i => T (x i)) (fun i => star T (y i)))) (.inr i)
    exact h.trans_lt hclose

end WeakPureInfiniteness

end

end OAI
