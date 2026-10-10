import OAI.Algebra.AuslanderReiten.HomComplex.FullHomLinear

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

variable (k : Type u) [CommRing k]
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n a n' : ℤ)

noncomputable def rightShiftCocycleLinearEquiv (hn : n' + a = n) :
    Cocycle K L n ≃ₗ[k] Cocycle K (L⟦a⟧) n' :=
  { Cocycle.rightShiftAddEquiv n a n' hn with
    map_smul' := by
      intro c x
      apply Subtype.ext
      exact Cochain.rightShift_smul x.val a n' hn c }

variable {k K L n a n'}

theorem rightShift_boundary (hn : n' + a = n) (x : Cocycle K L n)
    (hx : x ∈ coboundaries K L n) : x.rightShift a n' hn ∈ coboundaries K (L⟦a⟧) n' := by
  obtain ⟨m, hm, y, hy⟩ := hx
  have hm' : n' - 1 + a = m := by omega
  refine ⟨n' - 1, by omega, a.negOnePow • y.rightShift a (n' - 1) hm', ?_⟩
  rw [δ_units_smul, Cochain.δ_rightShift y a (n' - 1) n' hm' n hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

theorem rightUnshift_boundary (hn : n' + a = n) (x : Cocycle K (L⟦a⟧) n')
    (hx : x ∈ coboundaries K (L⟦a⟧) n') : x.rightUnshift n hn ∈ coboundaries K L n := by
  obtain ⟨m', hm', y, hy⟩ := hx
  have hm : m' + a = n - 1 := by omega
  refine ⟨n - 1, by omega, a.negOnePow • y.rightUnshift (n - 1) hm, ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift y (n - 1) hm n n' hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

variable (k K L n a n')

noncomputable def rightShiftCohomologyEquiv (hn : n' + a = n) :
    CohomologyClass K L n ≃ₗ[k] CohomologyClass K (L⟦a⟧) n' :=
  Submodule.Quotient.equiv (fullHomCoboundaries k K L n)
    (fullHomCoboundaries k K (L⟦a⟧) n') (rightShiftCocycleLinearEquiv k K L n a n' hn) (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact rightShift_boundary hn x hx
      · intro hy
        let E := rightShiftCocycleLinearEquiv k K L n a n' hn
        refine ⟨E.symm y, rightUnshift_boundary hn y hy, E.apply_symm_apply y⟩)

noncomputable def leftShiftCocycleLinearEquiv (hn : n + a = n') :
    Cocycle K L n ≃ₗ[k] Cocycle (K⟦a⟧) L n' :=
  { Cocycle.leftShiftAddEquiv n a n' hn with
    map_smul' := by
      intro c x
      apply Subtype.ext
      exact Cochain.leftShift_smul x.val a n' hn c }

variable {k K L n a n'}

theorem leftShift_boundary (hn : n + a = n') (x : Cocycle K L n)
    (hx : x ∈ coboundaries K L n) : x.leftShift a n' hn ∈ coboundaries (K⟦a⟧) L n' := by
  obtain ⟨m, hm, y, hy⟩ := hx
  have hm' : m + a = n' - 1 := by omega
  refine ⟨n' - 1, by omega, a.negOnePow • y.leftShift a (n' - 1) hm', ?_⟩
  rw [δ_units_smul, Cochain.δ_leftShift y a (n' - 1) n' hm' n hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

theorem leftUnshift_boundary (hn : n + a = n') (x : Cocycle (K⟦a⟧) L n')
    (hx : x ∈ coboundaries (K⟦a⟧) L n') : x.leftUnshift n hn ∈ coboundaries K L n := by
  obtain ⟨m', hm', y, hy⟩ := hx
  have hm : n - 1 + a = m' := by omega
  refine ⟨n - 1, by omega, a.negOnePow • y.leftUnshift (n - 1) hm, ?_⟩
  rw [δ_units_smul, Cochain.δ_leftUnshift y (n - 1) hm n n' hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

variable (k K L n a n')

noncomputable def leftShiftCohomologyEquiv (hn : n + a = n') :
    CohomologyClass K L n ≃ₗ[k] CohomologyClass (K⟦a⟧) L n' :=
  Submodule.Quotient.equiv (fullHomCoboundaries k K L n)
    (fullHomCoboundaries k (K⟦a⟧) L n') (leftShiftCocycleLinearEquiv k K L n a n' hn) (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact leftShift_boundary hn x hx
      · intro hy
        let E := leftShiftCocycleLinearEquiv k K L n a n' hn
        refine ⟨E.symm y, leftUnshift_boundary hn y hy, E.apply_symm_apply y⟩)

end ArExplicit.CompleteComparison

end OAI
