import OAI.Analysis.KadisonKastler.MatrixOrbitAverage

namespace OAI

/-! # Finite inner averages and their displacement bounds -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- A finite convex average of inner automorphisms of one concrete algebra. -/
structure FiniteInnerAverage where
  Index : Type
  fintype : Fintype Index
  nonempty : Nonempty Index
  unitary : Index → unitary (Algebra M)

attribute [instance] FiniteInnerAverage.fintype FiniteInnerAverage.nonempty

namespace FiniteInnerAverage

variable {M} (A : FiniteInnerAverage M)

def apply (x : H →L[ℂ] H) : H →L[ℂ] H :=
  finiteUnitaryAverage (fun i => ambientAlgebraUnitary (A.unitary i)) x

@[simp] theorem apply_sub (x y : H →L[ℂ] H) : A.apply (x - y) = A.apply x - A.apply y := by
  simp only [apply, finiteUnitaryAverage, finiteAverage, unitaryConj,
    mul_sub, sub_mul, Finset.sum_sub_distrib, smul_sub]

theorem norm_apply_le (x : H →L[ℂ] H) : ‖A.apply x‖ ≤ ‖x‖ :=
  norm_finiteAverage_le _ (fun _ => (norm_unitaryConj _ _).le)

theorem norm_apply_sub_le (x y : H →L[ℂ] H) :
    ‖A.apply x - A.apply y‖ ≤ ‖x - y‖ := by
  rw [← A.apply_sub]
  exact A.norm_apply_le _

theorem apply_mem_orbitHull (x : H →L[ℂ] H) :
    A.apply x ∈ convexHull ℝ (innerUnitaryOrbit M x) := by
  apply (convexHull_mono (s := Set.range (fun i =>
      unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)) ?_)
    (finiteAverage_mem_convexHull _)
  rintro _ ⟨i, rfl⟩
  exact ⟨A.unitary i, rfl⟩

end FiniteInnerAverage

end

end KadisonKastler

end OAI
