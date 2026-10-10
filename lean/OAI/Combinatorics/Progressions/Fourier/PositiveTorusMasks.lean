import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget
import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3

open scoped TensorProduct NNReal

theorem positiveCyclicNiltest_affine_torus {I : Type} [Fintype I]
    {N degree : ℕ} [NeZero N] {p : ℝ} (hdegree : 1 ≤ degree) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p)
    (Psi : (I → CircleFourier.Circle) → ℝ) (b a : I → ℝ) (K : ℝ≥0)
    (hPsi : ∀ v, 0 ≤ Psi v ∧ Psi v ≤ 1) (hLip : LipschitzWith K Psi)
    (hbudget : Real.log (3 + (K : ℝ)) ≤ p) :
    PositiveCyclicNiltest.{0} degree N p
      (fun x => Psi (fun i => ((b i + (x.val : ℝ) * a i : ℝ) : CircleFourier.Circle))) := by
  let d := Fintype.card I
  let e : I ≃ Fin d := Fintype.equivFin I
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] RationalTorus.Algebra d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] RationalTorus.Algebra d) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] RationalTorus.Algebra d) :=
    realification_moduleTopology_t2 (RationalTorus.basis d)
  let T := RationalTorus.realAffineNiltest e Psi b a K hPsi hLip
  refine .of_test (RationalTorus.nilmanifold d) hdegree T
    (RationalTorus.realAffineNiltest_unitInterval e Psi b a K hPsi hLip)
    (RationalTorus.realAffineNiltest_complexity e Psi b a K hPsi hLip hp hI hbudget) ?_
  intro x
  change _ = ((RationalTorus.realAffineNiltest e Psi b a K hPsi hLip).evalCyclic N (fun _ => x)).re
  rw [RationalTorus.realAffineNiltest_evalCyclic]
  rfl

end Erdos3

end

end OAI
