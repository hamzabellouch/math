import OAI.Analysis.Laughlin.Spin.Support
import OAI.Analysis.Laughlin.ThreeBody.RankTrace
import OAI.Analysis.Laughlin.ThreeBody.TraceLimit

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def pairOrbitalUnit (Q p j : ℕ) : PairOrbitalIndex Q → ℝ :=
  fun i => if i.1.val=p ∧ i.2.val=j then 1 else 0

theorem pairOrbitalUnit_dot (Q p j : ℕ) (hp : p < 2*Q-2+1) (hj : j ≤ Q)
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (pairOrbitalUnit Q p j) = v (⟨p,hp⟩,⟨j,by omega⟩) := by
  classical
  simp only [dotProduct,pairOrbitalUnit,mul_ite,mul_one,mul_zero]
  have he : ∀ i : PairOrbitalIndex Q, (i.1.val=p ∧ i.2.val=j) ↔ i=(⟨p,hp⟩,⟨j,by omega⟩) := by
    intro i
    constructor
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · intro h; subst i; exact ⟨rfl,rfl⟩
  simp_rw [he]
  simp

noncomputable def threeBodyLevelVector (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) :
    PairOrbitalIndex Q → ℝ :=
  (entries.map (fun e => if e.1+e.2.1=T then sourceAlpha t e • pairOrbitalUnit Q e.1 e.2.1 else 0)).sum

noncomputable def threeBodyLevelMatrix (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ)) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  let u := pairOrbitalUnit Q t (T-t)
  let a := threeBodyLevelVector Q t T entries
  ((ell : ℝ)/10^7) • (realOuter u a + realOuter a u) + realOuter a a

noncomputable def physicalThreeBodyMatrix (Q : ℕ) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  (Certificate.rows.map (fun row =>
    (((List.range 16).filter (fun T => row.1 ≤ T)).map
      (fun T => threeBodyLevelMatrix Q row.1 T row.2.1 row.2.2)).sum)).sum

theorem threeBodyLevelMatrix_quadratic (Q t T : ℕ) (ell : ℤ) (entries : List (ℕ × ℕ × ℤ))
    (v : PairOrbitalIndex Q → ℝ) :
    dotProduct v (threeBodyLevelMatrix Q t T ell entries *ᵥ v) =
      2*((ell : ℝ)/10^7)*dotProduct v (pairOrbitalUnit Q t (T-t))*
        dotProduct v (threeBodyLevelVector Q t T entries) +
      (dotProduct v (threeBodyLevelVector Q t T entries))^2 := by
  simp only [threeBodyLevelMatrix,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,realOuter_quadratic,smul_eq_mul]
  ring

end Laughlin.Spin

end OAI
