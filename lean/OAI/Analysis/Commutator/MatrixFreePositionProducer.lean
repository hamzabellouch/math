import Mathlib
import OAI.Analysis.Commutator.AmplifiedTowerGeometry
import OAI.Analysis.Commutator.IrreducibleMatrixTower
import OAI.Analysis.Commutator.MatrixCornerInclusion
import OAI.Analysis.Commutator.MatrixStandardForm
import OAI.Analysis.Commutator.MatrixVectorTrace
import OAI.Analysis.Commutator.NormalizedTowerFreePosition

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H) [Nontrivial M]

local instance matrixFreePositionProducerDecidableEq : DecidableEq ι := Classical.decEq ι

variable (E : ℕ → Stage M) (τ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

theorem exists_matrix_freeCornerPosition [TopologicalSpace.SeparableSpace τ.GNS]
    (hE : Monotone (fun n => (E n).hom.range))
    (hsize : ∀ n,n+1 ≤ Fintype.card (E n).I)
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (hω : (ω : Filter ℕ) ≤ atTop) :
    Nonempty (FreeCornerPosition (MatrixGNS.trace (ι:=ι) τ) ω
      (matrixVonNeumann ι i₀ (generated M E))
      (matrixInclusion ι i₀ M (generated M E) (generated_le M E))) := by
  let : Nonempty ι := ⟨i₀⟩
  let P := matrixVonNeumann ι i₀ M
  let R := generated M E
  let Q := matrixVonNeumann ι i₀ R
  let σ := matrixTrace ι i₀ M τ
  let F := fun n => amplifiedStage ι i₀ M (E n)
  let : Nontrivial P := (diagonalHom_injective ι i₀ M).nontrivial
  let U := standardMatrixUnitary ι i₀ M τ
  let : TopologicalSpace.SeparableSpace σ.GNS :=
    U.symm.surjective.denseRange.separableSpace U.symm.continuous
  have hQP : Q ≤ P := matrixVonNeumann_mono ι i₀ (generated_le M E)
  have hj (q : Q) : matrixEquiv ι i₀ M
      (matrixInclusion ι i₀ M R (generated_le M E) q)=NormalSubalgebra.inclusion P Q hQP q := by
    change matrixEquiv ι i₀ M ((matrixEquiv ι i₀ M).symm _)=_
    rw [StarAlgEquiv.apply_symm_apply]
    rfl
  have hQdiff : DiffuseProjection.HasNoMinimalProjections Q := by
    let ρ := NormalSubalgebra.trace M R (generated_le M E) τ
    apply matrix_diffuse_of_stages ι i₀ R (generated_factor M E hirr) ρ
      (NormalSubalgebra.tracial M R (generated_le M E) τ hτ)
      (NormalSubalgebra.faithful M R (generated_le M E) τ hfaith)
      (NormalSubalgebra.one M R (generated_le M E) τ h1) (generatedStage M E)
    intro N
    exact ⟨N,lt_of_lt_of_le (Nat.lt_succ_self N) (hsize N)⟩
  apply exists_freeCornerPosition_of_equiv_stages P Q hQP (matrixEquiv ι i₀ M)
    (matrixInclusion ι i₀ M R (generated_le M E)) hj (MatrixGNS.trace (ι:=ι) τ) σ ω F
    (amplifiedStage_monotone ι i₀ M E hE)
    (matrixTrace_equiv ι i₀ M τ) (MatrixGNS.trace_mul τ hτ)
    (matrixTrace_tracial ι i₀ M τ hτ) hω (matrixTrace_normal ι i₀ M τ hnormal)
    (matrixTrace_faithful ι i₀ M τ hfaith) (MatrixGNS.trace_one τ h1)
    (amplifiedStage_irreducible ι i₀ M E hirr) _ _ hQdiff
  · intro n a
    apply amplifiedStage_in_relative ι i₀ M E R _ n a
    intro k b
    exact stage_mem M E k b
  · apply tendsto_atTop_mono (f := fun n : ℕ => (n:ℝ)) _ tendsto_natCast_atTop_atTop
    intro n
    have hc : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hcard : n ≤ Fintype.card (F n).I := by
      rw [amplifiedStage_size]
      exact (Nat.le_succ n).trans ((hsize n).trans (Nat.le_mul_of_pos_left _ hc))
    exact_mod_cast hcard

end Kadison.MatrixTower

end

end
end

end OAI
