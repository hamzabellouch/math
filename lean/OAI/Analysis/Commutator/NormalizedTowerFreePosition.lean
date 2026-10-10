import Mathlib
import OAI.Analysis.Commutator.MatrixIndexEquiv
import OAI.Analysis.Commutator.RelativeEquivFreePosition

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open MatrixTower

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) [Nontrivial M] (hRM : R ≤ M)
  (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
  (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (E : ℕ → Stage M) (hE : Monotone (fun n => (E n).hom.range))

include hRM hj hE in
theorem exists_freeCornerPosition_of_equiv_stages [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n a,(E n).hom a*b=b*(E n).hom a) →
      ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,((E n).hom a : H →L[ℂ] H)∈R)
    (hgrow : Tendsto (fun n => (Fintype.card (E n).I:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  apply exists_freeCornerPosition_of_equiv_tower M R hRM e j hj τ σ ω
    (normalizedSize M E) (normalizedStage M E) (normalizedInclusion M E hE)
    htrace hτ hσ hω hnormal hfaith hone _ _
    (fun n m h a => normalizedInclusion_commutes M E hE h a) _ hdiffuse
  · intro b hb
    apply hirr b
    intro n a
    have hh := hb n ((matrixIndexEquiv (normalizedIndex M E n)).symm a)
    change (E n).hom ((matrixIndexEquiv (normalizedIndex M E n))
      ((matrixIndexEquiv (normalizedIndex M E n)).symm a))*b=
      b*(E n).hom ((matrixIndexEquiv (normalizedIndex M E n))
      ((matrixIndexEquiv (normalizedIndex M E n)).symm a)) at hh
    simpa only [StarAlgEquiv.apply_symm_apply] using hh
  · intro n a
    exact hstage n (matrixIndexEquiv (normalizedIndex M E n) a)
  · convert hgrow using 1
    ext n
    exact_mod_cast normalizedSize_succ M E n

end Kadison.TracialSequence

end

end
end

end OAI
