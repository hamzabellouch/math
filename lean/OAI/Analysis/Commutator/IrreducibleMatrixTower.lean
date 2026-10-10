import Mathlib
import OAI.Analysis.Commutator.MatrixTowerClosure
import OAI.Analysis.Commutator.MatrixTowerDiffuse
import OAI.Analysis.Commutator.MatrixTowerIrreducible

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def generatedStage (F : ℕ → Stage M) (n : ℕ) : Stage (generated M F) where
  I := (F n).I
  finite := (F n).finite
  dec := (F n).dec
  nonempty := (F n).nonempty
  hom := stageHom M F n

lemma generatedStage_monotone (F : ℕ → Stage M)
    (hF : Monotone (fun n => (F n).hom.range)) :
    Monotone (fun n => (generatedStage M F n).hom.range) := by
  intro n m hnm a ha
  rcases ha with ⟨b,rfl⟩
  obtain ⟨c,hc⟩ := hF hnm (show (F n).hom b∈(F n).hom.range from ⟨b,rfl⟩)
  exact ⟨c,Subtype.ext (congrArg (fun a : M => (a:H →L[ℂ] H)) hc)⟩

variable (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
  (hnormal : NormalGNS.BoundedWOTContinuous M τ)
  (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
  (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)

include hτ hnormal hfaith hone hfac hdiffuse in
theorem exists_irreducible_tower [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ F : ℕ → Stage M,
      Monotone (fun n => (F n).hom.range) ∧
      (∀ n,n+1≤Fintype.card (F n).I) ∧
      (∀ a : H →L[ℂ] H,a∈M → a∈Set.centralizer (generated M F : Set (H →L[ℂ] H)) →
        ∃ z : ℂ,a=z • (1:H →L[ℂ] H)) ∧
      FactorCorner.IsFactor (generated M F) ∧
      DiffuseProjection.HasNoMinimalProjections (generated M F) := by
  obtain ⟨x,hx,hxden⟩ := exists_selfAdjoint_dense_sequence M τ
  let F := tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx
  have hsize : ∀ n,n+1≤Fintype.card (F n).I := tower_size M τ hτ hnormal hfaith hone hfac hdiffuse x hx
  have hirr : ∀ a : M,(∀ n b,(F n).hom b*a=a*(F n).hom b) → ∃ z : ℂ,a=z • (1:M) := by
    intro a ha
    refine ⟨τ a,?_⟩
    exact scalar_of_commutes M τ hτ hone x hxden F
      (fun j _ hε => tower_requirement M τ hτ hnormal hfaith hone hfac hdiffuse x hx j hε) hfaith a ha
  have hR := generated_factor M F hirr
  refine ⟨F,tower_increasing M τ hτ hnormal hfaith hone hfac hdiffuse x hx,hsize,
    generated_irreducible M F hirr,hR,?_⟩
  let ρ := NormalSubalgebra.trace M (generated M F) (generated_le M F) τ
  apply diffuse_of_stages (generated M F) ρ
    (NormalSubalgebra.tracial M _ _ τ hτ)
    (NormalSubalgebra.faithful M _ _ τ hfaith)
    (NormalSubalgebra.one M _ _ τ hone) hR (generatedStage M F)
  intro N
  exact ⟨N,lt_of_lt_of_le (Nat.lt_succ_self N) (hsize N)⟩

end Kadison.MatrixTower

end

end
end

end OAI
