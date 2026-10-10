import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.StrongDensePeriodicity
import OAI.Probability.CriticalPercolation.LinearGroups.ProjectivelyPeriodicSchur

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type} [Field K] [CharZero K] [Countable K] [IsAlgClosed K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
variable [Group G] [DecidableEq G]
variable {degree : ℕ}

lemma StrongFullSpan.scalar_power (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : K, ((ρ g).toLinearMap)^m=a • (1:End K V) := by
  let b := Module.finBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  let τ := (linearMatrixEquiv (K:=K) (V:=V)).toMonoidHom.comp ρ
  have hm (g : G) : (τ g).val=e (ρ g).toLinearMap := rfl
  have ht : StrongFullMatrixSpan τ := by
    intro H hH
    let E := e.toLinearEquiv.trans (matrixFlatten (K:=K) (n:=Fin (finrank K V)))
    exact span_equiv_top E (fun h : H => (ρ h.val).toLinearMap) (hρ H hH)
  have : NeZero (finrank K V) := ⟨ne_of_gt (Module.finrank_pos (R:=K) (M:=V))⟩
  obtain ⟨m,hmpos,a,_,ha⟩ := scalar_power_of_strongFullMatrixSpan τ ht hg g
  refine ⟨m,hmpos,a,e.injective ?_⟩
  rw [map_pow,map_smul,map_one,←hm]
  exact ha

lemma StrongFullSpan.virtually_comm_range (ρ : G →* (V ≃ₗ[K] V))
    (hρ : StrongFullSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧
      ∀ x y : (ρ.comp H.subtype).range, x*y=y*x := by
  let := hg.fg
  exact exists_finiteIndex_comm_range_of_projectively_periodic ρ
    (fun g => hρ.scalar_power ρ hg g)

end CriticalPercolation.LinearGrowth
end
end

end OAI
