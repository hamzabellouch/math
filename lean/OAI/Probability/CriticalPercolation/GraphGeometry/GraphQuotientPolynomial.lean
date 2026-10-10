import Mathlib
import OAI.Probability.CriticalPercolation.Growth.GraphQuotientGrowth
import OAI.Probability.CriticalPercolation.Classification.QualitativeClassificationBoundary

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical Pointwise

namespace CriticalPercolation
namespace CompactQuotient

def HasSparsePolynomialWordGrowth (A : Type*) [Group A] : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ d : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard≤n^d

end CompactQuotient
namespace GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem quotient_sparse_polynomial_word_growth
    [TopologicalSpace X] [DiscreteTopology X]
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d)
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (ho : @IsOpen (Γ ≃g Γ) (autTopology Γ) (H : Set (Γ ≃g Γ))) :
    CompactQuotient.HasSparsePolynomialWordGrowth ((Γ ≃g Γ) ⧸ H) := by
  obtain ⟨M,_,hT,h1,hinv,hgen,hncard⟩ :=
    quotient_powers_ncard_le Γ hc hl ht o H ho
  refine ⟨(QuotientGroup.mk' H) '' displacement Γ o 1,hT,h1,hinv,hgen,d+1,?_⟩
  intro R
  obtain ⟨n,hn,hp⟩ := hpoly (max R (max M 1))
  have hnR : R≤n := (le_max_left _ _).trans hn
  have hnM : M≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨n,hnR,?_⟩
  calc
    (((QuotientGroup.mk' H) '' displacement Γ o 1)^n).ncard ≤
        (reachBall Γ o n).ncard*M := hncard n hn1
    _ ≤ n^d*M := Nat.mul_le_mul_right M hp
    _ ≤ n^d*n := Nat.mul_le_mul_left _ hnM
    _ = n^(d+1) := (pow_succ n d).symm

theorem weak_Gromov_counterexample_of_finite_classification_failure {K : ℝ}
    (hc : Γ.Connected) (hl : ∀ x, (Γ.neighborSet x).Finite)
    (ht : ∀ u v, ∃ g : Γ ≃g Γ, g u=v) (o : X) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, (reachBall Γ o n).ncard≤n^d)
    (h : HasFiniteApproximateQuotientCounterexample Γ K) :
    let _ : TopologicalSpace X := ⊥
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
      IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      Group.FG ((Γ ≃g Γ) ⧸ H) ∧
      CompactQuotient.HasSparsePolynomialWordGrowth ((Γ ≃g Γ) ⧸ H) ∧
      ¬Group.IsVirtuallyNilpotent ((Γ ≃g Γ) ⧸ H) := by
  let _ : TopologicalSpace X := ⊥
  let _ : DiscreteTopology X := ⟨rfl⟩
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨H,hn,hcH,hoH,_,hfg,_,hf⟩ :=
    not_virtuallyNilpotent_quotient_of_classification_failure Γ h
  let _ := hn
  exact ⟨H,hn,hcH,hoH,hfg,
    quotient_sparse_polynomial_word_growth Γ hc hl ht o d hpoly H hoH,hf⟩

end GraphTopology
end CriticalPercolation
end
end

end OAI
