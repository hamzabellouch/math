import Mathlib
import OAI.Probability.CriticalPercolation.Classification.ClassificationProducerBoundary
import OAI.Probability.CriticalPercolation.Classification.FiniteBGTBridge

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Pointwise

namespace CriticalPercolation.CompactQuotient
variable {A : Type*} [Group A]

def FiniteBGTPowerOutput (S : Set A) (n : ℕ) : Prop :=
  ∃ H N : Subgroup A, ∃ hH : H.Normal, let _ := hH
    N.Normal ∧ H≤N ∧ (H : Set A)⊆S^(4*n) ∧ N.index≠0 ∧
      Group.IsNilpotent (N ⧸ H.subgroupOf N)

def HasUniformFiniteBGTModels (A : Type*) [Group A] (K : ℝ) : Prop :=
  ∃ R : ℕ, ∀ S : Set A, S.Finite → (1 : A)∈S → S⁻¹=S →
    Subgroup.closure S=⊤ → ∀ n≥R, IsApproximateSubgroup K (S^n) →
      FiniteBGTPowerOutput S n

lemma finiteByVirtuallyNilpotent_of_finiteBGTPowerOutput
    (S : Set A) (hS : S.Finite) (n : ℕ) (h : FiniteBGTPowerOutput S n) :
    FiniteByVirtuallyNilpotent A := by
  obtain ⟨H,N,hn,_,hHN,hH,hN,hNil⟩ := h
  let _ := hn
  let _ := hNil
  exact ⟨H,hn,finite_by_nilpotent_of_BGT_output S hS n H N hHN hH hN⟩

lemma one_le_of_uniformFiniteApproximatePowers {K : ℝ}
    (h : UniformFiniteApproximatePowers A K) : 1≤K := by
  obtain ⟨S,_,_,_,_,hpow⟩ := h
  obtain ⟨n,_,hn⟩ := hpow 0
  exact hn.one_le

theorem finiteByVirtuallyNilpotent_of_uniform_models {K : ℝ}
    (hpow : UniformFiniteApproximatePowers A K)
    (hbgt : HasUniformFiniteBGTModels A K) : FiniteByVirtuallyNilpotent A := by
  obtain ⟨R,hR⟩ := hbgt
  obtain ⟨S,hS,h1,hinv,hgen,hscales⟩ := hpow
  obtain ⟨n,hn,ha⟩ := hscales R
  exact finiteByVirtuallyNilpotent_of_finiteBGTPowerOutput S hS n
    (hR S hS h1 hinv hgen n hn ha)

theorem no_uniform_finite_BGT_models {K : ℝ}
    (hpow : UniformFiniteApproximatePowers A K)
    (hf : ¬FiniteByVirtuallyNilpotent A) : ¬HasUniformFiniteBGTModels A K :=
  fun h => hf (finiteByVirtuallyNilpotent_of_uniform_models hpow h)

end CriticalPercolation.CompactQuotient
namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

theorem finite_classification_obstruction {K : ℝ}
    (h : HasFiniteApproximateQuotientCounterexample Γ K) :
    let _ : TopologicalSpace X := ⊥
    let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
    ∃ H : Subgroup (Γ ≃g Γ), ∃ hn : H.Normal, let _ := hn
      IsCompact (H : Set (Γ ≃g Γ)) ∧ IsOpen (H : Set (Γ ≃g Γ)) ∧
      1≤K ∧ Group.FG ((Γ ≃g Γ) ⧸ H) ∧
      CompactQuotient.UniformFiniteApproximatePowers ((Γ ≃g Γ) ⧸ H) K ∧
      ¬CompactQuotient.HasUniformFiniteBGTModels ((Γ ≃g Γ) ⧸ H) K := by
  let _ : TopologicalSpace X := ⊥
  let _ : TopologicalSpace (Γ ≃g Γ) := autTopology Γ
  obtain ⟨H,hn,hc,ho,hfg,hpow,hfail⟩ := h
  let _ := hn
  exact ⟨H,hn,hc,ho,CompactQuotient.one_le_of_uniformFiniteApproximatePowers hpow,
    hfg,hpow,CompactQuotient.no_uniform_finite_BGT_models hpow hfail⟩

end CriticalPercolation.GraphTopology
end
end

end OAI
