import OAI.MathematicalPhysics.Elasticity.Rigidity
import OAI.MathematicalPhysics.Elasticity.BoundaryJets

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryPacket
open Elasticity
/-- Full common-exterior reduction from the physical DN map. In particular no
prior boundary jets or agreement on a boundary neighbourhood is assumed. -/
theorem admissible_common_exterior {Ω : Set X} (hD : SourceDomain Ω)
    (l₁ m₁ l₂ m₂ : X → ℝ) (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂) :
    ∃ L₁ M₁ L₂ M₂ : X → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) L₁ ∧ ContDiff ℝ (⊤ : ℕ∞) M₁ ∧
      ContDiff ℝ (⊤ : ℕ∞) L₂ ∧ ContDiff ℝ (⊤ : ℕ∞) M₂ ∧
      EqOn L₁ l₁ Ω ∧ EqOn M₁ m₁ Ω ∧ EqOn L₂ l₂ Ω ∧ EqOn M₂ m₂ Ω ∧
      (∀ x,0 < M₁ x ∧ 0<3*L₁ x+2*M₁ x) ∧
      (∀ x,0 < M₂ x ∧ 0<3*L₂ x+2*M₂ x) ∧
      EqOn L₂ L₁ Ωᶜ ∧ EqOn M₂ M₁ Ωᶜ ∧
      DN Ω L₁ M₁=DN Ω L₂ M₂ ∧
      ∃ K,IsCompact K ∧ ∀ x∉K,L₁ x=0 ∧ M₁ x=1 ∧ L₂ x=0 ∧ M₂ x=1 := by
  obtain ⟨hjl,hjm⟩ := admissible_boundary_jets hD l₁ m₁ l₂ m₂ ha₁ ha₂ hDN
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,hK⟩ :=
    ElasticityBoundary.common_exterior_of_all_jets hD.2.2.1.isCompact_closure
      hU₁ hU₂ hs₁ hs₂ l₁ m₁ l₂ m₂ hl₁ hm₁ hl₂ hm₂ ha₁.2.2 ha₂.2.2 hjl hjm
  refine ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,?_,hK⟩
  exact (DN_coeff_congr hD.1.measurableSet heL₁ heM₁).trans
    (hDN.trans (DN_coeff_congr hD.1.measurableSet heL₂ heM₂).symm)
end ElasticityBoundaryPacket

end
end
section
noncomputable section
open Set
namespace Elasticity
open ElasticityAugmented ElasticityCoeffBounds

lemma exteriorConstant_of_eq_const {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set X} (hK : IsCompact K) (c : ℝ) (hc : ∀ x∉K,f x=c) :
    ExteriorConstant (smoothOfReal f hf) := by
  refine ⟨(c : ℂ),hK.of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  by_contra h
  apply hx
  change (f x : ℂ)-(c : ℂ)=0
  rw [hc x h,sub_self]

/-- Exact global smooth isotropic elasticity uniqueness on every bounded
connected domain with genuine smooth open boundary charts. Boundary jets,
common exterior, physical transfer, weak limits, constrained common frames,
parameter holomorphy and transport matching are all proved dependencies. -/
theorem source_global_uniqueness (Ω : Set X) (hD : SourceDomain Ω)
    (lam₁ mu₁ lam₂ mu₂ : X → ℝ)
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂) :
    (∀ x∈Ω,lam₁ x=lam₂ x) ∧ (∀ x∈Ω,mu₁ x=mu₂ x) := by
  obtain ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,hd,K,hK,hout⟩ :=
    ElasticityBoundaryPacket.admissible_common_exterior hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN
  let l : Fin 2 → X → ℝ := ![L₁,L₂]
  let m : Fin 2 → X → ℝ := ![M₁,M₂]
  have hl (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (l q) := by fin_cases q; exact hL₁; exact hL₂
  have hm (q : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (m q) := by fin_cases q; exact hM₁; exact hM₂
  have hp (q : Fin 2) (x : X) : 0 < m q x ∧ 0<3*l q x+2*m q x := by
    fin_cases q; exact hp₁ x; exact hp₂ x
  have hcll (q : Fin 2) : ExteriorConstant (smoothOfReal (l q) (hl q)) := by
    apply exteriorConstant_of_eq_const (hl q) hK 0
    intro x hx
    fin_cases q; exact (hout x hx).1; exact (hout x hx).2.2.1
  have hclm (q : Fin 2) : ExteriorConstant (smoothOfReal (m q) (hm q)) := by
    apply exteriorConstant_of_eq_const (hm q) hK 1
    intro x hx
    fin_cases q; exact (hout x hx).2.1; exact (hout x hx).2.2.2
  have he (x) (hx : x∉Ω) : l 0 x=l 1 x ∧ m 0 x=m 1 x := ⟨(hexL hx).symm,(hexM hx).symm⟩
  have hh := dn_global_coefficients_equal hD.1 hD.2.2.1 l m hl hm hp hcll hclm he hd
  constructor
  · intro x hx
    rw [← heL₁ hx,← heL₂ hx]
    exact congrFun hh.1 x
  · intro x hx
    rw [← heM₁ hx,← heM₂ hx]
    exact congrFun hh.2 x
end Elasticity

end
end
theorem Elasticity.global_uniqueness : Elasticity.MainClaim := by
  intro Ω hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN
  exact Elasticity.source_global_uniqueness Ω hD lam₁ mu₁ lam₂ mu₂ ha₁ ha₂ hDN

end OAI
