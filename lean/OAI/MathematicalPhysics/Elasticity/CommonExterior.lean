import OAI.MathematicalPhysics.Elasticity.Transfer

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
attribute [local instance] Classical.propDecidable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma extension_jets {K : Set E} {f g : E → ℝ} (h : f =ᶠ[𝓝ˢ K] g)
    {x : E} (hx : x∈K) (n : ℕ) : iteratedFDeriv ℝ n f x=iteratedFDeriv ℝ n g x := by
  exact ((h.filter_mono (nhds_le_nhdsSet hx)).iteratedFDeriv ℝ n).self_of_nhds

/-- Once actual boundary jets have been determined, the source common exterior
reduction follows, including every bounded component of the exterior. -/
theorem common_exterior_of_all_jets {Ω U₁ U₂ : Set E} (hc : IsCompact (closure Ω))
    (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (h₁ : closure Ω⊆U₁) (h₂ : closure Ω⊆U₂)
    (l₁ m₁ l₂ m₂ : E → ℝ)
    (hl₁ : ContDiffOn ℝ (⊤ : ℕ∞) l₁ U₁) (hm₁ : ContDiffOn ℝ (⊤ : ℕ∞) m₁ U₁)
    (hl₂ : ContDiffOn ℝ (⊤ : ℕ∞) l₂ U₂) (hm₂ : ContDiffOn ℝ (⊤ : ℕ∞) m₂ U₂)
    (hp₁ : ∀ x∈closure Ω, 0 < m₁ x ∧ 0 < 3*l₁ x+2*m₁ x)
    (hp₂ : ∀ x∈closure Ω, 0 < m₂ x ∧ 0 < 3*l₂ x+2*m₂ x)
    (hjl : ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x)
    (hjm : ∀ n : ℕ, ∀ x∈frontier Ω, iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x) :
    ∃ L₁ M₁ L₂ M₂ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) L₁ ∧ ContDiff ℝ (⊤ : ℕ∞) M₁ ∧
      ContDiff ℝ (⊤ : ℕ∞) L₂ ∧ ContDiff ℝ (⊤ : ℕ∞) M₂ ∧
      EqOn L₁ l₁ Ω ∧ EqOn M₁ m₁ Ω ∧ EqOn L₂ l₂ Ω ∧ EqOn M₂ m₂ Ω ∧
      (∀ x, 0 < M₁ x ∧ 0 < 3*L₁ x+2*M₁ x) ∧
      (∀ x, 0 < M₂ x ∧ 0 < 3*L₂ x+2*M₂ x) ∧
      EqOn L₂ L₁ Ωᶜ ∧ EqOn M₂ M₁ Ωᶜ ∧
      ∃ K, IsCompact K ∧ ∀ x∉K, L₁ x=0 ∧ M₁ x=1 ∧ L₂ x=0 ∧ M₂ x=1 := by
  obtain ⟨L₁,M₁,hL₁,hM₁,heL₁,heM₁,hp,hcL,hcM⟩ :=
    admissible_global_extension hc hU₁ h₁ l₁ m₁ hl₁ hm₁ hp₁
  obtain ⟨F,hF,_,heF⟩ := smooth_global_extension hc hU₂ h₂ l₂ hl₂
  obtain ⟨G,hG,_,heG⟩ := smooth_global_extension hc hU₂ h₂ m₂ hm₂
  let L₂ := Ω.piecewise F L₁
  let M₂ := Ω.piecewise G M₁
  have hL₂ : ContDiff ℝ (⊤ : ℕ∞) L₂ := by
    apply smooth_piecewise_all_jets Ω F L₁ hF hL₁
    intro n x hx
    rw [extension_jets heF (frontier_subset_closure hx),extension_jets heL₁ (frontier_subset_closure hx)]
    exact hjl n x hx
  have hM₂ : ContDiff ℝ (⊤ : ℕ∞) M₂ := by
    apply smooth_piecewise_all_jets Ω G M₁ hG hM₁
    intro n x hx
    rw [extension_jets heG (frontier_subset_closure hx),extension_jets heM₁ (frontier_subset_closure hx)]
    exact hjm n x hx
  have heL₂ : EqOn L₂ l₂ Ω := by
    intro x hx
    exact (piecewise_eq_of_mem Ω F L₁ hx).trans (heF.self_of_nhdsSet (subset_closure hx))
  have heM₂ : EqOn M₂ m₂ Ω := by
    intro x hx
    exact (piecewise_eq_of_mem Ω G M₁ hx).trans (heG.self_of_nhdsSet (subset_closure hx))
  refine ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,
    fun x hx => heL₁.self_of_nhdsSet (subset_closure hx),
    fun x hx => heM₁.self_of_nhdsSet (subset_closure hx),heL₂,heM₂,hp,?_,?_,?_,?_,?_,?_⟩
  · intro x
    by_cases hx : x∈Ω
    · rw [heL₂ hx,heM₂ hx]
      exact hp₂ x (subset_closure hx)
    · simpa only [L₂,M₂,piecewise_eq_of_notMem Ω _ _ hx] using hp x
  · intro x hx
    exact piecewise_eq_of_notMem Ω F L₁ hx
  · intro x hx
    exact piecewise_eq_of_notMem Ω G M₁ hx
  · exact closure Ω ∪ tsupport L₁ ∪ tsupport (fun x => M₁ x-1)
  · exact (hc.union hcL).union hcM
  · intro x hx
    have hO : x∉Ω := fun hh => hx (Or.inl (Or.inl (subset_closure hh)))
    have hL : L₁ x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inl (Or.inr hh)))
    have hz : (fun x => M₁ x-1) x=0 := image_eq_zero_of_notMem_tsupport (f := fun y => M₁ y-1) (fun hh => hx (Or.inr hh))
    have hM : M₁ x=1 := sub_eq_zero.mp hz
    exact ⟨hL,hM,(piecewise_eq_of_notMem Ω F L₁ hO).trans hL,
      (piecewise_eq_of_notMem Ω G M₁ hO).trans hM⟩
end ElasticityBoundary

end
end
section
noncomputable section
open Set MeasureTheory
namespace Elasticity

def BoundaryJetDetermination : Prop :=
  ∀ (Ω : Set X),Domain Ω → ∀ (l₁ m₁ l₂ m₂ : X → ℝ),
    Admissible Ω l₁ m₁ → Admissible Ω l₂ m₂ →
    DN Ω l₁ m₁=DN Ω l₂ m₂ →
    (∀ n : ℕ,∀ x∈frontier Ω,iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x) ∧
    (∀ n : ℕ,∀ x∈frontier Ω,iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x)

lemma Admissible.common_neighborhood {Ω : Set X} {l m : X → ℝ} (h : Admissible Ω l m) :
    ∃ U : Set X,IsOpen U ∧ closure Ω⊆U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) l U ∧ ContDiffOn ℝ (⊤ : ℕ∞) m U := by
  obtain ⟨U,hU,hsub,hLu⟩ := h.1
  obtain ⟨V,hV,hsub',hMv⟩ := h.2.1
  exact ⟨U∩V,hU.inter hV,subset_inter hsub hsub',hLu.mono inter_subset_left,
    hMv.mono inter_subset_right⟩

lemma admissible_of_global {Ω : Set X} {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hp : ∀ x,0 < m x ∧ 0<3*l x+2*m x) : Admissible Ω l m :=
  ⟨⟨univ,isOpen_univ,subset_univ _,hl.contDiffOn⟩,
    ⟨univ,isOpen_univ,subset_univ _,hm.contDiffOn⟩,fun x _ => hp x⟩

/-- The extension and DN-localization part of the boundary reduction is fully
proved. The all-jet premise here is explicitly the still-missing boundary
input; this declaration is NOT the main inverse theorem. -/
theorem admissible_common_exterior_of_jets {Ω : Set X} (hD : Domain Ω)
    (l₁ m₁ l₂ m₂ : X → ℝ) (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hjl : ∀ n : ℕ,∀ x∈frontier Ω,iteratedFDeriv ℝ n l₂ x=iteratedFDeriv ℝ n l₁ x)
    (hjm : ∀ n : ℕ,∀ x∈frontier Ω,iteratedFDeriv ℝ n m₂ x=iteratedFDeriv ℝ n m₁ x)
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
  obtain ⟨U₁,hU₁,hs₁,hl₁,hm₁⟩ := ha₁.common_neighborhood
  obtain ⟨U₂,hU₂,hs₂,hl₂,hm₂⟩ := ha₂.common_neighborhood
  obtain ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,hK⟩ :=
    ElasticityBoundary.common_exterior_of_all_jets hD.2.2.1.isCompact_closure
      hU₁ hU₂ hs₁ hs₂ l₁ m₁ l₂ m₂ hl₁ hm₁ hl₂ hm₂ ha₁.2.2 ha₂.2.2 hjl hjm
  refine ⟨L₁,M₁,L₂,M₂,hL₁,hM₁,hL₂,hM₂,heL₁,heM₁,heL₂,heM₂,hp₁,hp₂,hexL,hexM,?_,hK⟩
  exact (DN_coeff_congr hD.1.measurableSet heL₁ heM₁).trans
    (hDN.trans (DN_coeff_congr hD.1.measurableSet heL₂ heM₂).symm)
end Elasticity

end
end

end OAI
