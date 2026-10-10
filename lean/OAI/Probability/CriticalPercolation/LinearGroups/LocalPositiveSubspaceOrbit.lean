import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.LocalProjectiveAction

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
variable [CompleteSpace K] [FiniteDimensional K V]

omit [CompleteSpace K] in
lemma small_intersection_rank (U W : Submodule K V)
    (he : finrank K U=finrank K W) (hne : U≠W) :
    finrank K ↥(U⊓W)<finrank K U := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro hi
  have hle : U≤W := by rw [←hi]; exact inf_le_right
  exact hne (Submodule.eq_of_le_of_finrank_eq hle he)

lemma finite_positive_subspaces (μ : Measure (Space K V)) [IsFiniteMeasure μ]
    (d : ℕ) (ε : ℝ≥0∞) (hε : ε≠0)
    (hnull : ∀ W : Submodule K V, finrank K W<d → μ (subspace W)=0) :
    {W : Submodule K V | finrank K W=d ∧ ε≤μ (subspace W)}.Finite := by
  let T := {W : Submodule K V | finrank K W=d ∧ ε≤μ (subspace W)}
  by_contra hfin
  have hinf : T.Infinite := hfin
  let : Infinite T := hinf.to_subtype
  have hdis : Pairwise (AEDisjoint μ on (fun W:T => subspace W.val)) := by
    intro U W hne
    change μ (subspace U.val∩subspace W.val)=0
    rw [←subspace_inf]
    apply hnull
    rw [←U.property.1]
    apply small_intersection_rank _ _ (U.property.1.trans W.property.1.symm)
    exact fun he => hne (Subtype.ext he)
  have hs := tsum_measure_le_measure_univ
    (fun W:T => (measurable_subspace W.val).nullMeasurableSet) hdis
  have hc : (∑' _ : T, ε)≤∑' W:T, μ (subspace W.val) :=
    ENNReal.tsum_le_tsum (fun W => W.property.2)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hε] at hc
  exact (measure_ne_top μ Set.univ) (top_unique (hc.trans hs))

omit [CompleteSpace K] in
lemma exists_minimal_positive_subspace (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (h : ∃ W : Submodule K V, W≠⊤ ∧ μ (subspace W)≠0) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧ μ (subspace W)≠0 ∧
      ∀ U : Submodule K V, finrank K U<finrank K W → μ (subspace U)=0 := by
  have hex : ∃ d:ℕ, ∃ W : Submodule K V,
      finrank K W=d ∧ W≠⊤ ∧ μ (subspace W)≠0 := by
    obtain ⟨W,hW,hμ⟩ := h
    exact ⟨finrank K W,W,rfl,hW,hμ⟩
  obtain ⟨W,hWd,hWt,hWμ⟩ := Nat.find_spec hex
  refine ⟨W,?_,hWt,hWμ,?_⟩
  · intro he
    exact hWμ (by simp [he])
  · intro U hU
    by_contra hUμ
    have hut : U≠⊤ := by
      intro he
      have hh := Submodule.finrank_le W
      rw [he,finrank_top] at hU
      omega
    have hi := Nat.find_min' hex ⟨U,rfl,hut,hUμ⟩
    omega

lemma measure_subspace_map_eq (μ : Measure (Space K V))
    (a : V ≃L[K] V) (hμ : Measure.map (action a) μ=μ)
    (W : Submodule K V) :
    μ (subspace (W.map a.toLinearEquiv.toLinearMap))=μ (subspace W) := by
  conv_lhs => rw [←hμ]
  rw [Measure.map_apply (continuous_action a).measurable
    (measurable_subspace _),preimage_action_subspace]

lemma exists_finite_positive_subspace_orbit {G : Type*} [Group G]
    (ρ : G →* (V ≃L[K] V)) (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ)
    (h : ∃ W : Submodule K V, W≠⊤ ∧ μ (subspace W)≠0) :
    ∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧
      (Set.range (fun g => W.map (ρ g).toLinearEquiv.toLinearMap)).Finite := by
  obtain ⟨W,hWb,hWt,hWμ,hnull⟩ := exists_minimal_positive_subspace μ h
  refine ⟨W,hWb,hWt,?_⟩
  apply (finite_positive_subspaces μ (finrank K W) _ hWμ hnull).subset
  rintro U ⟨g,rfl⟩
  refine ⟨(ρ g).toLinearEquiv.finrank_map_eq W,?_⟩
  exact (measure_subspace_map_eq μ (ρ g) (hμ g) W).ge

end CriticalPercolation.LocalProjective
end
end

end OAI
