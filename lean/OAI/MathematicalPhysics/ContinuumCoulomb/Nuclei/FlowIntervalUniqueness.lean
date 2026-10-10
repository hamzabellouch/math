import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalDomain

namespace OAI

/-! Closed-interval uniqueness for the lifted field. The local Lipschitz
estimate suffices; no global bound on the field is assumed. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

private theorem flow_box_unique_right {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    {B : Set FlowPhase} (hLip : LipschitzOnWith K f B)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hB : ∀ t ∈ Icc a b, α t ∈ B ∧ β t ∈ B) (h0 : α a = β a) :
    EqOn α β (Icc a b) := by
  have hr (γ : ℝ → FlowPhase)
      (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (f (γ t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt γ (f (γ t)) (Ici t) t := by
    apply (hγ t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => B)
    (fun _ _ => hLip) (HasDerivWithinAt.continuousOn hα) (hr α hα)
    (fun t ht => (hB t ⟨ht.1,ht.2.le⟩).1)
    (HasDerivWithinAt.continuousOn hβ) (hr β hβ)
    (fun t ht => (hB t ⟨ht.1,ht.2.le⟩).2) h0

private theorem flow_box_unique_left {f : FlowPhase → FlowPhase} {K : ℝ≥0}
    {B : Set FlowPhase} (hLip : LipschitzOnWith K f B)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hB : ∀ t ∈ Icc a b, α t ∈ B ∧ β t ∈ B) (h0 : α b = β b) :
    EqOn α β (Icc a b) := by
  have hl (γ : ℝ → FlowPhase)
      (hγ : ∀ t ∈ Icc a b, HasDerivWithinAt γ (f (γ t)) (Icc a b) t)
      (t : ℝ) (ht : t ∈ Ioc a b) : HasDerivWithinAt γ (f (γ t)) (Iic t) t := by
    apply (hγ t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => B)
    (fun _ _ => hLip) (HasDerivWithinAt.continuousOn hα) (hl α hα)
    (fun t ht => (hB t ⟨ht.1.le,ht.2⟩).1)
    (HasDerivWithinAt.continuousOn hβ) (hl β hβ)
    (fun t ht => (hB t ⟨ht.1.le,ht.2⟩).2) h0

theorem flow_open_interval_unique {f : FlowPhase → FlowPhase} {S : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S)
    {a b : ℝ} {α β : ℝ → FlowPhase}
    (hα : ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (hαS : MapsTo α (Icc a b) S)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (heq : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  classical
  let P : Icc a b → Prop := fun t => α t = β t
  have hcα : Continuous (fun t : Icc a b => α t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivWithinAt.continuousOn hα)
  have hcβ : Continuous (fun t : Icc a b => β t) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivWithinAt.continuousOn hβ)
  have hpclosed : IsClosed {t : Icc a b | P t} := isClosed_eq hcα hcβ
  have hloc : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_eventually_eq P).mpr
    intro t
    by_cases ht : P t
    · obtain ⟨L,B,hBt,hLip⟩ :=
        ((hf.contDiffAt (hS.mem_nhds (hαS t.property))).of_le
          (by norm_num : (1:ℕ∞ω) ≤ 4)).exists_lipschitzOnWith
      have hnear : ∀ᶠ u in 𝓝[Icc a b] (t:ℝ), α u ∈ B ∧ β u ∈ B :=
        ((hα t t.property).continuousWithinAt.eventually hBt).and
          ((hβ t t.property).continuousWithinAt.eventually (by
            have ht' : α t = β t := ht
            rw [←ht']
            exact hBt))
      obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhdsWithin_iff.mp hnear
      have hlocal : ∀ᶠ u in 𝓝[Icc a b] (t:ℝ), α u = β u := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (t:ℝ) hδ),
          self_mem_nhdsWithin] with u hu hui
        have hdist : dist u (t:ℝ) < δ := hu
        by_cases htu : (t:ℝ) ≤ u
        · have hsub : Icc (t:ℝ) u ⊆ Icc a b := Icc_subset_Icc t.property.1 hui.2
          have hB (v : ℝ) (hv : v ∈ Icc (t:ℝ) u) : α v ∈ B ∧ β v ∈ B := by
            apply hδB
            refine ⟨?_,hsub hv⟩
            rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hv.1)]
            rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr htu)] at hdist
            linarith [hv.2]
          exact flow_box_unique_right hLip
            (fun v hv => (hα v (hsub hv)).mono hsub)
            (fun v hv => (hβ v (hsub hv)).mono hsub) hB ht ⟨htu,le_rfl⟩
        · have hut : u ≤ (t:ℝ) := le_of_not_ge htu
          have hsub : Icc u (t:ℝ) ⊆ Icc a b := Icc_subset_Icc hui.1 t.property.2
          have hB (v : ℝ) (hv : v ∈ Icc u (t:ℝ)) : α v ∈ B ∧ β v ∈ B := by
            apply hδB
            refine ⟨?_,hsub hv⟩
            rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hv.2)]
            rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hut)] at hdist
            linarith [hv.1]
          exact flow_box_unique_left hLip
            (fun v hv => (hα v (hsub hv)).mono hsub)
            (fun v hv => (hβ v (hsub hv)).mono hsub) hB ht ⟨le_rfl,hut⟩
      rw [nhdsWithin_eq_map_subtype_coe t.property] at hlocal
      filter_upwards [hlocal] with u hu
      exact propext (iff_of_true hu ht)
    · filter_upwards [hpclosed.isOpen_compl.mem_nhds ht] with u hu
      exact propext (iff_of_false hu ht)
  have : PreconnectedSpace (Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  intro t ht
  have hh := hloc.apply_eq_of_preconnectedSpace ⟨t,ht⟩ ⟨t₀,ht₀⟩
  change P ⟨t,ht⟩
  rw [hh]
  exact heq

end ContinuumCoulomb

end

end OAI
