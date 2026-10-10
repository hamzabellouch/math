import OAI.Probability.BenjaminiSchramm.PeakUpperExposure

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma connectionAvoidingHit_dependsOn (I J : Set E) (hJI : J ⊆ I)
    (u w : V) (T : Set V) :
    DependsOn (fun ω => ω ∈ connectionAvoidingHit G I J u w T) I := by
  intro ω η hωη
  have hJ : Set.inter ω J=Set.inter η J := by
    ext e
    change (ω e ∧ e ∈ J) ↔ (η e ∧ e ∈ J)
    by_cases hj : e ∈ J
    · exact and_congr (Iff.of_eq (hωη e (hJI hj))) Iff.rfl
    · simp only [hj,and_false]
  have hT := restrictedHit_dependsOn G I u T hωη
  exact congrArg₂ And (congrArg (fun ξ : Set E => Conn G ξ u w) hJ)
    (congrArg Not hT)

variable [Countable V] [Countable E]

lemma measurableSet_connectionAvoidingHit (I J : Set E) (u w : V) (T : Set V) :
    MeasurableSet (connectionAvoidingHit G I J u w T) := by
  have hm : Measurable (fun ω : Set E => ω ∩ J) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (((measurableSet_conn G u w).mem.comp hm).setOf).inter
    (measurableSet_restrictedHit G I u T).compl

theorem upper_cluster_peak_connection_comparison_in_domain (p : unitInterval)
    (D D' K J : Set E) (hKD : K ⊆ D) (hKD' : K ⊆ D') (hJD' : J ⊆ D') (x u w : V) (A T : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      law p (connectionAvoidingHit G D J u w T) ≤
    law p (({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) ∩
      {ω | Conn G (ω ∩ D') x w}) := by
  let C : Set (Set E) := {ω | cluster G (ω ∩ K) x=A}
  let I := D \ (K ∩ ballIncidentEdges G A)
  let B := restrictedSetHit G I A T
  let F := connectionAvoidingHit G I J u w T
  have hfresh : I ⊆ (K ∩ ballIncidentEdges G A)ᶜ := fun _ h => h.2
  have hCB : C ∩ (restrictedHit G D x T)ᶜ=C ∩ Bᶜ := by
    ext ω
    constructor
    · rintro ⟨hc,havoid⟩
      exact ⟨hc,fun hh => havoid ((upper_cluster_forbidden_hit_iff G ω D K hKD x A T hc hAT).mpr hh)⟩
    · rintro ⟨hc,havoid⟩
      exact ⟨hc,fun hh => havoid ((upper_cluster_forbidden_hit_iff G ω D K hKD x A T hc hAT).mp hh)⟩
  have hBc : MeasurableSet Bᶜ := (measurableSet_restrictedSetHit G I A T).compl
  have hdBc : DependsOn (fun ω => ω ∈ Bᶜ) I := by
    intro ω η hωη
    exact congrArg Not (restrictedSetHit_dependsOn G I A T hωη)
  have hFB : MeasurableSet (F ∩ Bᶜ) :=
    (measurableSet_connectionAvoidingHit G I J u w T).inter hBc
  have hdFB : DependsOn (fun ω => ω ∈ F ∩ Bᶜ) I := by
    intro ω η hωη
    exact congrArg₂ And (connectionAvoidingHit_dependsOn G I J hJI u w T hωη)
      (hdBc hωη)
  have hmon : law p (connectionAvoidingHit G D J u w T) ≤ law p F := by
    apply measure_mono
    rintro ω ⟨hc,havoid⟩
    refine ⟨hc,?_⟩
    rintro ⟨t,ht,hut⟩
    exact havoid ⟨t,ht,conn_mono G (Set.inter_subset_inter_right _ Set.sdiff_subset) hut⟩
  have hinc : C ∩ (F ∩ Bᶜ) ⊆
      (C ∩ (restrictedHit G D x T)ᶜ) ∩ {ω | Conn G (ω ∩ D') x w} := by
    rintro ω ⟨hc,hF,hB⟩
    have hp : ω ∈ C ∩ (restrictedHit G D x T)ᶜ := by
      rw [hCB]
      exact ⟨hc,hB⟩
    have hxu : Conn G (ω ∩ K) x u := by
      change u ∈ cluster G (ω ∩ K) x
      rwa [hc]
    exact ⟨hp,(conn_mono G (Set.inter_subset_inter_right _ hKD') hxu).trans
      (conn_mono G (Set.inter_subset_inter_right _ hJD') hF.1)⟩
  change law p (C ∩ (restrictedHit G D x T)ᶜ)*_ ≤ _
  conv_lhs => rw [hCB,upper_cluster_fresh_factor G p K I x A hfresh Bᶜ hBc hdBc]
  calc
    (law p C*law p Bᶜ)*law p (connectionAvoidingHit G D J u w T) ≤
        (law p C*law p Bᶜ)*law p F := mul_le_mul' le_rfl hmon
    _ = law p C*(law p F*law p Bᶜ) := by ring
    _ ≤ law p C*law p (F ∩ Bᶜ) := mul_le_mul' le_rfl
      (connection_avoiding_hit_complement_correlation G p I J hJI u w A T hfin)
    _ = law p (C ∩ (F ∩ Bᶜ)) :=
      (upper_cluster_fresh_factor G p K I x A hfresh (F ∩ Bᶜ) hFB hdFB).symm
    _ ≤ _ := measure_mono hinc

theorem upper_cluster_peak_connection_comparison (p : unitInterval)
    (D K J : Set E) (hKD : K ⊆ D) (x u w : V) (A T : Set V)
    (hu : u ∈ A) (hAT : Disjoint A T)
    (hJI : J ⊆ D \ (K ∩ ballIncidentEdges G A))
    (hfin : ∀ᵐ ω ∂law p,
      (cluster G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u).Finite) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) *
      law p (connectionAvoidingHit G D J u w T) ≤
    law p (({ω | cluster G (ω ∩ K) x=A} ∩ (restrictedHit G D x T)ᶜ) ∩
      {ω | Conn G (ω ∩ D) x w}) :=
  upper_cluster_peak_connection_comparison_in_domain G p D D K J hKD hKD
    (hJI.trans Set.sdiff_subset) x u w A T hu hAT hJI hfin

end Percolation.BenjaminiSchramm

end

end OAI
