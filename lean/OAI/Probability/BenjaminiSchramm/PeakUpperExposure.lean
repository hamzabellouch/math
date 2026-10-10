import OAI.Probability.BenjaminiSchramm.PeakComplementCorrelation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restricted_exactCluster_dependsOn_inter (K : Set E) (x : V) (A : Set V) :
    DependsOn (fun ω => cluster G (ω ∩ K) x=A) (K ∩ ballIncidentEdges G A) := by
  intro ω η hωη
  have hh : ∀ e ∈ ballIncidentEdges G A,
      (e ∈ Set.inter ω K)=(e ∈ Set.inter η K) := by
    intro e he
    change (ω e ∧ e ∈ K)=(η e ∧ e ∈ K)
    by_cases hk : e ∈ K
    · exact congrArg (fun P : Prop => P ∧ e ∈ K) (hωη e ⟨hk,he⟩)
    · simp only [hk,and_false]
  have h := (criticalModel G).exactCluster_dependsOn x A hh
  change ((criticalModel G).cluster (Set.inter ω K) x=A) =
    ((criticalModel G).cluster (Set.inter η K) x=A) at h
  rw [criticalModel_cluster,criticalModel_cluster] at h
  exact h

lemma restrictedSetHit_dependsOn (I : Set E) (A T : Set V) :
    DependsOn (fun ω => ω ∈ restrictedSetHit G I A T) I := by
  intro ω η hωη
  have he : Set.inter ω I=Set.inter η I := by
    ext e
    change (ω e ∧ e ∈ I) ↔ (η e ∧ e ∈ I)
    by_cases hi : e ∈ I
    · exact and_congr (Iff.of_eq (hωη e hi)) Iff.rfl
    · simp only [hi,and_false]
  exact congrArg (fun ξ : Set E => ∃ v ∈ A, ∃ t ∈ T, Conn G ξ v t) he

theorem upper_cluster_forbidden_hit_iff (ω : Set E) (D K : Set E) (hKD : K ⊆ D)
    (x : V) (A T : Set V) (hA : cluster G (ω ∩ K) x=A) (hAT : Disjoint A T) :
    ω ∈ restrictedHit G D x T ↔
      ω ∈ restrictedSetHit G (D \ (K ∩ ballIncidentEdges G A)) A T := by
  constructor
  · rintro ⟨t,ht,hxt⟩
    have hxA : x ∈ A := hA ▸ mem_cluster_self G _ x
    have htA : t ∉ A := fun h => Set.disjoint_left.mp hAT h ht
    obtain ⟨z,hz,hzt⟩ := conn_last_exit_frontier G (ω ∩ D) A hxA htA hxt
    obtain ⟨hzA,u,hu,e,he,heq⟩ := hz
    have hek : e ∉ K := by
      intro hk
      apply hzA
      rw [←hA]
      have hxu : Conn G (ω ∩ K) x u := by
        change u ∈ cluster G (ω ∩ K) x
        rwa [hA]
      exact hxu.tail ⟨e,⟨he.1,hk⟩,heq⟩
    have huz : Conn G (ω ∩ (D \ (K ∩ ballIncidentEdges G A))) u z :=
      (conn_refl G _ u).tail ⟨e,⟨he.1,he.2,fun h => hek h.1⟩,heq⟩
    refine ⟨u,hu,t,ht,huz.trans (conn_mono G ?_ hzt)⟩
    rintro e ⟨⟨he,heD⟩,heA⟩
    exact ⟨he,heD,fun h => heA h.2⟩
  · rintro ⟨u,hu,t,ht,hut⟩
    have hxu : Conn G (ω ∩ K) x u := by
      change u ∈ cluster G (ω ∩ K) x
      rwa [hA]
    refine ⟨t,ht,(conn_mono G (Set.inter_subset_inter_right _ hKD) hxu).trans ?_⟩
    exact conn_mono G (Set.inter_subset_inter_right _ Set.sdiff_subset) hut

variable [Countable V] [Countable E]

lemma upper_cluster_fresh_factor (p : unitInterval) (K I : Set E) (x : V) (A : Set V)
    (hfresh : I ⊆ (K ∩ ballIncidentEdges G A)ᶜ)
    (B : Set (Set E)) (hB : MeasurableSet B)
    (hdB : DependsOn (fun ω => ω ∈ B) I) :
    law p ({ω | cluster G (ω ∩ K) x=A} ∩ B) =
      law p {ω | cluster G (ω ∩ K) x=A} * law p B := by
  have hlaw : CriticalPercolation.BernoulliProduct.law (fun _ : E => p)=law p :=
    CriticalPercolation.BernoulliProduct.law_const p
  rw [←hlaw]
  exact CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ : E => p) (K ∩ ballIncidentEdges G A) _ B
    (measurableSet_restricted_exactCluster G K x A) hB
    (restricted_exactCluster_dependsOn_inter G K x A) (DependsOn.mono hfresh hdB)

end Percolation.BenjaminiSchramm

end

end OAI
