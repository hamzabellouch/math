import OAI.Probability.BenjaminiSchramm.FiniteEnergyModification
import OAI.Probability.BenjaminiSchramm.PeakExposureComparison
import OAI.Probability.BenjaminiSchramm.PeakSurgeryGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma mixed_root_surgery (D J γ : Set E) (P T : Set V)
    (hJD : J ⊆ D) (hγJ : γ ⊆ J) (hγP : γ ⊆ internalEdges G P)
    (hPT : Disjoint P T) (u v w : V) (huP : u ∈ P) (hγuv : Conn G γ u v)
    (ω : Set E) (hvw : Conn G (ω ∩ J) v w)
    (havoid : ω ∉ restrictedHit G D v T) :
    ∃ η : Set E, η ∈ connectionAvoidingHit G D J u w T ∧
      ∀ e ∉ ballIncidentEdges G P, (e ∈ ω)=(e ∈ η) := by
  let S := cluster G (ω ∩ D) v
  let Q := ballIncidentEdges G (P \ S)
  let η := (ω \ Q) ∪ γ
  have hvS : v ∈ S := mem_cluster_self G _ v
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hzT
    exact havoid ⟨z,hzT,hz⟩
  have hkeep : (ω ∩ J) ∩ internalEdges G S ⊆ η ∩ J := by
    rintro e ⟨⟨he,heJ⟩,heS⟩
    refine ⟨Or.inl ⟨he,?_⟩,heJ⟩
    rintro ⟨z,⟨_,hzS⟩,hze⟩
    exact hzS (heS z hze)
  have hvw' : Conn G (η ∩ J) v w := by
    have hh := conn_restrict_cluster_of_subset G (ω ∩ D) v
      (Set.inter_subset_inter_right _ hJD) (mem_cluster_self G _ v) hvw
    exact conn_mono G hkeep hh
  have hγsub : γ ⊆ η ∩ J := fun e he => ⟨Or.inr he,hγJ he⟩
  have huv : Conn G (η ∩ J) u v := conn_mono G hγsub hγuv
  have hclosed : ∀ e ∈ η ∩ D, ∀ z ∈ G e, z ∈ S ∪ P → ∀ z' ∈ G e, z' ∈ S ∪ P := by
    intro e he z hze hz z' hz'e
    rcases he.1 with heω | heγ
    · rcases hz with hzS | hzP
      · by_cases hzz' : z=z'
        · exact Or.inl (hzz' ▸ hzS)
        · have heq : G e=s(z,z') := (Sym2.mem_and_mem_iff hzz').mp ⟨hze,hz'e⟩
          exact Or.inl ((edge_cluster_sides G (ω ∩ D) v ⟨heω.1,he.2⟩ heq).mp hzS)
      · by_cases hzS : z ∈ S
        · by_cases hzz' : z=z'
          · exact Or.inl (hzz' ▸ hzS)
          · have heq : G e=s(z,z') := (Sym2.mem_and_mem_iff hzz').mp ⟨hze,hz'e⟩
            exact Or.inl ((edge_cluster_sides G (ω ∩ D) v ⟨heω.1,he.2⟩ heq).mp hzS)
        · exact (heω.2 ⟨z,⟨hzP,hzS⟩,hze⟩).elim
    · exact Or.inr (hγP heγ z' hz'e)
  have hηavoid : η ∉ restrictedHit G D u T := by
    rintro ⟨z,hzT,huz⟩
    have hz := conn_mem_of_open_closed G (η ∩ D) (S ∪ P) u (Or.inr huP) hclosed z huz
    rcases hz with hzS | hzP
    · exact Set.disjoint_left.mp hST hzS hzT
    · exact Set.disjoint_left.mp hPT hzP hzT
  refine ⟨η,⟨huv.trans hvw',hηavoid⟩,?_⟩
  intro e heP
  have heQ : e ∉ Q := fun ⟨z,hz,hze⟩ => heP ⟨z,hz.1,hze⟩
  have heγ : e ∉ γ := by
    intro he
    exact heP ⟨(G e).out.1,hγP he _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩
  apply propext
  change e ∈ ω ↔ (e ∈ ω ∧ e ∉ Q) ∨ e ∈ γ
  constructor
  · intro he
    exact Or.inl ⟨he,heQ⟩
  · rintro (⟨he,_⟩ | he)
    · exact he
    · exact (heγ he).elim

theorem mixed_root_connection_probability [Countable V] [Countable E]
    (hl : LocallyFinite G) (p : unitInterval) (D J γ : Set E) (P : Finset V) (T : Set V)
    (hJD : J ⊆ D) (hγJ : γ ⊆ J) (hγP : γ ⊆ internalEdges G (P : Set V))
    (hPT : Disjoint (P : Set V) T) (u v w : V) (huP : u ∈ P) (hγuv : Conn G γ u v) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(incidentSupport G hl P).card)*
      law p (connectionAvoidingHit G D J v w T) ≤ law p (connectionAvoidingHit G D J u w T) := by
  apply finite_energy_modification_bound p (incidentSupport G hl P) _ _
    (measurableSet_connectionAvoidingHit G D J u w T)
  rintro ω ⟨hvw,havoid⟩
  obtain ⟨η,hη,hagree⟩ := mixed_root_surgery G D J γ (P : Set V) T hJD hγJ hγP hPT
    u v w huP hγuv ω hvw havoid
  refine ⟨η,hη,fun e he => hagree e ?_⟩
  exact fun hh => he ((mem_incidentSupport G hl P e).mpr hh)

end Percolation.BenjaminiSchramm

end

end OAI
