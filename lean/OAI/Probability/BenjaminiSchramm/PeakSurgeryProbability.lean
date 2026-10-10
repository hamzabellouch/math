import OAI.Probability.BenjaminiSchramm.PeakFiniteEnergy
import OAI.Probability.UnimodularPercolation.Deformation.Derivatives

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def strictHeightPeakConnection (f : V → ℝ) (x z : V) : Set (Set E) :=
  {ω | Conn G ω x z ∧ ∀ y, Conn G ω z y → y ≠ z → f y < f z}

lemma measurableSet_strictHeightPeakConnection [Countable V] [Countable E]
    (f : V → ℝ) (x z : V) : MeasurableSet (strictHeightPeakConnection G f x z) := by
  exact ((measurableSet_conn G x z).mem.and (Measurable.forall fun y =>
    (measurableSet_conn G z y).mem.imp (measurable_const.imp measurable_const))).setOf

theorem lowerFrontierCell_strict_peak_probability [Countable V] [Countable E]
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ v, degree G v ≤ d)
    (p : unitInterval) (D S : Set V) (F : Finset V) (x u z : V)
    (f : V → ℝ) (hu : u ∈ F) (w : (openSimpleGraph G Set.univ).Walk u z)
    (havoid : ∀ v ∈ w.support, v ∉ S)
    (hbelow : ∀ v ∈ S ∪ (F : Set V), f v < f z)
    (hpeak : ∀ v ∈ w.support, v ≠ z → f v < f z) :
    law p (lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V))*
      ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(F.card+w.length+1))) ≤
        law p (lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V) ∩
          strictHeightPeakConnection G f x z) := by
  let A := lowerFrontierCell G (internalEdges G D) Set.univ x S (F : Set V)
  let Q := ballIncidentEdges G S
  let P := w.support.toFinset
  let W := F ∪ P
  let J := (incidentSupport G hloc W).filter fun e => e ∉ Q
  obtain ⟨l,hl,he,_ho⟩ := walk_lift_bonds G Set.univ w
  let σ : Set E := (l.toFinset : Set E)
  have hends (e : E) (he' : e ∈ l) (v : V) (hv : v ∈ G e) : v ∈ P :=
    List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_mem_edges
      (he ▸ List.mem_map_of_mem he') hv)
  have hmem (e : E) (he' : e ∈ l) : e ∈ J := by
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_incidentSupport G hloc W e).mpr
        ⟨(G e).out.1,Finset.mem_union_right F (hends e he' _ (Sym2.out_fst_mem _)),Sym2.out_fst_mem _⟩
    · rintro ⟨v,hv,hve⟩
      exact havoid v (List.mem_toFinset.mp (hends e he' v hve)) hv
  have hJ : (J : Set E) ⊆ Qᶜ := fun e he => (Finset.mem_filter.mp he).2
  have hJcard : J.card ≤ d*(F.card+w.length+1) := by
    have hP : P.card ≤ w.length+1 := by
      exact (List.toFinset_card_le w.support).trans_eq w.length_support
    calc
      _ ≤ (incidentSupport G hloc W).card := Finset.card_filter_le _ _
      _ ≤ W.card*d := incidentSupport_card_le G hloc d hd W
      _ ≤ (F.card+P.card)*d := Nat.mul_le_mul_right d (Finset.card_union_le F P)
      _ ≤ (F.card+(w.length+1))*d := Nat.mul_le_mul_right d (Nat.add_le_add_left hP F.card)
      _ = _ := by ring
  have hsub : A ∩ finiteBondPattern J σ ⊆ A ∩ strictHeightPeakConnection G f x z := by
    rintro η ⟨hη,hpat⟩
    have hSη : cluster G (η ∩ internalEdges G D) x=S := hη.1
    have hFη : openFrontier G η S=(F : Set V) := by
      simpa only [Set.inter_univ] using hη.2
    have hpath : Conn G η u z := hl.conn (fun e he' =>
      (Iff.of_eq (hpat e (hmem e he'))).mpr (List.mem_toFinset.mpr he'))
    have hclosed : ∀ e ∈ η, ∀ v ∈ G e, v ∈ (F : Set V) ∪ (P : Set V) →
        ∀ v' ∈ G e, v' ∈ S ∪ (F : Set V) ∪ (P : Set V) := by
      intro e heη v hv hvW v' hv'
      by_cases heQ : e ∈ Q
      · obtain ⟨a,ha,hae⟩ := heQ
        by_cases hvS : v' ∈ S
        · exact Or.inl (Or.inl hvS)
        · have hne : a ≠ v' := fun hh => hvS (hh ▸ ha)
          have hvF : v' ∈ openFrontier G η S :=
            ⟨hvS,a,ha,e,heη,(Sym2.mem_and_mem_iff hne).mp ⟨hae,hv'⟩⟩
          exact Or.inl (Or.inr (hFη ▸ hvF))
      · have heJ : e ∈ J := Finset.mem_filter.mpr
          ⟨(mem_incidentSupport G hloc W e).mpr
            ⟨v,Finset.mem_union.mpr hvW,hv⟩,heQ⟩
        have heσ : e ∈ σ := (Iff.of_eq (hpat e heJ)).mp heη
        exact Or.inr (hends e (List.mem_toFinset.mp heσ) v' hv')
    refine ⟨hη,?_⟩
    exact strict_peak_of_lower_frontier_surgery G η η D S (F : Set V) (P : Set V)
      x u z f hSη hFη hu (fun _ _ => rfl) hpath hclosed hbelow
        (fun v hv hvz => hpeak v (List.mem_toFinset.mp hv) hvz)
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  calc
    _ ≤ law p A*ENNReal.ofReal ((min (p : ℝ) (1-p))^J.card) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hδ hδ1 hJcard))
    _ ≤ law p (A ∩ finiteBondPattern J σ) := fresh_finiteBondPattern_cell_lower p Q A
      (measurableSet_lowerFrontierCell G _ _ x S _) (lowerFrontierCell_dependsOn G _ _ x S _) J hJ σ
    _ ≤ _ := measure_mono hsub

end Percolation.BenjaminiSchramm

end

end OAI
