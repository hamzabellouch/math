import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Gluing.SlotContour

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation

theorem infinite_cluster_of_reached_marks {V I : Type*} (H : SimpleGraph V)
    (seed : Finset V) (J : Set I) (hJ : J.Infinite) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ i∈J, ∃ v∈mark i, ∃ a∈seed, H.Reachable a v) :
    ∃ a∈seed, ({v | H.Reachable a v} : Set V).Infinite := by
  let := hJ.to_subtype
  have hex (i : J) : ∃ v∈mark i, ∃ a∈seed, H.Reachable a v := hreach i i.2
  choose v hv using hex
  have hinj : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) (hv i).1 (hij ▸ (hv j).1)
  have hi : (Set.range v).Infinite := Set.infinite_range_of_injective hinj
  by_contra hn
  push Not at hn
  have hf : (⋃ a∈seed, {v | H.Reachable a v}).Finite :=
    seed.finite_toSet.biUnion (fun a ha => hn a ha)
  apply hi.not_finite (hf.subset ?_)
  rintro _ ⟨i,rfl⟩
  obtain ⟨a,ha,hr⟩ := (hv i).2
  exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,hr⟩⟩

namespace BondGraph
variable {V E I : Type*} (G : BondGraph V E)

lemma percolation_of_infinite_marks (p : unitInterval) (B : Set (Set E))
    (J : Set E → Set I) (seed : Finset V) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ ω∈B, ∀ i∈J ω, ∃ v∈mark i, ∃ a∈seed,
      (G.openGraph ω).Reachable a v)
    (hpos : 0 < (G.law p).real (B∩{ω | (J ω).Infinite})) :
    0<G.law p G.percolates := by
  have hsub : B∩{ω | (J ω).Infinite}⊆G.percolates := by
    intro ω hω
    obtain ⟨a,_ha,hi⟩ := infinite_cluster_of_reached_marks (G.openGraph ω) seed
      (J ω) hω.2 mark hdis (hreach ω hω.1)
    exact ⟨a,hi⟩
  exact (ENNReal.toReal_pos_iff.mp hpos).1.trans_le (measure_mono hsub)

theorem no_subcritical_good_exploration (p : unitInterval) (hp : p<G.criticalProbability)
    (M : ℕ → MeasurableSpace (Set E)) (hM : Monotone M)
    (F : ℕ → Set (Set E)) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set (Set E)) (hmB : MeasurableSet[M 0] B) (hB : 0<(G.law p).real B)
    (S : Set E → Set Boundary.Grid)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, Boundary.quadrant v)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F (Boundary.gridSlot z))
    (seed : Finset V) (mark : Boundary.Grid → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ ω∈B, ∀ i∈S ω, ∃ v∈mark i, ∃ a∈seed,
      (G.openGraph ω).Reachable a v)
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B →
      (G.law p).real (A∩F n)≤q^4*(G.law p).real A) : False := by
  let : IsProbabilityMeasure (G.law p) := by
    unfold law
    infer_instance
  have hi := Boundary.infinitely_many_good_from_tests (G.law p) M hM F hF B hmB hB S
    hroot hquad hchild q hq₀ hq hcond
  have hperc := G.percolation_of_infinite_marks p B S seed mark hdis hreach hi
  exact (not_le_of_gt hp) (sInf_le hperc)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
