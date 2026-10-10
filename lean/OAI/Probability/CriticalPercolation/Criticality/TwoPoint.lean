import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteSumConnection
import OAI.Probability.CriticalPercolation.Criticality.DeleteImageIso

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

def twoPoint (p : unitInterval) (o v : V) : ℝ := (G.law p).real (G.hitEvent o {v})

lemma hit_singleton_eq (o v : V) :
    G.hitEvent o {v} = {ω | (G.openGraph ω).Reachable o v} := by
  ext ω
  simp only [BondGraph.hitEvent,Set.mem_ofPred_eq,Set.inter_singleton_nonempty,BondGraph.cluster]

lemma twoPoint_nonneg (p : unitInterval) (o v : V) : 0 ≤ twoPoint G p o v := measureReal_nonneg

lemma finite_contraction [Fintype E] [Nonempty V] {p : ℝ} (hp : p ∈ Icc 0 1)
    (N : ℕ) (a : ℝ) (ha : a < 1)
    (hdom : ∀ o : V, ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧
      boundaryFlux G p o Sᶜ ≤ a) (A : Finset V) (o : V) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤ N / (1-a) := by
  let f := fun y => ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable y v)
  have hb : BddAbove (Set.range f) := ⟨A.card,by
    rintro _ ⟨y,rfl⟩
    calc
      _ ≤ ∑ _v ∈ A, (1:ℝ) := Finset.sum_le_sum fun v _ => probability_le_one hp _
      _ = _ := by simp⟩
  let M := sSup (Set.range f)
  have hM : ∀ y, f y ≤ M := fun y => le_csSup hb ⟨y,rfl⟩
  have hM0 : 0 ≤ M := (Finset.sum_nonneg (fun _ _ => probability_nonneg hp _)).trans (hM o)
  have hcon : M ≤ N + a * M := by
    apply csSup_le (Set.range_nonempty f)
    rintro _ ⟨y,rfl⟩
    obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
    exact (finite_sum_connection_le G hp A S hS y hy M hM).trans
      (add_le_add (Nat.cast_le.mpr hn) (mul_le_mul_of_nonneg_right hphi hM0))
  apply (hM o).trans
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith

lemma finite_probability_connection (p : unitInterval) (K : Set E) (hK : K.Finite)
    (o v : V) :
    letI := hK.fintype
    probability (p : ℝ) (fun ω => ((G.restrictEdges K).openGraph ω).Reachable o v) =
      (G.law p).real {ω | K ∩ ω ∈ G.hitEvent o {v}} := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK,hit_singleton_eq]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,G.restrictEdges_openGraph]

theorem subcritical_susceptibility [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ C : ℝ, ∀ (A : Finset V) (o : V), ∑ v ∈ A, twoPoint G p o v ≤ C := by
  obtain ⟨N,a,ha,hdom⟩ := uniform_subcritical_domains G hl hq p hp
  refine ⟨N/(1-a),?_⟩
  intro A o
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  have hf (n : ℕ) : ∑ v ∈ A, (G.law p).real {ω | K n ∩ ω ∈ G.hitEvent o {v}} ≤
      N/(1-a) := by
    let := (K.finite n).fintype
    have hd : ∀ y : V, ∃ S : Set V, S.Finite ∧ y ∈ S ∧ S.ncard ≤ N ∧
        boundaryFlux (G.restrictEdges (K n)) (p : ℝ) y Sᶜ ≤ a := by
      intro y
      obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
      exact ⟨S,hS,hy,hn,(restricted_boundaryFlux_le_phi G hl p S hS y (K n) (K.finite n)).trans hphi⟩
    have hh := finite_contraction (G.restrictEdges (K n)) p.property N a ha hd A o
    simpa only [finite_probability_connection G p (K n) (K.finite n)] using hh
  have ht : Tendsto (fun n => ∑ v ∈ A, (G.law p).real
      {ω | K n ∩ ω ∈ G.hitEvent o {v}}) atTop (𝓝 (∑ v ∈ A, twoPoint G p o v)) := by
    apply tendsto_finsetSum
    intro v _
    simpa only [BondGraph.law,BernoulliProduct.law_const,twoPoint] using
      G.tendsto_real_hitEvent_exhaustion (fun _ : E => p) K o {v}
  exact le_of_tendsto ht (Eventually.of_forall hf)

theorem summable_subcritical_twoPoint [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    Summable (twoPoint G p o) := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨C,hC⟩ := subcritical_susceptibility G hl hq p hp
  exact summable_of_sum_le (twoPoint_nonneg G p o) (fun A => hC A o)

end CriticalPercolation.Sharpness
end
end CurrentModule10

end

end OAI
