import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PartitionGeometry
import OAI.Combinatorics.ThinTrees.Metric.Response

namespace OAI

/-! Partition response. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma lift_restrict_crossing (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n)) :
    liftEdges F (crossing (H.restrict F) p)=crossing H p ∩ F := by
  ext e
  simp only [liftEdges,mem_map,mem_crossing,mem_inter]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,embedding_mem F i⟩
  · rintro ⟨hi,he⟩
    obtain ⟨i,rfl⟩ := embedding_surj F he
    exact ⟨i,hi,rfl⟩

lemma restrict_crossing_card (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n)) :
    (crossing (H.restrict F) p).card=(crossing H p ∩ F).card := by
  rw [←lift_restrict_crossing,liftEdges,card_map]

lemma lift_restrict_crossing_filter (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n))
    (b : Fin m → Prop) :
    liftEdges F ((crossing (H.restrict F) p).filter (fun e => b (edgeEmbedding F e)))=
      (crossing H p ∩ F).filter b := by
  rw [←lift_restrict_crossing,liftEdges,liftEdges,filter_map]
  congr 1

lemma restrict_bad_card (H : MultiGraph n m) (F : Finset (Fin m)) (p : Setoid (Fin n))
    (b : Fin m → Prop) :
    ((crossing (H.restrict F) p).filter (fun e => b (edgeEmbedding F e))).card=
      ((crossing H p ∩ F).filter b).card := by
  rw [←lift_restrict_crossing_filter,liftEdges,card_map]

open MetricTests

theorem finite_chain_response :
    ∃r0 : ℕ, 2 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (J : Finset (Setoid (Fin n))),
      IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict F).EdgeConnectedReal univ (r/2:ℕ) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ F).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ F).card := by
  obtain ⟨r0,hr0,hresp⟩ := simultaneous_metric_response
  refine ⟨r0,hr0,?_⟩
  intro r hr n m H hn hconn F J hJ hlocal hroot s hs hsR
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨f,hf,hfroot,hfmem,hfsurj⟩ := enumerate_chain J hJ
  let P := toChain f hf
  have hpF : P.parts J.card={univ} := by
    change parts (f J.card)={univ}
    rw [hfroot,parts_top]
  have hpL : ∀i ≤ J.card, ∀A ∈ P.parts i, (H.restrict F).EdgeConnectedReal A (r/2:ℕ) := by
    intro i _ A hA
    rcases hfmem i with hi | hi
    · exact hlocal (f i) hi A hA
    · change A ∈ parts (f i) at hA
      rw [hi,parts_top,mem_singleton] at hA
      exact hA ▸ hroot
  obtain ⟨Y,hY,hYP,hbad⟩ := hresp r hr n m H hn hconn F P J.card hpF hpL s hs hsR
  refine ⟨Y,hY,hYP,?_⟩
  intro p hp
  obtain ⟨i,hi,hfi⟩ := hfsurj p hp
  have hh := hbad i hi.le
  rw [toChain_crossing,hfi,restrict_crossing_card] at hh
  have he := restrict_bad_card H F p
    (fun e => ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)
  have hinc (e : Fin F.card) : (H.restrict F).incidence e=H.incidence (edgeEmbedding F e) := by
    ext v
    simp only [MultiGraph.incidence,MultiGraph.restrict,Pi.sub_apply]
  simp_rw [hinc] at hh
  convert hh using 1
  congr 1
  convert he.symm using 1 <;> congr 1 <;> ext e <;> simp only [mem_filter]

end
end AlgorithmicThinTrees.Partitions
end

end OAI
