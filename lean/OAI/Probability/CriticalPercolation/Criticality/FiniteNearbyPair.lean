import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteInterpolationMeasure
import OAI.Probability.CriticalPercolation.GraphGeometry.DeletedTailGeometry
import OAI.Probability.CriticalPercolation.Criticality.BandScale

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_finset_sum {J : Type*} (w : E → A → ℝ) (S : Finset J)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j∈S, f j ω) = ∑ j∈S, expect w (f j) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm
end FiniteProduct
namespace BondGraph
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma expected_exteriorTailCount_lower (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (U : Set V) (B : Finset V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) (hU : U.toFinset.card<s^2) :
    expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ) ≤
      expect w (fun ω => exteriorTailCount (G.openGraph ω) U B s) := by
  have hcost : U.toFinset.card + U.toFinset.card*D*(s-1)≤ s^2+D*s^3 := by
    calc _ ≤ s^2+s^2*D*s := by gcongr; omega
         _ = _ := by ring
  have hg := expect_mono hn (fun ω => G.tailCount_le_exterior_add_damage (G.openGraph ω)
    (G.openGraph_mono (Set.subset_univ _)) U B s D hD)
  rw [expect_add,expect_const w hw] at hg
  have hr : ((U.toFinset.card + U.toFinset.card*D*(s-1):ℕ):ℝ)≤(s^2+D*s^3:ℕ) :=
    Nat.cast_le.mpr hcost
  linarith

lemma finite_nearby_pair_expect (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    expect w (fun ω => if s≤(G.cluster ω z).toFinset.card ∧
      (G.cluster ω z).toFinset.card<s^2 then 1 else 0) *
      (expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ)) ≤
    ∑ y∈B, expect w (fun ω => if ω∈G.twoClusterEvent y z s then 1 else 0) := by
  let band (U : Set V) := s≤U.toFinset.card ∧ U.toFinset.card<s^2
  let T := expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ)
  let F (U : Set V) (H : SimpleGraph V) := if band U then
    ∑ y∈B, (if y∉U ∧ s≤(component H y).toFinset.card then (1:ℝ) else 0) else 0
  have hsp := G.finite_spatialMarkov w hw {z} ∅ F
  simp only [delete_empty,roots_singleton] at hsp
  have hleft : expect w (fun ω => if band (G.cluster ω z) then
      exteriorTailCount (G.openGraph ω) (G.cluster ω z) B s else 0) =
      expect w (fun ω => if band (G.cluster ω z) then
        expect w (fun ω' => exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s) else 0) := by
    calc
      _ = expect w (fun ω => F (component (G.openGraph ω) z)
          (delete (G.openGraph ω) (component (G.openGraph ω) z))) := rfl
      _ = _ := hsp.trans (by
        congr 1
        funext ω
        change (expect w (fun ω' => if band (G.cluster ω z) then
          exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s else 0)) = _
        by_cases hb : band (G.cluster ω z)
        · simp only [ite_eq_left hb]
        · simp only [ite_eq_right hb,expect_zero])
  have hlower : expect w (fun ω => if band (G.cluster ω z) then (1:ℝ) else 0)*T ≤
      expect w (fun ω => if band (G.cluster ω z) then
        expect w (fun ω' => exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s) else 0) := by
    rw [← expect_mul_const]
    apply expect_mono hn
    intro ω
    split_ifs with hb
    · simp only [one_mul]
      exact G.expected_exteriorTailCount_lower w hw hn (G.cluster ω z) B s D hD hb.2
    · simp only [zero_mul,le_refl]
  rw [← hleft] at hlower
  refine hlower.trans ?_
  rw [← expect_finset_sum]
  apply expect_mono hn
  intro ω
  by_cases hb : band (G.cluster ω z)
  · rw [ite_eq_left hb]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
    · have ht : {e | ω e}∈G.twoClusterEvent y z s := by
        refine ⟨⟨fun hh => hy.1 hh.symm,?_⟩,?_⟩
        · apply (G.clusterTail_iff_card _ y s).mpr
          have hh : component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y =
              G.cluster {e | ω e} y := component_delete_component (G.openGraph {e | ω e}) z y hy.1
          simpa only [hh] using hy.2
        · exact (G.clusterTail_iff_card _ z s).mpr hb.1
      change (if y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
        then (1:ℝ) else 0) ≤ (if {e | ω e}∈G.twoClusterEvent y z s then 1 else 0)
      rw [ite_eq_left hy,ite_eq_left ht]
    · change (if y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
        then (1:ℝ) else 0) ≤ _
      rw [ite_eq_right hy]
      split_ifs <;> norm_num
  · rw [ite_eq_right hb]
    apply Finset.sum_nonneg
    intro _ _
    split_ifs <;> norm_num

lemma finite_nearby_pair (p : unitInterval) (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) :
    (G.law p).real (G.clusterBand z s) *
      ((∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
  let w := fun _ : E => BernoulliProduct.bitWeight p
  have hh := G.finite_nearby_pair_expect w (fun _ => BernoulliProduct.bitWeight_sum p)
    (fun _ => BernoulliProduct.bitWeight_nonneg p) B z s D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v)
  have hreal (A : Set (Set E)) : expect w (fun ω => if ω∈A then 1 else 0) =
      (G.law p).real A := by
    calc
      _ = FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
          (fun ω => ω ∈ A) := by
        unfold FiniteProduct.prob
        congr 1
      _ = _ := by
        simpa only [law,← BernoulliProduct.law_const] using
          (BernoulliProduct.prob_eq_real (fun _ : E => p) A)
  have hband : expect w (fun ω => if s≤(G.cluster ω z).toFinset.card ∧
      (G.cluster ω z).toFinset.card<s^2 then 1 else 0) = (G.law p).real (G.clusterBand z s) := by
    rw [← hreal]
    congr 1
    funext ω
    congr 1
    apply propext
    change _ ↔ {e | ω e}∈G.clusterTail z s ∧ {e | ω e}∉G.clusterTail z (s^2)
    rw [G.clusterTail_iff_card,G.clusterTail_iff_card,not_le]
    rfl
  have htail : expect w (fun ω => tailCount (G.openGraph ω) B s) =
      ∑ y∈B, (G.law p).real (G.clusterTail y s) := by
    unfold tailCount
    rw [expect_finset_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hreal]
    congr 1
    funext ω
    congr 1
    exact propext (G.clusterTail_iff_card {e | ω e} y s).symm
  rw [hband,htail] at hh
  simpa only [hreal] using hh

end BondGraph
end CriticalPercolation
end
end
end

end OAI
