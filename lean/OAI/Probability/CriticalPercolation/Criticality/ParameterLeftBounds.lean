import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.Criticality.ExhaustionEvents
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.Criticality.SharpnessPhi

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

lemma real_finiteWitness_mono_parameter (A : Set (Set E)) (hA : IsUpperSet A)
    (hw : BernoulliProduct.HasFiniteOpenWitness A) {p q : unitInterval} (hpq : p ≤ q) :
    (G.law p).real A ≤ (G.law q).real A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  have hfinite (n : ℕ) : (G.law p).real {ω | K n ∩ ω ∈ A} ≤
      (G.law q).real {ω | K n ∩ ω ∈ A} := by
    let := (K.finite n).fintype
    let F : Set (K n) → Prop := fun τ => Subtype.val '' τ ∈ A
    have hf : ∀ s t, s ⊆ t → F s → F t := fun _ _ h => hA (Set.image_mono h)
    have hh := Sharpness.probability_monotoneOn F hf p.property q.property hpq
    change Sharpness.probability (p:ℝ) F ≤ Sharpness.probability (q:ℝ) F at hh
    rw [Sharpness.finite_probability_restrict G p (K n) (K.finite n),
      Sharpness.finite_probability_restrict G q (K n) (K.finite n)] at hh
    have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (K n)) = K n ∩ ω := by
      ext e
      simp
    simpa only [F,he] using hh
  have htp := BernoulliProduct.tendsto_real_finiteWitness p A hA hw K
  have htq := BernoulliProduct.tendsto_real_finiteWitness q A hA hw K
  simp only [BernoulliProduct.law_const] at htp htq
  exact le_of_tendsto_of_tendsto htp htq (Eventually.of_forall hfinite)

lemma sdiff_bound_of_subcritical (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : BernoulliProduct.HasFiniteOpenWitness A)
    (hwB : BernoulliProduct.HasFiniteOpenWitness B)
    (p : unitInterval) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q : unitInterval, (p:ℝ)/2 ≤ q → q < p → (G.law q).real (A\B) ≤ C/(q:ℝ)) :
    (G.law p).real (A\B) ≤ 2*C/(p:ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hAp : (G.law p).real A - ε < (G.law p).real A := by linarith
  obtain ⟨q,hhalf,hqp,hqA⟩ := BernoulliProduct.exists_lower_parameter
    (I := Unit) (fun _ => A) (fun _ => hA) (fun _ => hwA) p hp
    (fun _ => (G.law p).real A - ε)
    (fun _ => by simpa only [BernoulliProduct.law_const,law] using hAp)
  have hq : (G.law p).real A - ε < (G.law q).real A := by
    simpa only [BernoulliProduct.law_const,law] using hqA ()
  have hABm : IsUpperSet (A∩B) := fun _ _ h hh => ⟨hA h hh.1,hB h hh.2⟩
  have hABw := hwA.inter hwB hA hB
  have hAB := G.real_finiteWitness_mono_parameter (A∩B) hABm hABw hqp.le
  have hmeas := BernoulliProduct.measurableSet_finiteWitness B hB hwB
  have hsumP := measureReal_sdiff_add_inter (μ := G.law p) (s := A) hmeas
  have hsumQ := measureReal_sdiff_add_inter (μ := G.law q) (s := A) hmeas
  have hp' : (0:ℝ) < p := hp
  have hq' : (0:ℝ) < q := lt_of_lt_of_le (by linarith : (0:ℝ)<(p:ℝ)/2) hhalf
  have hinv : C/(q:ℝ) ≤ 2*C/(p:ℝ) := by
    apply (div_le_div_iff₀ hq' hp').mpr
    nlinarith
  linarith [hb q hhalf hqp]

lemma twoCluster_bound_of_subcritical (u v : V) (s : ℕ)
    (p : unitInterval) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q : unitInterval, (p:ℝ)/2 ≤ q → q < p →
      (G.law q).real (G.twoClusterEvent u v s) ≤ C/(q:ℝ)) :
    (G.law p).real (G.twoClusterEvent u v s) ≤ 2*C/(p:ℝ) := by
  rw [G.twoClusterEvent_sdiff] at hb ⊢
  exact G.sdiff_bound_of_subcritical (G.clusterTail u s ∩ G.clusterTail v s) (G.hitEvent u {v})
    (fun _ _ h hh => ⟨G.clusterTail_isUpperSet u s h hh.1,G.clusterTail_isUpperSet v s h hh.2⟩)
    (G.hitEvent_isUpperSet u {v})
    ((G.clusterTail_hasFiniteOpenWitness u s).inter (G.clusterTail_hasFiniteOpenWitness v s)
      (G.clusterTail_isUpperSet u s) (G.clusterTail_isUpperSet v s))
    (G.hitEvent_hasFiniteOpenWitness u {v}) p hp C hC hb

end CriticalPercolation.BondGraph
end
end

end OAI
