import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.ContinuousProbability

namespace OAI

section
section CurrentModule6
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*}

lemma probability_eq_real [Fintype E] (p : unitInterval) (F : Set E → Prop) :
    probability (p : ℝ) F = (BernoulliProduct.law (fun _ : E => p)).real {ω | F ω} := by
  rw [← integral_indicator_one (μ := BernoulliProduct.law (fun _ : E => p))
    (s := {ω | F ω}) (.of_discrete), BernoulliProduct.integral_law_eq_expect]
  rfl

variable (G : BondGraph V E)

lemma finite_probability_restrict (p : unitInterval) (K : Set E) (hK : K.Finite)
    (F : Set K → Prop) :
    letI := hK.fintype
    probability (p : ℝ) F = (G.law p).real {ω | F (Subtype.val ⁻¹' ω)} := by
  let := hK.fintype
  rw [probability_eq_real, ← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [measureReal_def, Measure.map_apply hmeas (.of_discrete)]
  rw [BernoulliProduct.law_const]
  rfl

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  ext e
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma incident_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v,hv,he⟩
  exact ⟨v,h hv,he⟩

lemma delete_restrict_incident {S : Set V} {K : Set E} (hK : G.incidentEdges S ⊆ K)
    (ω : Set E) : delete (G.openGraph (K ∩ ω)) Sᶜ = delete (G.openGraph ω) Sᶜ := by
  ext x y
  constructor
  · exact fun h => ⟨G.openGraph_mono inter_subset_right h.1,h.2⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hx,hy⟩
    refine ⟨⟨⟨e,⟨hK ?_,he⟩,hend⟩,hne⟩,hx,hy⟩
    exact ⟨x,not_not.mp hx,by rw [hend]; simp⟩

def phi (p : unitInterval) (o : V) (S : Set V) : ℝ :=
  (p : ℝ) * ∑' e, (G.law p).real
    {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}

lemma boundaryReach_incident {S : Set V} {H : SimpleGraph V} {o : V} {e : E}
    (h : boundaryReach G Sᶜ H o e) : e ∈ G.incidentEdges S := by
  obtain ⟨x,y,he,hx,_hy,_hox⟩ := h
  exact ⟨x,not_not.mp hx,by rw [he]; simp⟩

lemma boundary_measure_support (p : unitInterval) (o : V) (S : Set V) :
    Function.support (fun e => (G.law p).real
      {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}) ⊆ G.incidentEdges S := by
  intro e he
  by_contra hn
  apply he
  have hh : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = ∅ := by
    ext ω
    exact iff_false_intro (fun h => hn (boundaryReach_incident G h))
  change (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = 0
  rw [hh,measureReal_empty]

lemma phi_eq_boundaryFlux (p : unitInterval) (o : V) (S : Set V)
    (K : Set E) (hK : K.Finite) (hSK : G.incidentEdges S ⊆ K) :
    letI := hK.fintype
    phi G p o S = boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ := by
  let := hK.fintype
  rw [phi, ← tsum_subtype_eq_of_support_subset ((boundary_measure_support G p o S).trans hSK),
    tsum_fintype, boundaryFlux_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [finite_probability_restrict G p K hK]
  congr 1
  ext ω
  change boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e.val ↔
    boundaryReach (G.restrictEdges K) Sᶜ
      (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e
  rw [G.restrictEdges_openGraph, delete_restrict_incident G hSK]
  rfl

lemma restricted_escape_le (p : unitInterval) (o : V) (T : Set V)
    (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    probability (p : ℝ) (reachesTarget (G.restrictEdges K) o T) ≤
      (G.law p).real (G.hitEvent o T) := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change reachesTarget (G.restrictEdges K) o T (Subtype.val ⁻¹' ω) at hω
  apply (reachesTarget_iff_hitEvent G o T ω).mp
  apply reachesTarget_mono G o T inter_subset_right
  change o ∈ roots (G.openGraph (K ∩ ω)) T
  simpa only [reachesTarget, G.restrictEdges_openGraph] using hω

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
