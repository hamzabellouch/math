import Mathlib
import OAI.Analysis.Conductivity.Geometry.CentralSlopeJet
import OAI.Analysis.Conductivity.Variational.CentralLocalAgreement

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralBallSet : Set R3 := WithLp.ofLp ⁻¹' centralPhysical

lemma centralBallSet_measurable : MeasurableSet centralBallSet :=
  centralPhysical_compact.measurableSet.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.measurable

lemma centralNeighborhoodRawCLM_smooth_restrict (f : centralSmoothFunctions) :
    lpRestrictionCLM centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f))=
      lpRestrictionCLM centralBallSet (centralFullJetCLM s (centralEmbedL s f)) := by
  apply Lp.ext
  filter_upwards [lpRestrictionCLM_ae centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f)),
    lpRestrictionCLM_ae centralBallSet (centralFullJetCLM s (centralEmbedL s f)),
    ae_restrict_of_ae (centralNeighborhoodRawCLM_smooth_ae s hs ha₀ ha f),
    ae_restrict_of_ae (centralFullJetCLM_smooth_ae s f),
    ae_restrict_mem centralBallSet_measurable] with x h₁ h₂ hn hc hx
  exact h₁.trans ((hn hx).trans ((hc hx).symm.trans h₂.symm))

theorem centralNeighborhoodCompletion_restrict (u : centralEnergySpace s) :
    lpRestrictionCLM centralBallSet (centralNeighborhoodCompletion s hs ha₀ ha u).val=
      lpRestrictionCLM centralBallSet (centralFullJetCLM s u.val) := by
  let L := (lpRestrictionCLM centralBallSet).comp (centralNeighborhoodRawCLM s hs ha₀ ha)-
    (lpRestrictionCLM centralBallSet).comp (centralFullJetCLM s)
  have hr : LinearMap.range (centralEmbedL s)≤LinearMap.ker L.toLinearMap := by
    rintro _ ⟨f,rfl⟩
    change lpRestrictionCLM centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f))-
      lpRestrictionCLM centralBallSet (centralFullJetCLM s (centralEmbedL s f))=0
    exact sub_eq_zero.mpr (centralNeighborhoodRawCLM_smooth_restrict s hs ha₀ ha f)
  have hu := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker u.property
  rw [centralNeighborhoodCompletion_val]
  exact sub_eq_zero.mp hu

lemma centralNeighborhoodCompletion_central_ae (u : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (centralNeighborhoodCompletion s hs ha₀ ha u).val x=centralFullJetCLM s u.val x := by
  have he := centralNeighborhoodCompletion_restrict s hs ha₀ ha u
  apply (ae_restrict_iff' centralBallSet_measurable).mp
  filter_upwards [lpRestrictionCLM_ae centralBallSet (centralNeighborhoodCompletion s hs ha₀ ha u).val,
    lpRestrictionCLM_ae centralBallSet (centralFullJetCLM s u.val)] with x h₁ h₂
  rw [←h₁,he,h₂]

end

open Set MeasureTheory Filter Topology

lemma H1_add_jet_ae (u v : H1) :
    (u+v).val=ᵐ[ballMeasure] (fun x => u.val x+v.val x) := by
  exact Lp.coeFn_add u.val v.val

lemma central_neighborhood_with_slopes (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a slopes : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      (w.val=ᵐ[ballMeasure] (fun x =>
        (centralNeighborhoodCompletion s hs ha₀ ha p).val x+
          centralSlopeJet a slopes (WithLp.ofLp x))) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
        w.val x=centralFullJetCLM s p.val x) := by
  obtain ⟨v,hv,hve,hvz⟩ := centralSlopeExtension_exists a slopes ha₀ ha
  let z : H1 := centralNeighborhoodCompletion s hs ha₀ ha p
  have hsum := H1_add_jet_ae z v
  have hz : z∈H10 := centralNeighborhoodCompletion_mem_H10 s hs ha₀ ha p
  refine ⟨z+v,H10.add_mem hz hv,?_,?_⟩
  · filter_upwards [hsum,hve] with x hadd he
    exact hadd.trans (congrArg (fun b : JetFiber => z.val x+b) he)
  · have hcentral := centralNeighborhoodCompletion_central_ae s hs ha₀ ha p
    filter_upwards [hsum,hvz,hcentral] with x hadd hvzero hc
    intro hx
    exact hadd.trans ((congrArg (fun b : JetFiber => z.val x+b) (hvzero hx)).trans
      ((add_zero _).trans (hc hx)))

theorem central_variational_neighborhood_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a slopes : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (hslopes : ∑ i,slopes i=0) :
    ∃ p : centralEnergySpace s,∃ w : H1,w∈H10 ∧ centralM s p=0 ∧
      (w.val=ᵐ[ballMeasure] (fun x =>
        (centralNeighborhoodCompletion s hs ha₀ ha p).val x+
          centralSlopeJet a slopes (WithLp.ofLp x))) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
        w.val x=centralFullJetCLM s p.val x) ∧
      (∀ v : centralEnergySpace s,
        inner ℝ (centralD s p) (centralD s v)+
          angularArea*(∑ i : Fin 3,inner ℝ
            (spectralGraphWeight (torusRate s) (centralT s i p))
            (spectralGraphWeight (torusRate s) (centralT s i v)))=
          angularArea*(∑ i : Fin 3,slopes i*
            spectralGraphMean (torusRate s) (centralT s i v))) := by
  obtain ⟨p,hp,hvar,_⟩ := central_unnormalized_variational_exists s slopes hslopes
  obtain ⟨w,hw,he,hc⟩ := central_neighborhood_with_slopes s hs a slopes ha₀ ha p
  exact ⟨p,w,hw,hp,he,hc,hvar⟩

end ScalarConductivity

end

end OAI
