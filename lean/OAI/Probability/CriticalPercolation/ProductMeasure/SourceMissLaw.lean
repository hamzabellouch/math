import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.Gluing.RootCorridor
import OAI.Probability.CriticalPercolation.Gluing.SourceConnectivity

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma source_miss_real (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' T))ᶜ=
      (BernoulliProduct.law (fun b => q (Sum.inl b))).real (G.seedHitEvent A T)ᶜ := by
  rw [probReal_compl_eq_one_sub ((G.withSource A).measurableSet_hitEvent _ _),
    probReal_compl_eq_one_sub (G.measurableSet_seedHitEvent A T),
    measureReal_def,measureReal_def,G.source_hit_probability A T q hq]

lemma restricted_seed_probability (A T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _) (G.measurableSet_seedHitEvent A T)]
  congr 1
  ext ω
  have he : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  simp only [Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]

lemma restricted_seed_miss_real (A T : Set V) (q : E → unitInterval) (R : Set E) :
    (BernoulliProduct.law q).real (G.restrictedSeed A T R)ᶜ=
      (BernoulliProduct.law (Sum.elim (pinnedParameters q Rᶜ ∅) (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' T))ᶜ := by
  rw [G.source_miss_real _ _ _ (fun _ => rfl),
    probReal_compl_eq_one_sub (G.restrictedSeed_measurable A T R),
    probReal_compl_eq_one_sub (G.measurableSet_seedHitEvent A T),
    measureReal_def,measureReal_def,G.restricted_seed_probability]
  rfl

theorem original_root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ) (U : Set E)
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law (fun _ : E => p')).real
      (G.restrictedSeed (G.vertexBall o m) (relayMark t z (L+1/2) σ ρ) U)ᶜ ≤ η+L*κ := by
  rw [G.restricted_seed_miss_real]
  apply G.root_corridor_miss hc hl o t z σ e ρ J L R m _ (fun _ => rfl)
    hσ he hρ hJ hL heL hr hto hzo ht hz hcR pc p' hpc₀ hpc hpp hppc _
    D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove
  intro b hb
  simp only [Sum.elim_inl,pinnedParameters,Set.mem_compl_iff,ite_eq_right (not_not_intro (hDU hb))]

end CriticalPercolation.BondGraph
end
end
end

end OAI
