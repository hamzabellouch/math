import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning
import OAI.Probability.CriticalPercolation.ProductMeasure.SourceEventLaw
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.Gluing.FreshCorridor

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_pinned_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : E → unitInterval)
    (I F U ω : Set E) (hFU : F⊆U)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q b=p')
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hfresh : Disjoint I (G.inducedEdges (relayDomain t z J (L+1/2) σ)))
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.blockProbability q I
      (G.restrictedSeed A (relayMark t z 0 σ ρ) F\
        G.restrictedSeed A (relayMark t z (L+1/2) σ ρ) U) ω).toReal ≤ (L+1)*κ := by
  let r : E → unitInterval := pinnedParameters (pinnedParameters q I ω) Uᶜ ∅
  let q' : (E⊕A) → unitInterval := Sum.elim r (fun _ => 1)
  have hq' : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q' (Sum.inl b)=p' := by
    intro b hb
    have hbU := hDU hb
    have hbI : b∉I := fun hi => Set.disjoint_left.mp hfresh hi hb
    simpa [q',r,pinnedParameters,hbU,hbI] using hq b hb
  exact (G.restricted_seed_diff_le_source A _ _ q I F U ω hFU).trans
    (G.coordinate_corridor_failure hc hl A hA q' t z σ e ρ J P L R m
      hσ he hρ hJ hL heL hr hP hsource ht hz hcR pc p' hpc₀ hpc hpp hppc hq'
      D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove)

end CriticalPercolation.BondGraph
end
end
end

end OAI
