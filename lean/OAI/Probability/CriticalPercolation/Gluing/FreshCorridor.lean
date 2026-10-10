import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Gluing.RelayScales
import OAI.Probability.CriticalPercolation.Gluing.SourceRelaySeparation
import OAI.Probability.CriticalPercolation.ProductMeasure.RelayProbability
import OAI.Probability.CriticalPercolation.Gluing.FreshCollarExact

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource A).hitEvent none (some '' relayMark t z 0 σ ρ)\
        (G.withSource A).hitEvent none (some '' relayMark t z (L+1/2) σ ρ)) ≤ (L+1)*κ := by
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L i)
  have hh := relay_failure_bound (BernoulliProduct.law q) H κ (L+1) (by
    intro i hi
    have hiL : i ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove i hiL
    apply G.fresh_collar_transfer hc hl A _ _ hA q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ P L R m i he hρ hiL
        (by linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz (hsource a ha))
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean)
  simpa [H,corridorRelay,show ¬L+1 ≤ L by omega] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
