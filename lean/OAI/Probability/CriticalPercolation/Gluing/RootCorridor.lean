import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.ProductMeasure.FreshRegionLaw
import OAI.Probability.CriticalPercolation.Gluing.RelayScales
import OAI.Probability.CriticalPercolation.ProductMeasure.RelayProbability
import OAI.Probability.CriticalPercolation.Gluing.SourceConnectivity
import OAI.Probability.CriticalPercolation.Gluing.FreshCollarExact
import OAI.Probability.CriticalPercolation.Gluing.SourceRelaySeparation

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (q : (E⊕G.vertexBall o m) → unitInterval)
    (hwire : ∀ a : G.vertexBall o m, q (Sum.inr a)=1)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
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
      ((G.withSource (G.vertexBall o m)).hitEvent none
        (some '' relayMark t z (L+1/2) σ ρ))ᶜ ≤ η+L*κ := by
  let A := G.vertexBall o m
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L (i+1))
  have h0 := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
    hσ he hρ hJ hL heL hr ht hz p' η hmove 0 (Nat.zero_le L)
  have ho : o∈G.vertexCollar (corridorRelay t z σ e ρ L 0) R := by
    apply Set.mem_iUnion₂.mpr
    refine ⟨o,?_,G.mem_vertexBall_self o R⟩
    simp only [corridorRelay]
    exact ⟨by simp [hto],by simp [hto,hρ],by simp [hzo]⟩
  have hh0 : 1-η ≤ (BernoulliProduct.law q).real (H 0) := by
    rw [measureReal_def,G.source_hit_probability A _ q hwire]
    exact (h0.2 o ho).trans (BernoulliProduct.fresh_region_lower (fun b => q (Sum.inl b))
      (fun _ => p') (G.inducedEdges (relayDomain t z J (L+1/2) σ)) hq _
      (G.measurableSet_seedHitEvent _ _) (G.seedHitEvent_upper _ _))
  have hfirst : (BernoulliProduct.law q).real (H 0)ᶜ ≤ η := by
    rw [probReal_compl_eq_one_sub ((G.withSource A).measurableSet_hitEvent _ _)]
    linarith
  have hh := relay_miss_bound (BernoulliProduct.law q) H κ η L hfirst (by
    intro i hi
    have hiL : i+1 ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove (i+1) hiL
    apply G.fresh_collar_transfer hc hl A _ _ (G.vertexBall_finite hl o m) q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ 0 L R m (i+1) he hρ hiL
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz ?_)
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean
    have hb := (abs_le.mp (G.coordinate_ball_bound t ρ hρ ht ha)).2
    simpa [hto] using hb)
  simpa only [H,corridorRelay,Nat.add_one_ne_zero,ite_false,
    ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
