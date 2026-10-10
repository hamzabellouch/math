import Mathlib
import OAI.Analysis.CoulombRadii.Variational.AtomicMasterUniform
import OAI.Analysis.CoulombRadii.Packets.RetainedInverseOffset

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_retained_master_fresh_transfer {D c A ε : ℝ}
    (hD : 0≤D) (hc : 0<c) (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0<s₀ ∧ s₀≤1 ∧ ∀ {N J : ℕ} (Z : ℕ) (hZ : 1≤Z)
    {ψ : Wavefunction (N+1)} {g : Gradient (N+1)}, FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g≤energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal)≤Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g≤E+D → ∀ {r₀ s : ℝ}, 0<r₀ → 0<s → s<s₀ →
    ∀ (j : ℕ), r₀ * (2 : ℝ) ^ j ≤ s →
    ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
    (r₀*2^j)^42≤(observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
    ∀ (y : Position) (hy : y≠0), r₀≤‖y‖ → Coulomb.atomicCellScale y≤A*(r₀*2^j) →
    ∃ u : Coulomb.H1Vector (N+1), Coulomb.Antisymmetric u ∧ Coulomb.mass u=1 ∧
      Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) ∧
      (∀ F : Coulomb.Configuration (N+1) → ℝ, Coulomb.potentialForm F u=
        (stateWeightedIntegral ψ (arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B)))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood
          (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
          (retainedTailObservation j ⁻¹' B) x*F (flattenConfiguration (N+1) x))) ∧
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*Coulomb.atomicCellScale y) (6*Coulomb.atomicCellScale y),
    ∃ T : Coulomb.AtomicBudgetHistory (Coulomb.atom Z hZ) u
      (Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm (Coulomb.atom Z hZ)≤Coulomb.form (Coulomb.atom Z hZ) u+
        Coulomb.thinIMS u y t ((Coulomb.atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(Coulomb.atomicCellScale y)^(6/5:ℝ))) ∧
      Coulomb.atomicPatchTFGap (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
        ((Coulomb.atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2≤
        2*(Coulomb.atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((Coulomb.atomicCellScale y)^(6/5:ℝ))≤
        (72*Coulomb.atomicPatchCountFactor*Coulomb.atomicCountConstant)*
          (Coulomb.atomicCellScale y)^(-29/5:ℝ) ∧
      ∀ (g₀ : 𝓢(Position,ℝ)), (∫ w,g₀ w^2)=1 →
      (∀ w,g₀ w=g₀ (EuclideanSpace.single 0 ‖w‖)) → (∀ w,1<‖w‖ → g₀ w=0) →
      |((Z:ℝ)*coulombKernel y-
          potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g₀ c r₀ s) y)-
        Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (by intro i; rfl) T.ensemble y hy
          ((Coulomb.atomicCellScale y)^(6/5:ℝ))
          (Real.rpow_pos_of_pos (Coulomb.atomicCellScale_pos hy) _) t ht.2|≤
        ε*(Coulomb.atomicCellScale y)^(-4:ℝ) := by
  obtain ⟨s₁,hs₁,hs₁1,Hoff⟩ := exists_retainedInverseOffset_small hD hA
  obtain ⟨s₂,hs₂,Hpatch⟩ := exists_atomic_master_fresh_uniform_transfer hc hA hε
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,(min_le_left _ _).trans hs₁1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss j hrs B hB hprob y hy hry hya
  have hr : 0<r₀*2^j := by positivity
  have hrs₁ : r₀*2^j<s₁ := hrs.trans_lt (hss.trans_le (min_le_left _ _))
  have := rawLaw_isProbability hd.2.2.1 hn
  have hp1 : (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B)≤1 := measureReal_le_one
  have hpEq := physical_retainedTailEvent_probability hd.2.2.1 hn
    (fun k : Fin J => r₀*2^k.val) (fun k => by positivity) j hB
  have hp0 := (pow_pos hr 42).trans_le hprob
  obtain ⟨u,hu,hum,hue,hlaw⟩ := atomic_arrayEvent_state Z hZ hd hn hmin hbase
    (fun k : RetainedScales J j => (r₀*2^k.val.val)^(101/100:ℝ))
    (fun k => Real.rpow_pos_of_pos (by positivity) _)
    (hB.preimage (measurable_retainedTailObservation j))
    (fun p z => by simp only [mem_preimage,retainedTailObservation_permute])
    (hpEq ▸ hp0)
  have hδ := retainedInverseOffset_nonneg hD hr (hrs₁.le.trans hs₁1)
  have hue' : Coulomb.form (Coulomb.atom Z hZ) u≤E+retainedInverseOffset D (r₀*2^j) := by
    apply hue.trans
    apply add_le_add le_rfl
    apply retained_event_offset_le hr₀ J j
    · simpa only [←hpEq] using hprob
    · simpa only [←hpEq] using hp1
  refine ⟨u,hu,hum,hue',hlaw,?_⟩
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hG,hdel,hF⟩ := Hpatch (Coulomb.atom Z hZ)
    (by intro i; rfl) u hu hum hE hue' hδ hr₀ hs (hss.trans_le (min_le_right _ _)) y hy hry
    (hya.trans (mul_le_mul_of_nonneg_left hrs hA.le))
    (Hoff hr hrs₁ (Coulomb.atomicCellScale_pos hy) hya)
  refine ⟨t,ht,T,hT,ho,hcs,hos,hG,hdel,?_⟩
  intro g₀ hgm hrad hgs
  have H := hF g₀ hgm hrad hgs
  simpa only [Coulomb.attraction,Coulomb.atom,Fin.sum_univ_one,zero_sub,sub_zero,norm_neg,
    Coulomb.coulombKernel,coulombKernel] using H
end NeutralAtom
end

end

end OAI
