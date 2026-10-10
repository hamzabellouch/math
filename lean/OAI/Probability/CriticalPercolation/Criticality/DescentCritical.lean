import Mathlib
import OAI.Probability.CriticalPercolation.Classification.StructuredCoordinates
import OAI.Probability.CriticalPercolation.Classification.RestrictedQuotient
import OAI.Probability.CriticalPercolation.Classification.AlgebraicDescent
import OAI.Probability.CriticalPercolation.Criticality.IntegerBoxes

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

universe groupUniverse vertexUniverse edgeUniverse actionUniverse

theorem critical_null_of_algebraic_descent {N : Type groupUniverse} [Group N]
    (hN : AlgebraicDescent N) :
    ∀ {V : Type vertexUniverse} {E : Type edgeUniverse} {Λ : Type actionUniverse}
      [Group Λ] [MulAction Λ V] [MulAction Λ E]
      (G : BondGraph V E),
      G.fullGraph.Connected → G.LocallyFinite → G.SubexponentialGrowth →
      G.PreservesEnds (Λ := Λ) →
      ∀ (S : Set V), S.Finite → (∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) →
      ∀ (ρ : Λ →* N), Surjective ρ →
      (∀ v : V, (MulAction.orbit ρ.ker v).Finite) →
      (∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) →
      G.criticalProbability<1 → G.law G.criticalProbability G.percolates=0 := by
  induction hN with
  | @finite N _ _ =>
    intro V E Λ _ _ _ G _ _ _ _ S hS hcover ρ _ hker _ _
    have hV := EquivariantCoordinates.finite_vertices_of_finite_quotient ρ hker S hS hcover
    have hempty : G.percolates=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨v,hv⟩
      exact hv (hV.subset (Set.subset_univ _))
    rw [hempty,measure_empty]
  | @cyclic N _ φ hφ hf =>
    intro V E Λ _ _ _ G _ hl _ ha S hS hcover ρ hρ hker hstab hpc
    have heq := G.finite_by_integer_critical_one hl ha S hS hcover ρ hρ φ hφ hf hker hstab
    exact False.elim ((ne_of_lt hpc) heq)
  | @plane N _ φ hφ lower ih =>
    intro V E Λ _ _ _ G hc hl hg ha S hS hcover ρ hρ hker hstab hpc
    let _ := hc.nonempty
    let _ := G.countable_vertices hc hl
    let _ := G.countable_bonds hc hl
    obtain ⟨z,hzonto,hz⟩ := exists_integer_pair_coordinates ρ hρ φ hφ hstab
    apply G.critical_null_of_action_coordinates hc hl ha S hS hcover hg hpc
      (fun g => (φ (ρ g)).toAdd) z hzonto hz
    by_contra hbad
    obtain ⟨k,o,ho,hcrit,hpos⟩ := G.bounded_ray_critical_component
      (fun v => ((z v).1 : ℝ)) (fun v => ((z v).2 : ℝ)) (by simpa only [Int.cast_abs] using hbad)
    let zM : V → Multiplicative (ℤ×ℤ) := fun v => Multiplicative.ofAdd (z v)
    let Q := integerPairBox k
    let C := G.domainComponent (zM ⁻¹' Q) o
    let L := componentKernel (φ.comp ρ) C
    let H := G.induce C
    let _ := restrictedVertexAction C L (componentKernel_le (φ.comp ρ) C)
    let _ := G.restrictedEdgeAction ha C L (componentKernel_le (φ.comp ρ) C)
    have hzm : ∀ g v, zM (g • v)=(φ.comp ρ) g*zM v :=
      fun g v => congrArg Multiplicative.ofAdd (hz g v)
    obtain ⟨R,hR,hRcover⟩ := G.componentKernel_finite_orbits ha S hS hcover
      (φ.comp ρ) zM hzm Q (integerPairBox_finite k) o ho
    let f := ρ.comp L.subtype
    have hfker : ∀ v : C, (MulAction.orbit f.rangeRestrict.ker v).Finite :=
      rangeRestrict_kernel_orbits f
        (restricted_kernel_orbits ρ hker C L (componentKernel_le (φ.comp ρ) C))
    have hfstab : ∀ v : C,
        ((MulAction.stabilizer L v).map f.rangeRestrict : Set f.range).Finite :=
      rangeRestrict_stabilizer_images f
        (restricted_stabilizer_images ρ hstab C L (componentKernel_le (φ.comp ρ) C))
    have hle : f.range≤φ.ker := component_quotient_le_kernel ρ φ C
    have hnull := ih f.range hle H
      (G.domainComponent_connected (zM ⁻¹' Q) o) (G.induce_locallyFinite hl C)
      (G.induce_subexponential hl hg C)
      (G.restricted_preservesEnds ha C L (componentKernel_le (φ.comp ρ) C))
      R hR hRcover f.rangeRestrict f.rangeRestrict_surjective hfker hfstab
      (by change H.criticalProbability=G.criticalProbability at hcrit
          rw [hcrit]; exact hpc)
    exact (ne_of_gt hpos) hnull

end CriticalPercolation.BondGraph
end
end
end

end OAI
