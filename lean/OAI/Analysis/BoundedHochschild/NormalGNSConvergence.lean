import OAI.Analysis.BoundedHochschild.NormalGNSWeakTopology

namespace OAI

/-! On bounded nets the given predual topology agrees with weak operator
convergence in the faithful normal representation. -/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normalGNS_predual_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type*} {l : Filter I} {a : I → M} {b : M} (h : PredualTendsto e a l b)
    (ξ η : NormalGNS e) :
    Tendsto (fun i => inner ℂ η (normalGNSRepresentation e (a i) ξ)) l
      (𝓝 (inner ℂ η (normalGNSRepresentation e b ξ))) := by
  obtain ⟨x, hx⟩ := (mem_normalDual e _).mp (normalGNSRepresentation_coefficients e η ξ)
  change Tendsto (fun i => coefficient (normalGNSRepresentation e) η ξ (a i)) l
    (𝓝 (coefficient (normalGNSRepresentation e) η ξ b))
  simpa only [hx] using (h x).star

lemma predual_tendsto_of_normalGNS (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type*} {l : Filter I} {a : I → M} {b : M} {C : ℝ}
    (hbdd : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (h : ∀ ξ η : NormalGNS e,
      Tendsto (fun i => inner ℂ η (normalGNSRepresentation e (a i) ξ)) l
        (𝓝 (inner ℂ η (normalGNSRepresentation e b ξ)))) :
    PredualTendsto e a l b := by
  let f (i : I) : WeakDual ℂ X := StrongDual.toWeakDual (e.symm (a i))
  let g : WeakDual ℂ X := StrongDual.toWeakDual (e.symm b)
  let B : Set (WeakDual ℂ X) := {F | ‖WeakDual.toStrongDual F‖ ≤ C}
  have hB : IsCompact B := by
    have heq : B = WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) C := by
      ext F
      simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    exact WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C
  have hf : ∀ᶠ i in l, f i ∈ B := by
    filter_upwards [hbdd] with i hi
    change ‖e.symm (a i)‖ ≤ C
    simpa only [e.symm.norm_map] using hi
  have he (i : I) : normalGNSWeak e (f i) =
      ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (a i)) := by
    change ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (e (e.symm (a i)))) = _
    rw [e.apply_symm_apply]
  have heg : normalGNSWeak e g = ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e b) := by
    change ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (e (e.symm b))) = _
    rw [e.apply_symm_apply]
  have ht : Tendsto (normalGNSWeak e ∘ f) l (𝓝 (normalGNSWeak e g)) := by
    simp only [Function.comp_def, he, heg]
    exact ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr h
  have hfg : Tendsto f l (𝓝 g) := by
    apply hB.tendsto_nhds_of_unique_mapClusterPt hf
    intro F _ hF
    apply normalGNSWeak_injective e
    have hc := hF.continuousAt_comp (normalGNSWeak_continuous e).continuousAt
    have hc' : (𝓝 (normalGNSWeak e F) ⊓ map (normalGNSWeak e ∘ f) l).NeBot := hc
    exact eq_of_nhds_neBot (hc'.mono (inf_le_inf_left _ ht))
  intro x
  exact (WeakDual.eval_continuous x).continuousAt.tendsto.comp hfg

end BoundedHochschild.KadisonRingrose

end

end OAI
