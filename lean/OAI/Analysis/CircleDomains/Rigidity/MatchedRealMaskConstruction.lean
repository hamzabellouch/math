import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskData

namespace OAI

/-! Construction of every mask system, including its actual L² paying
density, continuous compact scalar, and connected residual-dust domain. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.exists_real_mask (E : D.MatchedRoundDisks)
    (hmax : PlanarMaximalL2) (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hG' : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {φ : Sphere → ℝ} (hφ : Continuous φ) {L : ℝ≥0}
    (hL : LipschitzWith L (fun z : ℂ => φ (z : Sphere)))
    (hφzero : ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), φ p = 0) (m : ℕ) :
    Nonempty (MatchedRealMask E hG.1 hf φ L m) := by
  let I := E.traceInterval hG.1 hf φ L
  let a := fun n => volume.real (I n)
  obtain ⟨cut,P,hs,hu,hz,ho,hPm,hP0,hP2,hpay⟩ := exists_trace_balloon_real_system hmax
    E.traceCenter E.traceRadius a (traceEnumeration_nonneg E.source_nonneg)
    (fun _ => measureReal_nonneg)
    (traceEnumeration_ball_disjoint (fun i j h => (E.source_disjoint h).mono
      ball_subset_closedBall ball_subset_closedBall) 0)
    (traceEnumeration_summable_sq E.source_summable) (E.traceInterval_summable_sq hG.1 hf φ L) m
  let ccut := fun n z => cut n (Complex.equivRealProdCLM z)
  have hcu (n : ℕ) (z : ℂ) : ccut n z ∈ Icc (0:ℝ) 1 := hu n _
  have hcc (n : ℕ) : Continuous (ccut n) := (hs n).continuous.comp Complex.equivRealProdCLM.continuous
  have hcz (n : ℕ) (z : ℂ) (h : ‖z-E.traceCenter n‖ ≤
      traceBalloonInnerRatio m*traceBalloonRadius E.traceRadius m n) : ccut n z = 0 := by
    apply hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  have hco (n : ℕ) (z : ℂ) (h : traceBalloonRadius E.traceRadius m n ≤ ‖z-E.traceCenter n‖) : ccut n z = 1 := by
    apply ho
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  obtain ⟨W,hW,hWK,hWz,hO,hOc,hOd,hOr⟩ := E.exists_mask_domain hG hinf hf hG' hinf' hrem
    hφ hL m hcu hcc hcz hco
  let U := fun z => infiniteTracePrimitive ccut I 0 z (φ (D.selectedTarget hG.1 hf (z : Sphere)))
  have hUc : Continuous U := E.mask_continuous hG hinf hf hG' hinf' hφ hL m hcu hcc hcz hco 0
  have hUs : HasCompactSupport U := D.mask_compactSupport hG.1 hinf hf hfix hφzero ccut I
  have hEq : D.realMaskValue E hG.1 hf φ L cut = U ∘ Complex.equivRealProdCLM.symm := by
    funext p
    simp only [realMaskValue,realSelectedScalar,U,ccut,I,comp_apply,
      infiniteTracePrimitive_comp,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨⟨cut,hs,hu,hz,ho,P,hPm,hP0,hP2,hpay,W,hW,hWK,?_,?_,?_,hO,hOc,hOd,hOr⟩⟩
  · exact hWz
  · rw [hEq]
    exact hUc.comp Complex.equivRealProdCLM.symm.continuous
  · rw [hEq]
    exact hUs.comp_homeomorph Complex.equivRealProdCLM.symm.toHomeomorph

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
