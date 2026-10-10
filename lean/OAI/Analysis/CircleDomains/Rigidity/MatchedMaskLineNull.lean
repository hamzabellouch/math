import OAI.Analysis.CircleDomains.Probability.CommonPointNullSet
import OAI.Analysis.CircleDomains.Rigidity.MaskedLineNullImage

namespace OAI

/-! The actual global Sobolev masks imply null scalar traces on the
common point set. Every parameter comes from the matched disks and the
constructed masks; finite-prefix inactivity is proved from their radii. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.commonPoint_trace_null_of_masks (E : D.MatchedRoundDisks)
    (hprincipal : PrincipalRealBeltrami)
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G))
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G)) (φ : Sphere → ℝ) (L : ℝ≥0)
    (M : ∀ m, MatchedRealMask E hG.1 hf φ L m)
    (W : ∀ m, DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG.1 hf φ L (M m).cutoff ∘ euclideanPlaneCoordinates) univ)
    (i : Fin 2) :
    ∀ᵐ y ∂volume, volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) ''
      {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
  let I := E.traceInterval hG.1 hf φ L
  let A := fun j => Ioo (transverseCoordinate i (E.traceCenter j)-traceBalloonRadius E.traceRadius 0 j)
    (transverseCoordinate i (E.traceCenter j)+traceBalloonRadius E.traceRadius 0 j)
  have hI (j : ℕ) : MeasurableSet (I j) := measurableSet_Ioo
  have hIf (j : ℕ) : volume (I j) ≠ ∞ := by
    dsimp only [I,MatchedRoundDisks.traceInterval]
    exact ne_of_lt measure_Ioo_lt_top
  have htail := ae_balloon_line_tails
    (fun j => (traceBalloonRadius_pos (r := E.traceRadius) 0 j).le)
    (fun j => transverseCoordinate i (E.traceCenter j)) hIf
    (E.traceInterval_summable_sq hG.1 hf φ L)
    (traceBalloonRadius_summable_sq (traceEnumeration_summable_sq E.source_summable) 0)
  have hq (m : ℕ) := sobolev_typical_line_payment
    ((M m).continuous.comp euclideanPlaneCoordinates.continuous)
    ((M m).compact.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph) (W m) i
  choose Q hQ hQ0 hQL hQpay using hq
  have hp (m : ℕ) := memLp_realCoordinateLine_ae
    (M m).density_measurable (M m).density_memLp i
  have hd (m : ℕ) := ae_ae_realCoordinateLine (M m).pays i
  filter_upwards [D.commonPointPlane_line_null hprincipal hG hinf hf hH hinf' hrem i,
    htail,ae_all_iff.mpr hQpay,ae_all_iff.mpr hp,ae_all_iff.mpr hd] with y hnull ht hqline hpline hdline
  let C := {x | complexCoordinateLine i y x ∈ D.commonPointPlane ∧ complexCoordinateLine i y x ≠ 0}
  have hC : volume C = 0 := measure_mono_null (fun _ hx => hx.1) hnull
  have htrace : volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) '' C) = 0 := by
    apply null_image_of_masked_line_payments hC _ hI hIf y ht
      (fun m j x => (M m).cutoff j (realCoordinateLine i y x))
      (fun m j => ((M m).smooth j).comp ((realCoordinateLine_contDiff i y).of_le (by simp)))
      (fun m j x => (M m).unit j _)
      (fun m t => (M m).density (realCoordinateLine i y t))
      (fun m t => Q m (physicalCoordinateLine i y t))
      (fun m => (hpline m).locallyIntegrable (by norm_num))
      (fun m => (hqline m).1)
      (fun m t => (M m).density_nonneg _) (fun m t => hQ0 m _)
    · intro m
      filter_upwards [hdline m] with t ht
      intro n
      apply le_trans _ (ht n)
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (realCoordinateLine_abs_deriv_le ((M m).smooth j) i y t) measureReal_nonneg
    · intro m x z
      convert (hqline m).2 x z using 1
      simp only [Function.comp_apply,realCoordinateLine_physical,realMaskValue,
        infiniteTracePrimitive_comp,I]
    · intro m j hy x
      apply (M m).outer
      apply (traceBalloonRadius_le_first m j).trans
      apply le_of_not_gt
      intro hlt
      apply hy
      have h := (complexCoordinateLine_transverse_le i y x (E.traceCenter j)).trans_lt hlt
      exact ⟨by linarith [(abs_lt.mp h).1],by linarith [(abs_lt.mp h).2]⟩
    · intro N x hx
      obtain ⟨m,V,hV,hxV,hpre⟩ := E.commonPoint_prefix_avoidance hx.1 hx.2 N
      refine ⟨m,(complexCoordinateLine i y) ⁻¹' V,?_,hxV,?_⟩
      · exact hV.preimage (Complex.equivRealProdCLM.symm.continuous.comp
          (realCoordinateLine_contDiff i y).continuous)
      · intro z hz j hj
        exact (M m).outer j _ (hpre _ hz j hj)
  have hextra : volume ((fun x => D.realSelectedScalar hG.1 hf φ (realCoordinateLine i y x)) ''
      {x | complexCoordinateLine i y x = 0}) = 0 := by
    apply measure_mono_null _ (measure_singleton (D.realSelectedScalar hG.1 hf φ (0,0)))
    rintro _ ⟨x,hx,rfl⟩
    apply mem_singleton_iff.mpr
    have he : realCoordinateLine i y x = (0,0) := by
      apply Complex.equivRealProdCLM.symm.injective
      exact hx
    exact congrArg (D.realSelectedScalar hG.1 hf φ) he
  apply measure_mono_null _ (measure_union_null htrace hextra)
  rintro _ ⟨x,hx,rfl⟩
  by_cases hz : complexCoordinateLine i y x = 0
  · exact Or.inr ⟨x,hz,rfl⟩
  · exact Or.inl ⟨x,⟨hx,hz⟩,rfl⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
