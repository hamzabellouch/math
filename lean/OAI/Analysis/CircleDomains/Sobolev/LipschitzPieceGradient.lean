import OAI.Analysis.CircleDomains.Probability.LocalPartialMeasurability
import OAI.Analysis.CircleDomains.Sobolev.PhysicalLineDifferentiation
import OAI.Analysis.CircleDomains.Sobolev.LineDerivativeLocality
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! A Lipschitz extension agreeing on a measurable piece has the original
Sobolev weak gradient there, almost everywhere. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_piece_partial_eq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set EuclideanPlane} (hS : MeasurableSet S)
    {g : EuclideanPlane → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (heq : EqOn u g S) (i : Fin 2) :
    (fun p => fderiv ℝ g p (EuclideanSpace.single i 1)) =ᵐ[volume.restrict S]
      fun p => V p i := by
  have hVm := local_partial_aestronglyMeasurable hLp i
  let G : EuclideanPlane → ℝ := hVm.mk (fun p => V p i)
  have hG : Measurable G := hVm.stronglyMeasurable_mk.measurable
  have hVG : (fun p => V p i) =ᵐ[volume] G := hVm.ae_eq_mk
  have hP : MeasurableSet {p | p ∈ Sᶜ ∨ fderiv ℝ g p (EuclideanSpace.single i 1) = G p} :=
    hS.compl.union (measurableSet_eq_fun (measurable_fderiv_apply_const ℝ g (EuclideanSpace.single i 1)) hG)
  have hglobal : ∀ᵐ p ∂volume,
      p ∈ Sᶜ ∨ fderiv ℝ g p (EuclideanSpace.single i 1) = G p := by
    apply ae_of_ae_ae_physicalCoordinateLine hP i
    filter_upwards [locally_sobolev_coordinate_ae_hasDerivAt hu hw hLp i,
      ae_ae_physicalCoordinateLine (hg.ae_differentiableAt (μ := volume)) i,
      ae_ae_physicalCoordinateLine hVG i] with y hy hgy hVy
    have hline : EqOn (fun t => u (physicalCoordinateLine i y t))
        (fun t => g (physicalCoordinateLine i y t))
        {t | physicalCoordinateLine i y t ∈ S} := fun t ht => heq ht
    filter_upwards [hy, hgy, hVy, ae_derivative_eq_of_eqOn hline] with t ht hgt hVt hloc
    by_cases hmem : physicalCoordinateLine i y t ∈ S
    · right
      exact (hloc hmem _ _ ht (hasDerivAt_physicalCoordinate_comp hgt)).symm.trans hVt
    · exact Or.inl hmem
  change ∀ᵐ p ∂volume.restrict S, fderiv ℝ g p (EuclideanSpace.single i 1) = V p i
  rw [ae_restrict_iff' hS]
  filter_upwards [hglobal, hVG] with p hp hVp hpS
  exact (hp.resolve_left (not_not_intro hpS)).trans hVp.symm

lemma lipschitz_piece_gradient_eq {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {S : Set EuclideanPlane} (hS : MeasurableSet S)
    {g : EuclideanPlane → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) (heq : EqOn u g S) :
    ∀ᵐ p ∂volume.restrict S, ∀ i : Fin 2,
      fderiv ℝ g p (EuclideanSpace.single i 1) = V p i :=
  ae_all_iff.mpr (fun i => lipschitz_piece_partial_eq hu hw hLp hS hg heq i)

end CircleDomainRigidity

end

end OAI
