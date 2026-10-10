import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! A compactly supported planar Sobolev function whose weak gradient
vanishes is zero, by positive mollification. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Convolution
noncomputable section
namespace CircleDomainRigidity

theorem zero_of_compact_support_zero_weak_gradient
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u)
    (hg : ∀ i : Fin 2, (fun x => hw.weakGrad x i) =ᵐ[volume] 0) :
    u =ᵐ[volume] 0 := by
  have hu : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  have hzero (n : ℕ) : planarMollification u n = 0 := by
    have hd (x : EuclideanPlane) : fderiv ℝ (planarMollification u n) x = 0 := by
      have heq : (fderiv ℝ (planarMollification u n) x).toLinearMap = 0 := by
        apply (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ext
        intro i
        change (fderiv ℝ (planarMollification u n) x)
          ((EuclideanSpace.basisFun (Fin 2) ℝ) i) = 0
        rw [EuclideanSpace.basisFun_apply, planarMollification_derivative hw]
        have he := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
          (EventuallyEq.refl (ae volume) ((DeGiorgi.shrinkingBump (d := 2) n).normed volume)) (hg i)
        rw [he, convolution_zero]
        rfl
      ext y
      exact LinearMap.congr_fun heq y
    have hc := planarMollification_hasCompactSupport hs n
    obtain ⟨y, hy⟩ : ∃ y, y ∉ tsupport (planarMollification u n) :=
      (Set.ne_univ_iff_exists_notMem _).mp hc.isCompact.ne_univ
    funext x
    exact (is_const_of_fderiv_eq_zero
      ((planarMollification_smooth (hu.locallyIntegrable (by norm_num)) n).differentiable
        (by simp)) hd x y).trans (image_eq_zero_of_notMem_tsupport hy)
  have ht := planarMollification_tendsto_L2 hu
  simp only [hzero, Pi.zero_apply, zero_sub] at ht
  change Tendsto (fun _ : ℕ => eLpNorm (-u) 2 volume) atTop (𝓝 0) at ht
  rw [eLpNorm_neg] at ht
  exact (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp
    (tendsto_nhds_unique tendsto_const_nhds ht)

end CircleDomainRigidity

end

end OAI
