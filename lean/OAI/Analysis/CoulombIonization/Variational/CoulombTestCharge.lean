import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SmoothNewton

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

lemma tfLaplacian_support {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Function.support (Δ g) ⊆ tsupport g := by
  intro x hx
  by_contra hn
  apply hx
  rw [tfLaplacian_eq hg]
  apply Finset.sum_eq_zero
  intro i _
  apply Function.notMem_support.mp
  intro hi
  apply hn
  exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
    ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)) (subset_tsupport _ hi))

theorem tfPotential_laplacian {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (z : TFSpace) :
    tfPotential (Δ g) z = -(4*Real.pi*g z) := by
  have hgc : HasCompactSupport (fun x => g (z+x)) :=
    hcg.comp_homeomorph (Homeomorph.addLeft z)
  have hh := compact_laplacian_newton_zero (hg.comp (contDiff_const.add contDiff_id)) hgc
  simp only [Function.comp_def,id_eq] at hh
  rw [tfLaplacian_translate] at hh
  simp only [add_zero] at hh
  have hi := integral_add_left_eq_self (μ := volume) (fun x => Δ g x/‖z-x‖) z
  calc
    tfPotential (Δ g) z = ∫ x, Δ g (z+x)/‖z-(z+x)‖ := hi.symm
    _ = ∫ x, Δ g (z+x)/‖x‖ := by simp only [sub_add_cancel_left,norm_neg]
    _ = _ := hh

def coulombTestCharge (g : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  -(Δ g x)/(4*Real.pi)

lemma coulombTestCharge_continuous {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (coulombTestCharge g) := (tfLaplacian_continuous hg).neg.div_const _

lemma coulombTestCharge_compact {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    HasCompactSupport (coulombTestCharge g) := by
  change HasCompactSupport (fun x => (-Δ g x)*(4*Real.pi)⁻¹)
  exact ((tfLaplacian_compact hg hcg).neg).mul_right

lemma coulombTestCharge_support {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) :
    Function.support (coulombTestCharge g) ⊆ tsupport g := by
  intro x hx
  apply tfLaplacian_support hg
  intro hz
  exact hx (by simp [coulombTestCharge,hz])

theorem tfPotential_testCharge {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) (z : TFSpace) :
    tfPotential (coulombTestCharge g) z = g z := by
  have he : (fun x => coulombTestCharge g x/‖z-x‖) =
      fun x => (-(4*Real.pi)⁻¹)*(Δ g x/‖z-x‖) := by
    funext x
    unfold coulombTestCharge
    ring
  rw [tfPotential,he,integral_const_mul]
  change -(4*Real.pi)⁻¹*tfPotential (Δ g) z = g z
  rw [tfPotential_laplacian hg hcg z]
  field_simp [Real.pi_ne_zero]

theorem testCharge_dirichlet_energy {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, tfPotential (coulombTestCharge g) x*coulombTestCharge g x) =
      (4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) := by
  simp_rw [tfPotential_testCharge hg hcg,coulombTestCharge]
  have he : (fun x => g x*(-Δ g x/(4*Real.pi))) =
      fun x => -(4*Real.pi)⁻¹*(g x*Δ g x) := by funext x; ring
  rw [he,integral_const_mul,compact_laplacian_energy hg hcg]
  ring

open MeasureTheory Filter Set Metric InnerProductSpace Laplacian
open scoped BigOperators ContDiff Topology

lemma exists_patch_testCharge (R : ℝ) {g : TFSpace → ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    ∃ f : TFLp (ballMeasure R),
      (∀ x, tfBallPotential R f x = g x) ∧
      tfCoulombL R f f = (4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) := by
  let ρ := coulombTestCharge g
  have hρs : Function.support ρ ⊆ ball 0 R := (coulombTestCharge_support hg).trans hs
  have hρ : MemLp ρ (5/3) := (coulombTestCharge_continuous hg).memLp_of_hasCompactSupport
    (coulombTestCharge_compact hg hcg)
  have hm : MemLp ρ (5/3) (ballMeasure R) := hρ.mono_measure Measure.restrict_le_self
  let f : TFLp (ballMeasure R) := hm.toLp ρ
  have hf : (fun x => f x) =ᵐ[ballMeasure R] ρ := hm.coeFn_toLp
  have hpot (x : TFSpace) : tfBallPotential R f x = g x := by
    calc
      _ = ∫ y, ρ y/‖x-y‖ ∂ballMeasure R := integral_congr_ae (hf.mono fun y hy => by change f y = ρ y at hy; rw [hy])
      _ = ∫ y, ρ y/‖x-y‖ := by
        rw [ballMeasure,←integral_indicator measurableSet_ball]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          by_cases hy : y ∈ ball (0 : TFSpace) R
          · simp [hy]
          · have hz : ρ y = 0 := Function.notMem_support.mp (fun h => hy (hρs h))
            simp [hy,hz]
      _ = _ := tfPotential_testCharge hg hcg x
  refine ⟨f,hpot,?_⟩
  rw [tfCoulombL_potential]
  simp_rw [hpot]
  calc
    _ = ∫ x, g x*ρ x ∂ballMeasure R := integral_congr_ae (hf.mono fun x hx => by change f x = ρ x at hx; rw [hx])
    _ = ∫ x, g x*ρ x := by
      rw [ballMeasure,←integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ ball (0 : TFSpace) R
        · simp [hx]
        · have hz : ρ x = 0 := Function.notMem_support.mp (fun h => hx (hρs h))
          simp [hx,hz]
    _ = _ := by simpa only [tfPotential_testCharge hg hcg] using testCharge_dirichlet_energy hg hcg

theorem tfCoulomb_dirichlet_duality (R : ℝ) (f : TFLp (ballMeasure R))
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, g x*f x ∂ballMeasure R)^2 ≤
      ((4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2))*tfCoulombL R f f := by
  obtain ⟨q,hq,hqe⟩ := exists_patch_testCharge R hg hcg hs
  have he : tfCoulombL R q f = ∫ x, g x*f x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hq]
  simpa only [he,hqe] using tfCoulombL_pair_sq_le R q f

theorem tfPatchGap_test_control (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {g : TFSpace → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, g x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (2*(4*Real.pi)⁻¹*(∑ i : Fin 3, ∫ x, (tfPartial g i x)^2))*tfPatchGap R T hT Φ σ := by
  obtain ⟨q,hq,hqe⟩ := exists_patch_testCharge R hg hcg hs
  have he : tfCoulombL R q (σ-tfPatchMinimizer R T hT Φ) =
      ∫ x, g x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hq]
  have hh := tfPatchGap_pair_control R T hT Φ hσ q
  rw [he,hqe] at hh
  simpa only [mul_assoc] using hh

end CoulombAnalysis

end

end OAI
