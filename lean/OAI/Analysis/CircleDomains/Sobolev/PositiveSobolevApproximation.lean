import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates
import OAI.Analysis.CircleDomains.Sobolev.PositiveMollification
import OAI.Analysis.KLS.Sobolev.SobolevApproximation

namespace OAI

/-! An explicit positive mollification of a compactly supported planar
Sobolev function. The values and weak derivatives converge in L². -/

open Set Filter MeasureTheory
open scoped ENNReal Topology Convolution

noncomputable section

namespace CircleDomainRigidity

def planarMollification (u : EuclideanPlane → ℝ) (n : ℕ) : EuclideanPlane → ℝ :=
  ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)

theorem planarMollification_smooth {u : EuclideanPlane → ℝ}
    (hu : LocallyIntegrable u volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (planarMollification u n) :=
  (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed.contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed hu

theorem planarMollification_mem_Icc {u : EuclideanPlane → ℝ}
    (hu : AEStronglyMeasurable u volume) {a b : ℝ} (hb : ∀x, u x ∈ Icc a b)
    (n : ℕ) (x : EuclideanPlane) : planarMollification u n x ∈ Icc a b :=
  normed_convolution_mem_Icc volume (DeGiorgi.shrinkingBump n) hu (fun y _ => hb y)

theorem planarMollification_hasCompactSupport {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) (n : ℕ) : HasCompactSupport (planarMollification u n) := by
  exact (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed.convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hu

theorem tendsto_planarMollifier_radius :
    Tendsto (fun n => (DeGiorgi.shrinkingBump (d := 2) n).rOut) atTop (𝓝 0) := by
  simpa only [DeGiorgi.shrinkingBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem planarMollification_tsupport_subset (u : EuclideanPlane → ℝ) (n : ℕ) :
    tsupport (planarMollification u n) ⊆
      Metric.cthickening (DeGiorgi.shrinkingBump (d := 2) n).rOut (tsupport u) := by
  have hs := support_convolution_subset
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (DeGiorgi.shrinkingBump (d := 2) n).normed volume) (g := u)
  apply closure_minimal (hs.trans ?_) Metric.isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
  rw [(DeGiorgi.shrinkingBump (d := 2) n).support_normed_eq] at ha
  have ha' : ‖a‖ < (DeGiorgi.shrinkingBump (d := 2) n).rOut := by
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  apply Metric.mem_cthickening_of_dist_le (x := a + b) (y := b)
    (δ := (DeGiorgi.shrinkingBump (d := 2) n).rOut) (tsupport u)
    (subset_tsupport u hb)
  simpa only [dist_eq_norm, add_sub_cancel_right] using ha'.le

theorem planarMollification_support_eventually {u : EuclideanPlane → ℝ}
    (hu : HasCompactSupport u) {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hsub : tsupport u ⊆ Ω) : ∀ᶠ n in atTop, tsupport (planarMollification u n) ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.isCompact.exists_cthickening_subset_open hΩ hsub
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn
  exact (planarMollification_tsupport_subset u n).trans
      ((Metric.cthickening_mono hn.le _).trans hδΩ)

theorem planarMollification_eventually_eq_on_plateau
    {u : EuclideanPlane → ℝ} {V : Set EuclideanPlane} (hV : IsOpen V)
    {c : ℝ} (hc : ∀x ∈ V, u x = c) {x : EuclideanPlane} (hx : x ∈ V) :
    ∀ᶠ n in atTop, planarMollification u n x = c := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV x hx
  have hr : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < δ :=
    (tendsto_order.1 tendsto_planarMollifier_radius).2 δ hδ
  filter_upwards [hr] with n hn
  exact normed_convolution_eq_of_constant volume (DeGiorgi.shrinkingBump n)
    (fun y hy => hc y (hball ((Metric.ball_subset_ball hn.le) hy)))

theorem planarMollification_derivative_of_weak {u g : EuclideanPlane → ℝ}
    (hu : LocallyIntegrable u volume) (i : Fin 2)
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u univ) (n : ℕ) (x : EuclideanPlane) :
    (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) =
      ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  let bump : EuclideanPlane → ℝ := (DeGiorgi.shrinkingBump (d := 2) n).normed volume
  let Dbump : EuclideanPlane → EuclideanPlane →L[ℝ] ℝ := fderiv ℝ bump
  let ei : EuclideanPlane := EuclideanSpace.single i 1
  have hb : ContDiff ℝ 1 bump := (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed
  have hs : HasCompactSupport bump := (DeGiorgi.shrinkingBump (d := 2) n).hasCompactSupport_normed
  have hd := hs.hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hb hu x
  have hd' : (fderiv ℝ (planarMollification u n) x) ei =
      ((Dbump ⋆[ContinuousLinearMap.precompL EuclideanPlane
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei := by
    simpa only [planarMollification, bump, Dbump] using
      congrArg (fun A : EuclideanPlane →L[ℝ] ℝ => A ei) hd.fderiv
  have hconv :
      ((Dbump ⋆[ContinuousLinearMap.precompL EuclideanPlane
        (ContinuousLinearMap.lsmul ℝ ℝ), volume] u) x) ei =
      ((fun y => (fderiv ℝ bump y) ei) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
    calc
      _ = ((u ⋆[ContinuousLinearMap.precompR EuclideanPlane
          (ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] Dbump) x) ei := by
        simpa [ContinuousLinearMap.precompL, Dbump] using
          congrArg (fun F => F x ei) (MeasureTheory.convolution_flip
            (L := ContinuousLinearMap.precompR EuclideanPlane (ContinuousLinearMap.lsmul ℝ ℝ).flip)
            (μ := volume) (f := u) (g := Dbump))
      _ = (u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] (fun y => Dbump y ei)) x := by
        exact MeasureTheory.convolution_precompR_apply
          (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (μ := volume)
          (f := u) (g := Dbump) hu (hs.fderiv (𝕜 := ℝ))
          (hb.continuous_fderiv one_ne_zero) x ei
      _ = _ := by
        simpa [Dbump] using congrArg (fun F => F x)
          ((MeasureTheory.convolution_flip (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
            (μ := volume) (f := u) (g := fun y => Dbump y ei)).symm)
  exact hd'.trans (hconv.trans
    (DeGiorgi.convolution_fderiv_eq_convolution_weakPartial_univ hweak
      (DeGiorgi.shrinkingBump (d := 2) n).contDiff_normed hs x))


theorem planarMollification_derivative {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u univ) (n : ℕ) (i : Fin 2) (x : EuclideanPlane) :
    (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) =
      ((DeGiorgi.shrinkingBump (d := 2) n).normed volume
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => hw.weakGrad y i)) x := by
  have hm : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  exact planarMollification_derivative_of_weak (hm.locallyIntegrable (by norm_num))
    i (hw.isWeakGrad i) n x

theorem planarMollification_tendsto_L2 {u : EuclideanPlane → ℝ}
    (hu : MemLp u 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => planarMollification u n x - u x) 2 volume)
      atTop (𝓝 0) := by
  have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) volume := by simpa using hu
  simpa only [planarMollification, ENNReal.ofReal_ofNat] using
    DeGiorgi.tendsto_eLpNorm_normedConvolution_sub (d := 2) (p := 2) (by norm_num) hu'

theorem planarMollification_tendsto_gradient_L2 {u : EuclideanPlane → ℝ}
    (hw : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun x =>
      (fderiv ℝ (planarMollification u n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
      2 volume) atTop (𝓝 0) := by
  have hgi : MemLp (fun x => hw.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hw.weakGrad_component_memLp i
  have h := planarMollification_tendsto_L2 hgi
  convert h using 1
  funext n
  apply eLpNorm_congr_ae
  exact Eventually.of_forall fun x => congrArg (fun z => z - hw.weakGrad x i)
    (planarMollification_derivative hw n i x)

theorem exists_positive_smooth_compact_approx
    {u : EuclideanPlane → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u univ)
    (hs : HasCompactSupport u) (hunit : ∀x, u x ∈ Icc 0 1)
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) (hsub : tsupport u ⊆ Ω) :
    ∃ φ : ℕ → EuclideanPlane → ℝ,
      (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n) ∧
        tsupport (φ n) ⊆ Ω ∧ ∀x, φ n x ∈ Icc 0 1) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - u x) 2 volume) atTop (𝓝 0) ∧
      ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 volume)
        atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (planarMollification_support_eventually hs hΩ hsub)
  have hu : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hw.memLp
  refine ⟨fun n => planarMollification u (n + N), ?_, ?_, ?_⟩
  · intro n
    exact ⟨planarMollification_smooth (hu.locallyIntegrable (by norm_num)) _,
      planarMollification_hasCompactSupport hs _, hN _ (Nat.le_add_left _ _),
      planarMollification_mem_Icc hu.aestronglyMeasurable hunit _⟩
  · exact (planarMollification_tendsto_L2 hu).comp (tendsto_add_atTop_nat N)
  · intro i
    exact (planarMollification_tendsto_gradient_L2 hw i).comp (tendsto_add_atTop_nat N)

end CircleDomainRigidity

end

end OAI
