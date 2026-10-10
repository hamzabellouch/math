import OAI.Analysis.CircleDomains.Topology.PlanarPairCalculus
import OAI.Analysis.CircleDomains.Sobolev.SobolevConformalTransport
import OAI.Analysis.CircleDomains.Sobolev.L2ProductConvergence

namespace OAI

/-! The joint smooth chain rule for the actual continuous compact source
coordinates. Positive mollification converges pointwise and in gradient
L2, so the two coefficient products pass to the weak derivative. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem compact_pair_weak_chain
    {u v : EuclideanPlane → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hsu : HasCompactSupport u) (hsv : HasCompactSupport v)
    (Wu : DeGiorgi.MemW1pWitness 2 u univ) (Wv : DeGiorgi.MemW1pWitness 2 v univ)
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {B C : ℝ} (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (hΦb : ∀ y, ‖Φ y‖ ≤ B) (hΦd : ∀ y, ‖fderiv ℝ Φ y‖ ≤ C) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (0 : Fin 2) 1)*Wu.weakGrad x i+
        fderiv ℝ Φ (planePair (u x) (v x)) (EuclideanSpace.single (1 : Fin 2) 1)*Wv.weakGrad x i)
      (fun x => Φ (planePair (u x) (v x))) univ := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using Wu.memLp
  have hvL : MemLp v 2 volume := by simpa only [Measure.restrict_univ] using Wv.memLp
  have hGu : MemLp (fun x => Wu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using Wu.weakGrad_component_memLp i
  have hGv : MemLp (fun x => Wv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using Wv.weakGrad_component_memLp i
  let a := planarMollification u
  let b := planarMollification v
  let P := fun x => planePair (u x) (v x)
  let Pn := fun n x => planePair (a n x) (b n x)
  let k := fun (j : Fin 2) y => fderiv ℝ Φ y (EuclideanSpace.single j 1)
  have hkc (j : Fin 2) : Continuous (k j) :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hkb (j : Fin 2) (y : EuclideanPlane) : ‖k j y‖ ≤ C := by
    have h := (fderiv ℝ Φ y).le_opNorm (EuclideanSpace.single j 1)
    have h' : ‖k j y‖ ≤ ‖fderiv ℝ Φ y‖ := by
      simpa only [PiLp.norm_single, norm_one, mul_one] using h
    exact h'.trans (hΦd y)
  have has (n : ℕ) : ContDiff ℝ 1 (a n) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n).of_le (by simp)
  have hbs (n : ℕ) : ContDiff ℝ 1 (b n) :=
    (planarMollification_smooth (hvL.locallyIntegrable (by norm_num)) n).of_le (by simp)
  have hPs (n : ℕ) : ContDiff ℝ 1 (Pn n) := contDiff_planePair (has n) (hbs n)
  have hPt (x : EuclideanPlane) : Tendsto (fun n => Pn n x) atTop (𝓝 (P x)) :=
    ((planarMollification_tendsto_of_continuous hu x).smul tendsto_const_nhds).add
      ((planarMollification_tendsto_of_continuous hv x).smul tendsto_const_nhds)
  intro φ hφ hs hsub
  let e : EuclideanPlane := EuclideanSpace.single i 1
  have hdc : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun x => fderiv ℝ φ x e) := hs.fderiv_apply (𝕜 := ℝ) e
  have hφL : MemLp φ 2 (volume : Measure EuclideanPlane) :=
    hφ.continuous.memLp_of_hasCompactSupport hs
  have hleft := tendsto_integral_of_dominated_convergence (μ := (volume : Measure EuclideanPlane))
    (F := fun n x => Φ (Pn n x)*fderiv ℝ φ x e)
    (f := fun x => Φ (P x)*fderiv ℝ φ x e)
    (fun x => B*‖fderiv ℝ φ x e‖)
    (fun n => ((hΦ.comp (hPs n)).continuous.aestronglyMeasurable).mul hdc.aestronglyMeasurable)
    ((hdc.integrable_of_hasCompactSupport hds).norm.const_mul B)
    (fun n => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΦb _) (norm_nonneg _)))
    (Eventually.of_forall (fun x => ((hΦ.continuous.tendsto _).comp (hPt x)).mul_const _))
  have hrightu := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (a n) x e) (G := fun x => Wu.weakGrad x i)
    (h := fun n x => k 0 (Pn n x)) (H := fun x => k 0 (P x)) (φ := φ)
    (fun n => planarMollification_partial_memLp Wu hsu n i) hGu hφL
    (planarMollification_tendsto_gradient_L2 Wu i)
    (fun n => ((hkc 0).comp (hPs n).continuous).aestronglyMeasurable)
    hC (fun n => Eventually.of_forall (fun x => hkb 0 _))
    (Eventually.of_forall (fun x => ((hkc 0).tendsto _).comp (hPt x)))
  have hrightv := tendsto_integral_bounded_mul_L2
    (g := fun n x => fderiv ℝ (b n) x e) (G := fun x => Wv.weakGrad x i)
    (h := fun n x => k 1 (Pn n x)) (H := fun x => k 1 (P x)) (φ := φ)
    (fun n => planarMollification_partial_memLp Wv hsv n i) hGv hφL
    (planarMollification_tendsto_gradient_L2 Wv i)
    (fun n => ((hkc 1).comp (hPs n).continuous).aestronglyMeasurable)
    hC (fun n => Eventually.of_forall (fun x => hkb 1 _))
    (Eventually.of_forall (fun x => ((hkc 1).tendsto _).comp (hPt x)))
  have hI {g : EuclideanPlane → ℝ} (hg : MemLp g 2 volume)
      {t : EuclideanPlane → ℝ} (ht : AEStronglyMeasurable t volume) (htb : ∀ x, ‖t x‖ ≤ C) :
      Integrable (fun x => t x*g x*φ x) := by
    apply ((hg.integrable_mul hφL).norm.const_mul C).mono'
      ((ht.mul hg.aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖t x*g x*φ x‖ ≤ C*‖g x*φ x‖
      simpa only [norm_mul, mul_assoc] using mul_le_mul_of_nonneg_right (htb x) (norm_nonneg (g x*φ x))
  have heq (n : ℕ) : (∫ x, Φ (Pn n x)*fderiv ℝ φ x e) =
      -((∫ x, k 0 (Pn n x)*fderiv ℝ (a n) x e*φ x)+
        (∫ x, k 1 (Pn n x)*fderiv ℝ (b n) x e*φ x)) := by
    have hw := DeGiorgi.HasWeakPartialDeriv.of_contDiff (i := i) isOpen_univ
      (hΦ.comp (hPs n)) φ hφ hs hsub
    simp only [Measure.restrict_univ] at hw
    have hd (x : EuclideanPlane) : fderiv ℝ (fun y => Φ (Pn n y)) x e =
        k 0 (Pn n x)*fderiv ℝ (a n) x e+k 1 (Pn n x)*fderiv ℝ (b n) x e :=
      fderiv_planePair_comp ((has n).differentiable one_ne_zero x)
        ((hbs n).differentiable one_ne_zero x) (hΦ.differentiable one_ne_zero _) e
    change (∫ x, Φ (Pn n x)*fderiv ℝ φ x e) =
      -(∫ x, fderiv ℝ (fun y => Φ (Pn n y)) x e*φ x) at hw
    simp only [hd, add_mul] at hw
    rw [integral_add (hI (t := fun x => k 0 (Pn n x)) (planarMollification_partial_memLp Wu hsu n i)
      (((hkc 0).comp (hPs n).continuous).aestronglyMeasurable) (fun x => hkb 0 _))
      (hI (t := fun x => k 1 (Pn n x)) (planarMollification_partial_memLp Wv hsv n i)
      (((hkc 1).comp (hPs n).continuous).aestronglyMeasurable) (fun x => hkb 1 _))] at hw
    exact hw
  have hPr : Continuous P := continuous_planePair hu hv
  have hsum := hrightu.add hrightv
  have hIu := hI (t := fun x => k 0 (P x)) hGu
    (((hkc 0).comp hPr).aestronglyMeasurable) (fun x => hkb 0 _)
  have hIv := hI (t := fun x => k 1 (P x)) hGv
    (((hkc 1).comp hPr).aestronglyMeasurable) (fun x => hkb 1 _)
  have hls : (∫ x, k 0 (P x)*Wu.weakGrad x i*φ x)+
      (∫ x, k 1 (P x)*Wv.weakGrad x i*φ x) =
      ∫ x, (k 0 (P x)*Wu.weakGrad x i+k 1 (P x)*Wv.weakGrad x i)*φ x := by
    rw [← integral_add hIu hIv]
    congr 1
    funext x
    ring
  rw [hls] at hsum
  simp only [Measure.restrict_univ]
  exact tendsto_nhds_unique hleft (by simpa only [heq] using hsum.neg)

end CircleDomainRigidity

end

end OAI
