import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfDilation
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchEuler

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

lemma tfBallPotential_nonneg {R : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (x : TFSpace) : 0 ≤ tfBallPotential R f x := by
  apply integral_nonneg_of_ae
  filter_upwards [hf] with y hy
  exact div_nonneg hy (norm_nonneg _)

lemma tfPatchMinimizer_ae_bound {R T F : ℝ} (hT : 0 < T) (Φ : TFField R)
    (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    ∀ᵐ x ∂ballMeasure R, tfPatchMinimizer R T hT Φ x ≤
      (max F 0 / ((5/3:ℝ)*T))^(3/2:ℝ) := by
  let f := tfPatchMinimizer R T hT Φ
  have hf := tfPatchMinimizer_nonneg R T hT Φ
  have he := tfPatchFunctional_euler R Φ hT hf (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hΦ] with x he hpx
  rw [he]
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) (by positivity)) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact max_le_max_right 0 (by linarith [tfBallPotential_nonneg hf x])

def boundedPatchRepresentative (R B : ℝ) (f : TFLp (ballMeasure R)) : TFSpace → ℝ :=
  (ball 0 R).indicator (fun x => min (max (f x) 0) (max B 0))

lemma boundedPatchRepresentative_measurable (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Measurable (boundedPatchRepresentative R B f) :=
  ((Lp.stronglyMeasurable f).measurable.max measurable_const).min measurable_const
    |>.indicator measurableSet_ball

lemma boundedPatchRepresentative_nonneg (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    0 ≤ boundedPatchRepresentative R B f x :=
  indicator_nonneg (fun _ _ => le_min (le_max_right _ _) (le_max_right _ _)) x

lemma boundedPatchRepresentative_le (R B : ℝ) (f : TFLp (ballMeasure R)) (x : TFSpace) :
    boundedPatchRepresentative R B f x ≤ max B 0 := by
  by_cases hx : x ∈ ball (0 : TFSpace) R
  · simp only [boundedPatchRepresentative,indicator_of_mem hx]
    exact min_le_right _ _
  · simp only [boundedPatchRepresentative,indicator_of_notMem hx]
    exact le_max_right _ _

lemma boundedPatchRepresentative_support (R B : ℝ) (f : TFLp (ballMeasure R)) :
    Function.support (boundedPatchRepresentative R B f) ⊆ closedBall 0 R :=
  support_indicator_subset.trans ball_subset_closedBall

lemma boundedPatchRepresentative_ae {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    boundedPatchRepresentative R B f =ᵐ[volume] tfExtension R f := by
  have hh := (ae_restrict_iff' measurableSet_ball).mp (hf.and hb)
  filter_upwards [hh] with x hx
  by_cases hmem : x ∈ ball (0 : TFSpace) R
  · dsimp [boundedPatchRepresentative,tfExtension]
    rw [indicator_of_mem hmem,indicator_of_mem hmem,max_eq_left (hx hmem).1,
      min_eq_left ((hx hmem).2.trans (le_max_left _ _))]
  · simp only [boundedPatchRepresentative,tfExtension,indicator_of_notMem hmem]

lemma boundedPatchRepresentative_ae_ball {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    boundedPatchRepresentative R B f =ᵐ[ballMeasure R] f := by
  filter_upwards [hf,hb,ae_restrict_mem measurableSet_ball] with x hf hb hx
  simp only [boundedPatchRepresentative,indicator_of_mem hx,max_eq_left hf,
    min_eq_left (hb.trans (le_max_left _ _))]

lemma boundedPatchRepresentative_mass {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, boundedPatchRepresentative R B f x) = ∫ x, f x ∂ballMeasure R := by
  rw [integral_congr_ae (boundedPatchRepresentative_ae hf hb)]
  exact integral_indicator measurableSet_ball

lemma boundedPatchRepresentative_kinetic {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ x, (boundedPatchRepresentative R B f x)^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_rpow_nonneg hf]
  have he := boundedPatchRepresentative_ae hf hb
  have he' : (fun x => (boundedPatchRepresentative R B f x)^(5/3:ℝ)) =ᵐ[volume]
      fun x => (tfExtension R f x)^(5/3:ℝ) := he.mono fun _ hx => congrArg (fun t : ℝ => t^(5/3:ℝ)) hx
  rw [integral_congr_ae he']
  simp_rw [tfExtension_kinetic]
  exact integral_indicator measurableSet_ball

lemma boundedPatchRepresentative_coulomb {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) :
    (∫ p : TFSpace × TFSpace, boundedPatchRepresentative R B f p.1 *
      boundedPatchRepresentative R B f p.2 / ‖p.1-p.2‖) = tfCoulombL R f f := by
  rw [tfCoulombL_extension]
  have he := boundedPatchRepresentative_ae hf hb
  apply integral_congr_ae
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he,
    Measure.quasiMeasurePreserving_snd.ae he] with p h1 h2
  rw [h1,h2]

lemma boundedPatchRepresentative_field {R B : ℝ} {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hb : ∀ᵐ x ∂ballMeasure R, f x ≤ B) (Φ : TFSpace → ℝ) :
    (∫ x, Φ x*boundedPatchRepresentative R B f x) = ∫ x, Φ x*f x ∂ballMeasure R := by
  have he : (fun x => Φ x*tfExtension R f x) =
      (ball 0 R).indicator (fun x => Φ x*f x) := by
    funext x
    by_cases hx : x ∈ ball (0 : TFSpace) R <;> simp [tfExtension,hx]
  calc
    _ = ∫ x, Φ x*tfExtension R f x := integral_congr_ae
      ((boundedPatchRepresentative_ae hf hb).mono fun x hx => by rw [hx])
    _ = _ := by rw [he]; exact integral_indicator measurableSet_ball

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

def patchMeasure (y : TFSpace) (R : ℝ) : Measure TFSpace := volume.restrict (ball y R)

lemma patch_translation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x => y+x) (ballMeasure R) (patchMeasure y R) := by
  have he : (fun x : TFSpace => y+x) ⁻¹' ball y R = ball 0 R := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hh := (measurePreserving_add_left (volume : Measure TFSpace) y).restrict_preimage
    (s := ball y R) measurableSet_ball
  rw [he] at hh
  exact hh

lemma patch_untranslation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x => -y+x) (patchMeasure y R) (ballMeasure R) :=
  (patch_translation_preserving y R).symm (MeasurableEquiv.addLeft y)

def patchPull {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (patchMeasure y R)) : Lp ℝ p (ballMeasure R) :=
  Lp.compMeasurePreserving (fun x => y+x) (patch_translation_preserving y R) f

def patchPush {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (ballMeasure R)) : Lp ℝ p (patchMeasure y R) :=
  Lp.compMeasurePreserving (fun x => -y+x) (patch_untranslation_preserving y R) f

lemma patchPull_coe {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (patchMeasure y R)) :
    patchPull y R f =ᵐ[ballMeasure R] fun x => f (y+x) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma patchPush_coe {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (ballMeasure R)) :
    patchPush y R f =ᵐ[patchMeasure y R] fun x => f (-y+x) :=
  Lp.coeFn_compMeasurePreserving _ _

@[simp] lemma patchPull_push {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (ballMeasure R)) : patchPull y R (patchPush y R f) = f := by
  apply Lp.ext
  filter_upwards [patchPull_coe y R (patchPush y R f),
    (patch_translation_preserving y R).quasiMeasurePreserving.ae (patchPush_coe y R f)] with x hx hg
  rw [hx, hg, neg_add_cancel_left]

@[simp] lemma patchPush_pull {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (patchMeasure y R)) : patchPush y R (patchPull y R f) = f := by
  apply Lp.ext
  filter_upwards [patchPush_coe y R (patchPull y R f),
    (patch_untranslation_preserving y R).quasiMeasurePreserving.ae (patchPull_coe y R f)] with x hx hg
  rw [hx, hg, add_neg_cancel_left]

@[simp] lemma patchPull_norm {p : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (f : Lp ℝ p (patchMeasure y R)) : ‖patchPull y R f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

lemma patchPull_nonneg (y : TFSpace) (R : ℝ) {f : TFLp (patchMeasure y R)}
    (hf : NonnegDensity f) : NonnegDensity (patchPull y R f) := by
  filter_upwards [patchPull_coe y R f,
    (patch_translation_preserving y R).quasiMeasurePreserving.ae hf] with x hx hf
  rw [hx]; exact hf

lemma patchPush_nonneg (y : TFSpace) (R : ℝ) {f : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) : NonnegDensity (patchPush y R f) := by
  filter_upwards [patchPush_coe y R f,
    (patch_untranslation_preserving y R).quasiMeasurePreserving.ae hf] with x hx hf
  rw [hx]; exact hf

lemma patchPull_integral_pair {p q : ℝ≥0∞} (y : TFSpace) (R : ℝ)
    (Φ : Lp ℝ p (patchMeasure y R)) (f : Lp ℝ q (patchMeasure y R)) :
    (∫ x, patchPull y R Φ x * patchPull y R f x ∂ballMeasure R) =
      ∫ x, Φ x * f x ∂patchMeasure y R := by
  calc
    _ = ∫ x, Φ (y+x) * f (y+x) ∂ballMeasure R := by
      apply integral_congr_ae
      filter_upwards [patchPull_coe y R Φ, patchPull_coe y R f] with x hx hf
      rw [hx,hf]
    _ = _ := (patch_translation_preserving y R).integral_comp
      (Homeomorph.addLeft y).measurableEmbedding (fun x => Φ x * f x)

lemma patchPull_coulomb (y : TFSpace) (R : ℝ) (f g : TFLp (patchMeasure y R)) :
    tfCoulombL R (patchPull y R f) (patchPull y R g) =
      ∫ p : TFSpace × TFSpace, f p.1 * g p.2 / ‖p.1-p.2‖
        ∂(patchMeasure y R).prod (patchMeasure y R) := by
  rw [tfCoulombL_apply]
  calc
    _ = ∫ p : TFSpace × TFSpace, f (y+p.1) * g (y+p.2) / ‖(y+p.1)-(y+p.2)‖
        ∂(ballMeasure R).prod (ballMeasure R) := by
      apply integral_congr_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (patchPull_coe y R f),
        (Measure.quasiMeasurePreserving_snd (μ := ballMeasure R)
        (ν := ballMeasure R)).ae (patchPull_coe y R g)] with p hf hg
      rw [hf,hg,add_sub_add_left_eq_sub]
    _ = _ := (patch_translation_preserving y R |>.prod (patch_translation_preserving y R)).integral_comp
      ((Homeomorph.addLeft y).measurableEmbedding.prodMap (Homeomorph.addLeft y).measurableEmbedding)
      (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1-p.2‖)

def patchFunctional (y : TFSpace) (R T : ℝ) (Φ : Lp ℝ (5/2) (patchMeasure y R))
    (f : TFLp (patchMeasure y R)) : ℝ :=
  T*‖f‖^(5/3:ℝ) - (∫ x, Φ x * f x ∂patchMeasure y R) +
    (1/2:ℝ)*(∫ p : TFSpace × TFSpace, f p.1 * f p.2 / ‖p.1-p.2‖
      ∂(patchMeasure y R).prod (patchMeasure y R))

lemma patchFunctional_pull (y : TFSpace) (R T : ℝ) (Φ : Lp ℝ (5/2) (patchMeasure y R))
    (f : TFLp (patchMeasure y R)) :
    tfPatchFunctional R T (patchPull y R Φ) (patchPull y R f) = patchFunctional y R T Φ f := by
  simp only [tfPatchFunctional, tfPatchLinear_apply, patchPull_norm, patchPull_integral_pair,
    patchPull_coulomb, patchFunctional, sub_eq_add_neg]

theorem patchFunctional_existsUnique (y : TFSpace) (R : ℝ) {T : ℝ} (hT : 0 < T)
    (Φ : Lp ℝ (5/2) (patchMeasure y R)) :
    ∃! f : TFLp (patchMeasure y R), NonnegDensity f ∧
      ∀ g, NonnegDensity g → patchFunctional y R T Φ f ≤ patchFunctional y R T Φ g := by
  let f := tfPatchMinimizer R T hT (patchPull y R Φ)
  refine ⟨patchPush y R f, ⟨patchPush_nonneg y R (tfPatchMinimizer_nonneg ..), ?_⟩, ?_⟩
  · intro g hg
    rw [← patchFunctional_pull, patchPull_push, ← patchFunctional_pull]
    exact tfPatchMinimizer_min R T hT (patchPull y R Φ) (patchPull_nonneg y R hg)
  · intro g hg
    have he : patchPull y R g = f := by
      apply tfPatchFunctional_min_unique R (patchPull y R Φ) hT (patchPull_nonneg y R hg.1)
        (tfPatchMinimizer_nonneg ..)
      · intro u hu
        have hh := hg.2 _ (patchPush_nonneg y R hu)
        rw [← patchFunctional_pull, ← patchFunctional_pull, patchPull_push] at hh
        exact hh
      · exact fun _ hu => tfPatchMinimizer_min R T hT (patchPull y R Φ) hu
    rw [← he, patchPush_pull]

end CoulombAnalysis

end

end OAI
