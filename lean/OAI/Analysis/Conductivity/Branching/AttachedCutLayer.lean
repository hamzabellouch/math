import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndLayer
import OAI.Analysis.Conductivity.Variational.AffineLayer
import OAI.Analysis.Conductivity.Walls.LocalizedMatchedSeam

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal

lemma continuous_sourceBand_memLp {q : (Fin 3 → ℝ) → ℝ} (hq : Continuous q)
    {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    MemLp q 2 (volume.restrict (sourceClosedCollarBand l r)) := by
  have hc := isCompact_sourceClosedCollarBand hl hr
  let : IsFiniteMeasure (volume.restrict (sourceClosedCollarBand l r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuousOn hq.continuousOn
  exact MemLp.of_bound hq.aestronglyMeasurable M
    ((ae_restrict_mem hc.measurableSet).mono (fun x hx => hM x hx))

lemma smooth_attachedEnd_cut_layer_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ∀ x,|χ x|≤1) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h)
    (hu : MemLp (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
      (fun x => (attachedEndPoissonField s f a b 0 x).re-q x)) 2 volume)
    {ε : ℝ} (hε : 0<ε) (hεη : ε≤|a| *η) :
    (∫ x in {x | 0<a*(sourceCollarTime x-b) ∧ a*(sourceCollarTime x-b)≤ε},
      (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
        (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2)≤
      (sourceCollarVolumeConstant*(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)/|a|^3)*ε^3 := by
  let l := min b (b+ε/a)
  let r := max b (b+ε/a)
  obtain ⟨hlen,hleft,hright,hiff,hnear⟩ := affine_layer_interval (b:=b) ha hε.le
  have heη : ε/|a|≤η := (div_le_iff₀ (abs_pos.mpr ha)).mpr (by simpa [mul_comm] using hεη)
  have hl' : -(1:ℝ)/100≤l := hl.trans (by dsimp [l]; linarith)
  have hr' : r≤(1:ℝ)/100 := (by dsimp [r]; linarith : r≤b+η).trans hr
  have hb : b∈Icc (-(1:ℝ)/100) (1/100) := ⟨by linarith,by linarith⟩
  have hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 ε := fun t ht => (hiff t).mp ht
  have hp := ((attachedEndPoissonField_memLp s hs f ha hε.le (min_le_max) hl' hr' hT 0).re.sub
    (continuous_sourceBand_memLp hq.continuous hl' hr')).integrable_sq
  have hup := hu.integrable_sq
  calc
    _ ≤ ∫ x in sourceClosedCollarBand l r,
        (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
          (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2 := by
      apply setIntegral_mono_set hup.integrableOn
        (Eventually.of_forall (fun x => sq_nonneg _))
      exact Eventually.of_forall (fun x hx => (hiff _).mpr ⟨hx.1.le,hx.2⟩)
    _ ≤ ∫ x in sourceClosedCollarBand l r,((attachedEndPoissonField s f a b 0 x).re-q x)^2 := by
      apply integral_mono_ae hup.integrableOn hp
      apply Eventually.of_forall
      intro x
      by_cases ht : 0<a*(sourceCollarTime x-b)
      · simp only [cutMatchedValue,ht,ite_eq_left,mul_pow]
        have hsq : (χ x)^2≤1 := by
          simpa only [sq_abs,one_pow] using (pow_le_pow_left₀ (abs_nonneg (χ x)) (hχ x) 2)
        simpa only [one_mul,Pi.sub_apply,RCLike.re_to_complex] using mul_le_mul_of_nonneg_right hsq
          (sq_nonneg ((attachedEndPoissonField s f a b 0 x).re-q x))
      · simp only [cutMatchedValue,ht,ite_false,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
        positivity
    _ ≤ sourceCollarVolumeConstant*(r-l)*((2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(ε/|a|)^2) :=
      smooth_attachedEnd_band_rate hs f hq hK ha hε.le (by positivity) hb min_le_max hl' hr' hT hnear htrace g hg
    _ = _ := by
      change sourceCollarVolumeConstant*(max b (b+ε/a)-min b (b+ε/a))*_= _
      rw [hlen]
      ring

lemma smooth_attachedEnd_cut_thin {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h)
    (hu : MemLp (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
      (fun x => (attachedEndPoissonField s f a b 0 x).re-q x)) 2 volume) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<a*(sourceCollarTime x-b) ∧ ((n:ℝ)+1)*(a*(sourceCollarTime x-b))≤2},
      (cutMatchedValue (fun x => a*(sourceCollarTime x-b)) χ
        (fun x => (attachedEndPoissonField s f a b 0 x).re-q x) x)^2) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := smooth_sourceCollar_lipschitz hq
  apply seamLayer_scaled_tendsto_of_cubic_pi (mul_pos (abs_pos.mpr ha) hη)
  intro ε hε hεη
  exact smooth_attachedEnd_cut_layer_rate hs f hq hχ hK ha hη hl hr htrace g hg hu hε hεη

end ScalarConductivity

end

end OAI
