import OAI.Analysis.LienardCycles.FixedWidthFamilies

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ParameterVariation
open ScalarArcs PartialCalculus ArchVariation

lemma arch_interior_pos {φ u : ℝ → ℝ} {h t a b y : ℝ}
    (hu : IsArch φ u h t a b) (hy : y ∈ Ioo a b) : h < u y := by
  by_cases hh : y ≤ φ t
  · have hi := hu.inc (show a ∈ Icc a (φ t) from ⟨le_rfl,hu.lower_lt_peak.le⟩)
      (show y ∈ Icc a (φ t) from ⟨hy.1.le,hh⟩) hy.1
    simpa only [hu.lower] using hi
  · have hi := hu.dec (show y ∈ Icc (φ t) b from ⟨(le_of_not_ge hh),hy.2.le⟩)
      (show b ∈ Icc (φ t) b from ⟨hu.peak_lt_upper.le,le_rfl⟩) hy.2
    simpa only [hu.upper] using hi

theorem positive_displacement {z a f : ℝ → ℝ} {l r δ : ℝ}
    (ha : Continuous a) (hz : ContinuousOn z (Icc l r))
    (hd : ∀ y ∈ Icc l r, HasDerivAt z (a y*z y+f y) y)
    (hf : ∀ y ∈ Ioo l r, 0 < f y) (hl : l < 0) (hr : 0 < r)
    (hzl : z l = δ*l) (hzr : z r = δ*r) : 0 < δ := by
  let w : ℝ → ℝ := fun y => Real.exp (-(∫ s in l..y, a s))
  let g : ℝ → ℝ := fun y => w y*z y
  have hwd (y : ℝ) : HasDerivAt w (-a y*w y) y := by
    convert (ha.integral_hasStrictDerivAt l y).hasDerivAt.neg.exp using 1;
      (first | rfl | (dsimp [w]; ring))
  have hgc : ContinuousOn g (Icc l r) :=
    (continuous_iff_continuousAt.mpr (fun y => (hwd y).continuousAt)).continuousOn.mul hz
  have hgd (y : ℝ) (hy : y ∈ Icc l r) : HasDerivAt g (w y*f y) y := by
    convert (hwd y).mul (hd y hy) using 1; (first | rfl | ring)
  have hm : StrictMonoOn g (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hgc
    intro y hy
    rw [(hgd y (interior_subset hy)).deriv]
    exact mul_pos (Real.exp_pos _) (hf y (by simpa only [interior_Icc] using hy))
  have hh := hm (show l ∈ Icc l r from ⟨le_rfl,(hl.trans hr).le⟩)
    (show r ∈ Icc l r from ⟨(hl.trans hr).le,le_rfl⟩) (hl.trans hr)
  dsimp [g] at hh
  rw [hzl,hzr] at hh
  have hwpos : 0 < w r := Real.exp_pos _
  have hwnon : 0 < w l := Real.exp_pos _
  have hden : 0 < w r*r-w l*l := by nlinarith
  nlinarith

theorem midpoint_positive {Φ u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {θ r t : ℝ}
    (hΦ : ContDiff ℝ ω Φ) (hbase : ∀ s, Φ (s,0) = 0)
    (hY : DifferentiableAt ℝ Y θ) (hr : 0 < r)
    (ha : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0 t (Y θ-r) (Y θ+r))
    (hu : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ContDiffAt ℝ ω u (θ,y))
    (he : ∀ y ∈ Icc (Y θ-r) (Y θ+r), ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2)
    (hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0)
    (hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0)
    (hpos : ∀ x, 0 < x → 0 < first Φ (θ,x)) : 0 < deriv Y θ := by
  let l := Y θ-r
  let b := Y θ+r
  have hlb : l < b := by dsimp [l,b]; linarith
  have hll : l ∈ Icc l b := ⟨le_rfl,hlb.le⟩
  have hbb : b ∈ Icc l b := ⟨hlb.le,le_rfl⟩
  have ha0 : l < 0 := by simpa only [hbase] using ha.lower_transverse
  have hb0 : 0 < b := by simpa only [hbase] using ha.upper_transverse
  have hac : Continuous (fun y => second Φ (θ,u (θ,y))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (second_contDiffAt (hΦ.contDiffAt)).continuousAt.comp
      (continuousAt_const.prodMk ha.continuous.continuousAt)
  have hzc : ContinuousOn (fun y => first u (θ,y)) (Icc l b) := by
    intro y hy
    exact ((first_contDiffAt (hu y hy)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzdl : HasDerivAt (fun y => u (θ,y)) (-l) l := by
    simpa only [show u (θ,l) = 0 from ha.lower,hbase,zero_sub] using ha.equation l hll
  have hzdb : HasDerivAt (fun y => u (θ,y)) (-b) b := by
    simpa only [show u (θ,b) = 0 from ha.upper,hbase,zero_sub] using ha.equation b hbb
  have hel := hit_variation ((hu l hll).differentiableAt (by simp))
    (hY.sub_const r) (hasDerivAt_const θ (0:ℝ)) hl
  have heb := hit_variation ((hu b hbb).differentiableAt (by simp))
    (hY.add_const r) (hasDerivAt_const θ (0:ℝ)) hb
  rw [(second_hasDerivAt ((hu l hll).differentiableAt (by simp))).unique hzdl,
    (hY.hasDerivAt.sub_const r).deriv] at hel
  rw [(second_hasDerivAt ((hu b hbb).differentiableAt (by simp))).unique hzdb,
    (hY.hasDerivAt.add_const r).deriv] at heb
  apply positive_displacement hac hzc
    (fun y hy => ?_) (fun y hy => hpos _ (arch_interior_pos ha hy)) ha0 hb0
    (show first u (θ,l) = deriv Y θ*l by linarith)
    (show first u (θ,b) = deriv Y θ*b by linarith)
  convert scalar_ode_variation (hu y hy) (hΦ.differentiable (by simp) _) (he y hy) using 1
  ring

end QuinticLienard.ParameterVariation

end OAI
