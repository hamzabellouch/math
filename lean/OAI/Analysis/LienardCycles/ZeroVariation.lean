import OAI.Analysis.LienardCycles.QuadraticVariation

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ParameterVariation
open ScalarArcs PartialCalculus ArchVariation

theorem zero_profile_variation {Φ u : ℝ × ℝ → ℝ} {Y B : ℝ → ℝ} {θ r t δ : ℝ}
    (hΦ : ContDiff ℝ ω Φ) (hzero : ∀ x, Φ (θ,x) = 0)
    (hY : DifferentiableAt ℝ Y θ) (hY0 : Y θ = 0) (hr : 0 < r)
    (ha : IsArch (fun x => Φ (θ,x)) (fun y => u (θ,y)) 0 t (-r) r)
    (hu : ∀ y ∈ Icc (-r) r, ContDiffAt ℝ ω u (θ,y))
    (he : ∀ y ∈ Icc (-r) r, ∀ᶠ q in 𝓝 (θ,y),
      HasDerivAt (fun s => u (q.1,s)) (Φ (q.1,u q)-q.2) q.2)
    (hl : ∀ᶠ s in 𝓝 θ, u (s,Y s-r) = 0)
    (hb : ∀ᶠ s in 𝓝 θ, u (s,Y s+r) = 0)
    (hB : ∀ y ∈ Icc (-r) r,
      HasDerivAt B (first Φ (θ,(r^2-y^2)/2)) y)
    (hBv : B r-B (-r) = 2*r*δ) : deriv Y θ = δ := by
  have hll : -r ∈ Icc (-r) r := ⟨le_rfl,by linarith⟩
  have hbb : r ∈ Icc (-r) r := ⟨by linarith,le_rfl⟩
  have hu0 : EqOn (fun y => u (θ,y)) (fun y => (r^2-y^2)/2) (Icc (-r) r) := by
    refine eq_of_hasDerivAt_eq_on_Icc ha.continuous.continuousOn (by fun_prop)
      (d := fun y => -y) ?_ ?_ hll (by simpa using ha.lower)
    · intro y hy
      simpa only [hzero,zero_sub] using ha.equation y hy
    · intro y _
      convert ((hasDerivAt_const y (r^2)).sub ((hasDerivAt_id y).pow 2)).div_const 2 using 1 <;>
        (first | rfl | (dsimp; ring))
  have hz (y : ℝ) (hy : y ∈ Icc (-r) r) :
      HasDerivAt (fun s => first u (θ,s)) (first Φ (θ,(r^2-y^2)/2)) y := by
    have hs : second Φ (θ,u (θ,y)) = 0 := by
      apply (second_hasDerivAt (hΦ.differentiable (by simp) _)).unique
      simpa only [hzero] using hasDerivAt_const (u (θ,y)) (0:ℝ)
    have hh := scalar_ode_variation (hu y hy) (hΦ.differentiable (by simp) _) (he y hy)
    have hv : u (θ,y) = (r^2-y^2)/2 := hu0 hy
    rw [hs,zero_mul,add_zero,hv] at hh
    exact hh
  have hzc : ContinuousOn (fun y => first u (θ,y)) (Icc (-r) r) := by
    intro y hy
    exact ((first_contDiffAt (hu y hy)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hBc : ContinuousOn B (Icc (-r) r) := fun y hy => (hB y hy).continuousAt.continuousWithinAt
  have hv := eq_of_hasDerivAt_eq_on_Icc hzc (hBc.add continuousOn_const) hz
    (fun y hy => (hB y hy).add_const (first u (θ,-r)-B (-r))) hll (by dsimp; ring)
  have hend := hv hbb
  dsimp at hend
  have hel := hit_variation (by simpa only [hY0,zero_sub] using
      (hu (-r) hll).differentiableAt (by simp))
    (hY.sub_const r) (hasDerivAt_const θ (0:ℝ)) hl
  have heb := hit_variation (by simpa only [hY0,zero_add] using
      (hu r hbb).differentiableAt (by simp))
    (hY.add_const r) (hasDerivAt_const θ (0:ℝ)) hb
  have hesl : second u (θ,-r) = r := by
    apply (second_hasDerivAt ((hu (-r) hll).differentiableAt (by simp))).unique
    simpa only [hzero,sub_neg_eq_add,zero_add] using ha.equation (-r) hll
  have hesb : second u (θ,r) = -r := by
    apply (second_hasDerivAt ((hu r hbb).differentiableAt (by simp))).unique
    simpa only [hzero,zero_sub] using ha.equation r hbb
  simp only [hY0,zero_sub,zero_add,(hY.hasDerivAt.sub_const r).deriv,
    (hY.hasDerivAt.add_const r).deriv,hesl,hesb] at hel heb
  nlinarith

end QuinticLienard.ParameterVariation

end OAI
