import OAI.Analysis.LienardCycles.RiccatiJets

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
namespace QuinticLienard.RiccatiJets
open PartialCalculus

lemma deriv_analytic {f : ℝ → ℝ} {t : ℝ} (hf : ContDiffAt ℝ ω f t) :
    ContDiffAt ℝ ω (deriv f) t := hf.derivWithin (by simp)

lemma curve_hasDerivAt {f : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t,Y t)) (hY : DifferentiableAt ℝ Y t) :
    HasDerivAt (fun s => f (s,Y s))
      (first f (t,Y t)+deriv Y t*second f (t,Y t)) t := by
  simpa only [fderiv_pair,one_mul] using!
    hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hY.hasDerivAt)

lemma root_first {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : second u (t,Y t) = d*u (t,Y t)+b*(u (t,Y t))^2-Y t)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first u (t,Y t) = Y t*deriv Y t := by
  have hd := ArchVariation.hit_variation (hu.differentiableAt (by simp))
    (hY.differentiableAt (by simp)) (hasDerivAt_const t (0:ℝ)) hroot
  rw [he,hroot.self_of_nhds] at hd
  nlinarith

lemma root_first_eventually {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : second u =ᶠ[𝓝 (t,Y t)] (fun q => d*u q+b*(u q)^2-q.2))
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    (fun s => first u (s,Y s)) =ᶠ[𝓝 t] (fun s => Y s*deriv Y s) := by
  have hc := continuousAt_id.prodMk hY.continuousAt
  filter_upwards [hc.eventually (hu.eventually (by simp)), hY.eventually (by simp),
    hc.eventually he,hroot.eventually_nhds] with s hus hYs hes hrs
  exact root_first hus hYs hes hrs

lemma root_second {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first (first u) (t,Y t) = (deriv Y t)^2+Y t*deriv (deriv Y) t-d*Y t*(deriv Y t)^2 := by
  have hj := jets_eventually hu he
  have hz := root_first_eventually hu hY hj.1 hroot
  have hd := curve_hasDerivAt ((first_contDiffAt hu).differentiableAt (by simp))
    (hY.differentiableAt (by simp))
  have hr := (hY.differentiableAt (by simp)).hasDerivAt.mul
    ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt
  have h := hd.unique (hr.congr_of_eventuallyEq hz)
  rw [hj.2.1.self_of_nhds] at h
  dsimp only at h
  have hz0 : first u (t,Y t) = Y t*deriv Y t := hz.self_of_nhds
  rw [hroot.self_of_nhds,hz0] at h
  nlinarith

lemma root_second_eventually {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    (fun s => first (first u) (s,Y s)) =ᶠ[𝓝 t]
      (fun s => (deriv Y s)^2+Y s*deriv (deriv Y) s-d*Y s*(deriv Y s)^2) := by
  have hc := continuousAt_id.prodMk hY.continuousAt
  filter_upwards [hc.eventually (hu.eventually (by simp)), hY.eventually (by simp),
    hc.eventually he.eventually_nhds,hroot.eventually_nhds] with s hus hYs hes hrs
  exact root_second hus hYs hes hrs

lemma root_third {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0) :
    first (first (first u)) (t,Y t) =
      Y t*deriv (deriv (deriv Y)) t +3*deriv Y t*deriv (deriv Y) t
      -3*d*Y t*deriv Y t*deriv (deriv Y) t-2*d*(deriv Y t)^3
      +d^2*Y t*(deriv Y t)^3-2*b*(Y t)^2*(deriv Y t)^3 := by
  have hj := jets_eventually hu he
  have hz := root_first_eventually hu hY hj.1 hroot
  have ha := root_second_eventually hu hY he hroot
  have hd := curve_hasDerivAt ((first_contDiffAt (first_contDiffAt hu)).differentiableAt (by simp))
    (hY.differentiableAt (by simp))
  have h1 := (hY.differentiableAt (by simp)).hasDerivAt
  have h2 := ((deriv_analytic hY).differentiableAt (by simp)).hasDerivAt
  have h3 := ((deriv_analytic (deriv_analytic hY)).differentiableAt (by simp)).hasDerivAt
  have hr := ((h2.pow 2).add (h1.mul h3)).sub ((h1.const_mul d).mul (h2.pow 2))
  have h := hd.unique (hr.congr_of_eventuallyEq ha)
  rw [hj.2.2.1.self_of_nhds] at h
  dsimp only at h
  have hz0 : first u (t,Y t) = Y t*deriv Y t := hz.self_of_nhds
  have ha0 := ha.self_of_nhds
  dsimp only at ha0
  rw [hroot.self_of_nhds,hz0,ha0] at h
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply] at h
  nlinarith

noncomputable def schwarzian (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv (deriv Y)) t/deriv Y t-(3/2)*(deriv (deriv Y) t/deriv Y t)^2

lemma root_invariants {u : ℝ × ℝ → ℝ} {Y : ℝ → ℝ} {t d b : ℝ}
    (hu : ContDiffAt ℝ ω u (t,Y t)) (hY : ContDiffAt ℝ ω Y t)
    (he : ∀ᶠ q in 𝓝 (t,Y t), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hroot : ∀ᶠ s in 𝓝 t, u (s,Y s)=0)
    (hy : Y t ≠ 0) (hl : deriv Y t ≠ 0) :
    logJet u (t,Y t) = deriv (deriv Y) t/deriv Y t+deriv Y t/Y t-d*deriv Y t ∧
    schwarzJet u (t,Y t) = schwarzian Y t+
      (deriv Y t)^2*(-2*b*Y t-d^2/2+d/Y t-3/(2*(Y t)^2)) := by
  have hz := (root_first_eventually hu hY (jets_eventually hu he).1 hroot).self_of_nhds
  dsimp only at hz
  have ha := root_second hu hY he hroot
  have hc := root_third hu hY he hroot
  dsimp [logJet,schwarzJet,schwarzian]
  rw [hz,ha,hc]
  constructor <;> field_simp <;> ring

end QuinticLienard.RiccatiJets

end OAI
