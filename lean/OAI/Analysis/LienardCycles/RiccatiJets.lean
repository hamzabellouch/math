import OAI.Analysis.LienardCycles.ModelEndpoint

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

lemma mixed_equation {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ ω f p) (he : second f =ᶠ[𝓝 p] g)
    (hg : HasDerivAt (fun s => g (s,p.2)) a p.1) :
    second (first f) p = a := by
  rw [←mixed_comm hf]
  apply (first_hasDerivAt ((second_contDiffAt hf).differentiableAt (by simp))).unique
  exact hg.congr_of_eventuallyEq ((continuousAt_id.prodMk continuousAt_const).eventually he)

lemma mixed_equation_eventually {f g G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ ω f p) (he : second f =ᶠ[𝓝 p] g)
    (hg : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => g (s,q.2)) (G q) q.1) :
    second (first f) =ᶠ[𝓝 p] G := by
  filter_upwards [hf.eventually (by simp),he.eventuallyEq_nhds,hg] with q hq heq hgq
  exact mixed_equation hq heq hgq

theorem jets_eventually {u : ℝ × ℝ → ℝ} {p : ℝ × ℝ} {d b : ℝ}
    (hu : ContDiffAt ℝ ω u p)
    (he : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2) :
    (second u =ᶠ[𝓝 p] (fun q => d*u q+b*(u q)^2-q.2)) ∧
    (second (first u) =ᶠ[𝓝 p] (fun q => (d+2*b*u q)*first u q)) ∧
    (second (first (first u)) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first u) q+2*b*(first u q)^2)) ∧
    (second (first (first (first u))) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first (first u)) q+6*b*first u q*first (first u) q)) := by
  have huN : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ ω u q := hu.eventually (by simp)
  have h0 : second u =ᶠ[𝓝 p] (fun q => d*u q+b*(u q)^2-q.2) := by
    filter_upwards [huN,he] with q hq heq
    exact (second_hasDerivAt (hq.differentiableAt (by simp))).unique heq
  have h1 : second (first u) =ᶠ[𝓝 p] (fun q => (d+2*b*u q)*first u q) := by
    apply mixed_equation_eventually hu h0
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    convert! ((hd.const_mul d).add ((hd.pow 2).const_mul b)).sub_const q.2 using 1
    ring
  have h2 : second (first (first u)) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first u) q+2*b*(first u q)^2) := by
    apply mixed_equation_eventually (first_contDiffAt hu) h1
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    have hz := first_hasDerivAt ((first_contDiffAt hq).differentiableAt (by simp))
    convert! (((hd.const_mul (2*b)).const_add d).mul hz) using 1
    ring
  have h3 : second (first (first (first u))) =ᶠ[𝓝 p]
      (fun q => (d+2*b*u q)*first (first (first u)) q+6*b*first u q*first (first u) q) := by
    apply mixed_equation_eventually (first_contDiffAt (first_contDiffAt hu)) h2
    filter_upwards [huN] with q hq
    have hd := first_hasDerivAt (hq.differentiableAt (by simp))
    have hz := first_hasDerivAt ((first_contDiffAt hq).differentiableAt (by simp))
    have ha := first_hasDerivAt ((first_contDiffAt (first_contDiffAt hq)).differentiableAt (by simp))
    convert! ((((hd.const_mul (2*b)).const_add d).mul ha).add
      ((hz.pow 2).const_mul (2*b))) using 1
    ring
  exact ⟨h0,h1,h2,h3⟩

noncomputable def logJet (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := first (first u) q/first u q
noncomputable def schwarzJet (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  first (first (first u)) q/first u q-(3/2)*(logJet u q)^2

theorem invariant_derivatives {u : ℝ × ℝ → ℝ} {m y d b : ℝ}
    (hu : ContDiffAt ℝ ω u (m,y))
    (he : ∀ᶠ q in 𝓝 (m,y), HasDerivAt (fun s => u (q.1,s))
      (d*u q+b*(u q)^2-q.2) q.2)
    (hz : first u (m,y) ≠ 0) :
    HasDerivAt (fun s => logJet u (m,s)) (2*b*first u (m,y)) y ∧
    HasDerivAt (fun s => schwarzJet u (m,s)) 0 y := by
  have hj := jets_eventually hu he
  have hd1 := second_hasDerivAt ((first_contDiffAt hu).differentiableAt (by simp))
  have hd2 := second_hasDerivAt ((first_contDiffAt (first_contDiffAt hu)).differentiableAt (by simp))
  have hd3 := second_hasDerivAt ((first_contDiffAt (first_contDiffAt (first_contDiffAt hu))).differentiableAt (by simp))
  rw [hj.2.1.self_of_nhds] at hd1
  rw [hj.2.2.1.self_of_nhds] at hd2
  rw [hj.2.2.2.self_of_nhds] at hd3
  have hA : HasDerivAt (fun s => logJet u (m,s)) (2*b*first u (m,y)) y := by
    have hd := hd2.div hd1 hz
    have hc : ((d+2*b*u (m,y))*first (first u) (m,y)+2*b*(first u (m,y))^2)*first u (m,y)
        - first (first u) (m,y)*((d+2*b*u (m,y))*first u (m,y)) =
        (2*b*first u (m,y))*(first u (m,y))^2 := by ring
    have hv : (((d+2*b*u (m,y))*first (first u) (m,y)+2*b*(first u (m,y))^2)*first u (m,y)
        - first (first u) (m,y)*((d+2*b*u (m,y))*first u (m,y)))/(first u (m,y))^2 =
        2*b*first u (m,y) := by rw [hc]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hz)
    simpa only [hv, logJet, Pi.div_apply] using! hd
  refine ⟨hA,?_⟩
  have hd := (hd3.div hd1 hz).sub ((hA.pow 2).const_mul (3/2))
  have hc : (((d+2*b*u (m,y))*first (first (first u)) (m,y)+6*b*first u (m,y)*first (first u) (m,y))*
      first u (m,y)-first (first (first u)) (m,y)*((d+2*b*u (m,y))*first u (m,y)))/
      (first u (m,y))^2 - (3/2)*((2:ℝ)*logJet u (m,y)^(2-1)*(2*b*first u (m,y))) = 0 := by
    dsimp [logJet]
    field_simp
    ring
  convert! hd using 1
  simpa only [Nat.cast_ofNat] using hc.symm

end QuinticLienard.RiccatiJets

end OAI
