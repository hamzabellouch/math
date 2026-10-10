import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Leaf Germ Identity. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.AlignedProductChart
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {A B : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

omit [CompleteSpace A] [CompleteSpace B] in
lemma tangent_curve_snd_derivative (P : AlignedProductChart S A B)
    {h : ℂ → X.Carrier} {z : ℂ}
    (hh : ContMDiffAt 𝓘(ℂ,ℂ) (ModelWithCorners X) ω h z)
    (hy : h z∈P.chart.source)
    (ht : mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z (1 : ℂ)∈S.first (h z)) :
    HasFDerivAt (fun t => (P.chart (h t)).2) (0 : ℂ →L[ℂ] B) z := by
  have hp := P.holomorphicAt hy
  have ha := (hp.comp z hh).contDiffAt.analyticAt.differentiableAt
  have hc := mfderiv_comp z (hp.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hc
  have hd : fderiv ℂ (fun t => (P.chart (h t)).2) z=0 := by
    change fderiv ℂ (fun x => ((P.chart ∘ h) x).2) z=0
    rw [fderiv.snd ha,hc]
    apply ContinuousLinearMap.ext
    intro w
    have hw : mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z w∈S.first (h z) := by
      have he : w=w • (1 : ℂ) := by simp
      erw [he,map_smul]
      exact (S.first (h z)).smul_mem w ht
    have hm : mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (h z)
        (mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z w) ∈
        Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,A × B) P.chart (h z)).toLinearMap (S.first (h z)) :=
      ⟨_,hw,rfl⟩
    rw [P.first _ hy] at hm
    exact hm
  rw [←hd]
  exact ha.snd.hasFDerivAt

omit [CompleteSpace A] [CompleteSpace B] in
theorem tangent_curve_snd_eventually (P : AlignedProductChart S A B)
    {h : ℂ → X.Carrier} {z₀ : ℂ}
    (hh : ContMDiff 𝓘(ℂ,ℂ) (ModelWithCorners X) ω h)
    (hy : h z₀∈P.chart.source)
    (ht : ∀z,mfderiv 𝓘(ℂ,ℂ) (ModelWithCorners X) h z (1 : ℂ)∈S.first (h z)) :
    ∀ᶠ z in 𝓝 z₀,(P.chart (h z)).2=(P.chart (h z₀)).2 := by
  have hnh := (hh z₀).continuousAt.preimage_mem_nhds (P.chart.open_source.mem_nhds hy)
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hnh
  have hD : ∀z∈Metric.ball z₀ r,
      HasFDerivAt (fun t => (P.chart (h t)).2) (0 : ℂ →L[ℂ] B) z :=
    fun z hz => P.tangent_curve_snd_derivative (hh z) (hs hz) (ht z)
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball z₀ r).isPreconnected
    (fun z hz => (hD z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z hz).fderiv) hz (Metric.mem_ball_self hr)

 

theorem germ_zero_of_all_jets (P : AlignedProductChart S A B) (L : LeafJetAtlas S)
    {f : X.Carrier → ℂ} {y : X.Carrier} (hy : y∈P.chart.source)
    (hf : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω f y)
    (hz : ∀m,L.jet f y m=0) :
    (fun a => f (P.chart.symm (a,(P.chart y).2))) =ᶠ[𝓝 (P.chart y).1] 0 := by
  apply HorizontalJet.eventually_zero_of_all_zero (P.coordinate_function_analytic hy hf)
  intro m
  apply (P.jet_eq_zero_iff f hy m).mp
  rw [P.jet_independent (L.chart y) hy (L.mem_source y) hf m (fun n hn => hz n)]
  exact hz m

end SplitTangent.AlignedProductChart

end

end OAI
