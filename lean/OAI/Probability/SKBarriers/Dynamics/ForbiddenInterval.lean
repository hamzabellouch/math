import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairGibbsGap
import OAI.Probability.SKBarriers.Parisi.CDFMinimizer
import OAI.Probability.SKBarriers.Coverage.FiniteCoverageMixing

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem exists_forbidden_interval {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    {l u : ℝ} (hl : 0≤l) (hu : u≤1) (h : ¬∀x∈Ioo l u,f x=x) :
    ∃a₀ a₁ d : ℝ,l<a₀ ∧ a₀<a₁ ∧ a₁<u ∧ 0<d ∧ ∀x∈Icc a₀ a₁,d≤|x-f x| := by
  push Not at h
  obtain ⟨z,hz,hfZ⟩ := h
  have hz0 : 0<z := hl.trans_lt hz.1
  have hz1 : z<1 := hz.2.trans_le hu
  have hc : ContinuousAt (fun x => |x-f x|) z :=
    (continuousAt_id.sub ((hf z ⟨hz0.le,hz1.le⟩).continuousAt (Icc_mem_nhds hz0 hz1))).abs
  have hd : 0 < |z-f z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hfZ))
  have hznhds : ∀ᶠ x in 𝓝 z,x∈Ioo l u := Ioo_mem_nhds hz.1 hz.2
  have hh : ∀ᶠ x in 𝓝 z,x∈Ioo l u ∧ |z-f z|/2≤|x-f x| :=
    hznhds.and (Filter.Tendsto.eventually_const_le (half_lt_self hd) hc)
  obtain ⟨r,hr,hrball⟩ := Metric.mem_nhds_iff.mp hh
  let a₀ := z-r/2
  let a₁ := z+r/2
  have hleft : a₀∈Metric.ball z r := by
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp only [a₀]
    rw [sub_sub_cancel_left,abs_neg,abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hright : a₁∈Metric.ball z r := by
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp only [a₁]
    rw [add_sub_cancel_left,abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  refine ⟨a₀,a₁,|z-f z|/2,(hrball hleft).1.1,?_,(hrball hright).1.2,half_pos hd,?_⟩
  · dsimp only [a₀,a₁]; linarith only [hr]
  · intro x hx
    apply (hrball ?_).2
    rw [Metric.mem_ball,Real.dist_eq]
    have H : |x-z|≤r/2 := abs_le.mpr (by dsimp only [a₀,a₁] at hx; constructor <;> linarith only [hx.1,hx.2])
    exact H.trans_lt (half_lt_self hr)

 theorem pairStrip_annealed_bound {β : ℝ} (hβ : 0<β)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {a₀ a₁ d : ℝ} (ha₀ : 0≤a₀) (hd : 0<d)
    (hgap : ∀x∈Icc a₀ a₁,d≤|x-scalarCDFOverlap β (cdf (μ : Measure ℝ)) x|) :
    ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (pairStripSet n a₀ a₁) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  have H := eventual_pairMismatch_polynomial_bound (A:=d) (a:=0) (t:=(4:ℝ)/5) (ε:=1)
    hβ hd le_rfl (by norm_num) (by norm_num) zero_lt_one
    (cdf (μ : Measure ℝ)) (fun x => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (supported_probability_cdf_one μ hμ) hmin
  simp only [neg_zero,Real.rpow_zero,mul_one,one_mul] at H
  filter_upwards [H] with n hn
  refine (integral_mono (replicaGibbsMass_integrable β _) (replicaGibbsMass_integrable β _)
    (fun J => replicaGibbsMass_mono β J ?_)).trans hn
  intro s hs
  have hh := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha₀.trans hh.1,hgap _ hh⟩

end SK.Analytic

end
end

end OAI
