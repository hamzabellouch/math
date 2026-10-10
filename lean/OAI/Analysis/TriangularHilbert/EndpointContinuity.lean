import OAI.Analysis.TriangularHilbert.CyclicSlice

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma continuousAt_threshold (u v : ℝ) (hu : u ≠ v) :
    ContinuousAt (fun r : ℝ => if r < v then (1:ℝ) else 0) u := by
  rcases lt_or_gt_of_ne hu with h|h
  · have he : ∀ᶠ r in 𝓝 u, r < v := eventually_lt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [hr,ite_true]
  · have he : ∀ᶠ r in 𝓝 u, v < r := eventually_gt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [not_lt.mpr hr.le,ite_false]

lemma continuousAt_hardKernel_endpoints (r R t : ℝ) (hr : r ≠ |t|) (hR : R ≠ |t|) :
    ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 t) (r,R) := by
  have h1 : ContinuousAt (fun p : ℝ×ℝ => if p.1 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold r |t| hr).comp (continuousAt_fst (p := (r,R)))
  have h2 : ContinuousAt (fun p : ℝ×ℝ => if p.2 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold R |t| hR).comp (continuousAt_snd (p := (r,R)))
  exact (h1.sub h2).div_const t

lemma ae_continuousAt_hardKernel_endpoints (r R a : ℝ) :
    ∀ᵐ c : ℝ, ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 (a+c)) (r,R) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h1 h2 h3 h4
  apply continuousAt_hardKernel_endpoints
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h3; linarith
    · apply h4; linarith

lemma continuousAt_cyclicHard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ContinuousAt (fun p : ℝ×ℝ => cyclicKernelOutput B C (hardKernel p.1 p.2) z) (r,R) := by
  let s := Set.Icc (-(R+1+|z.1+z.2|)) (R+1+|z.1+z.2|)
  let L := 1/(r/2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let D (c : ℝ) := ‖B (z.2,c)‖^3
  let E (c : ℝ) := ‖C (c,z.1)‖^3
  have hdom : Integrable (s.indicator (fun c => (D c+E c+2)*L)) :=
    IntegrableOn.integrable_indicator
      (((hz.2.2.1.integrableOn.add hz.2.2.2.integrableOn).add
        (integrableOn_const (C := (2:ℝ)) isCompact_Icc.measure_ne_top)).mul_const L) measurableSet_Icc
  have hnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 ∧ p.1 < p.2 ∧ p.2 < R+1 := by
    have h1 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 :=
      (continuous_fst.tendsto (r,R)) (eventually_gt_nhds (show r/2 < r by linarith))
    have h2 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), 0 < p.2-p.1 :=
      ((continuous_snd.sub continuous_fst).tendsto (r,R)) (eventually_gt_nhds (show 0 < R-r by linarith))
    have h3 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), p.2 < R+1 :=
      (continuous_snd.tendsto (r,R)) (eventually_lt_nhds (show R < R+1 by linarith))
    filter_upwards [h1,h2,h3] with p hp1 hp2 hp3
    exact ⟨hp1,by linarith,hp3⟩

  apply tendsto_integral_filter_of_dominated_convergence (s.indicator (fun c => (D c+E c+2)*L))
  · exact Eventually.of_forall (fun p => (hz.1.mul hz.2.1).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)).aestronglyMeasurable)))
  · filter_upwards [hnear] with p hp
    filter_upwards [] with c
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc]
      exact norm_product_kernel_le (fun c => B (z.2,c)) (fun c => C (c,z.1))
        (fun c => hardKernel p.1 p.2 (z.1+z.2+c)) (D := D) (E := E) hL (c := c) le_rfl le_rfl
        ((abs_hardKernel_le (by linarith [hp.1]) hp.2.1.le _).trans
          (one_div_le_one_div_of_le (by positivity) hp.1.le))
    · have he : hardKernel p.1 p.2 (z.1+z.2+c) = 0 := by
        apply hardKernel_shift_support hp.2.1.le
        intro hh
        apply hc
        exact ⟨by linarith [hh.1,hp.2.2],by linarith [hh.2,hp.2.2]⟩
      simp only [he,Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc,le_refl]
  · exact hdom
  · filter_upwards [ae_continuousAt_hardKernel_endpoints r R (z.1+z.2)] with c hc
    exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hc.tendsto)
end
end TriangularHilbert.Heat
end

end OAI
