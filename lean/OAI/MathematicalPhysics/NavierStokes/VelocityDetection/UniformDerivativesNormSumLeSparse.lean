import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem norm_sum_le_sparse {ι V : Type*} [NormedAddCommGroup V]
    (s : Finset ι) (v : ι → V) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i ∈ s, ‖v i‖ ≤ C)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i ∈ s, v i‖ ≤ C := by
  classical
  by_cases h : ∃ i ∈ s, v i ≠ 0
  · obtain ⟨i, hi, hvi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hv i hi
    · intro j hj hji
      exact (hd i hi j hj hji.symm).resolve_left hvi
    · exact fun h => (h hi).elim
  · have hz : ∀ i ∈ s, v i = 0 := by simpa using h
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact hC

end VelocityDetection.UniformDerivatives
end

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem jet_zero_before {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) {a : ℝ}
    (hz : ∀ t ≤ a, ∀ X, f (t, X) = 0) (n : ℕ) {t : ℝ} (ht : t ≤ a) (X : E) :
    iteratedFDeriv ℝ n f (t, X) = 0 := by
  have heq : EqOn (fun t => iteratedFDeriv ℝ n f (t, X)) (fun _ => 0) (Iio a) := by
    intro s hs
    have hev : f =ᶠ[𝓝 (s, X)] 0 := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hs] with q hq
      exact hz q.1 hq.le q.2
    simpa using (hev.iteratedFDeriv ℝ n).eq_of_nhds
  have hcont : Continuous (fun t => iteratedFDeriv ℝ n f (t, X)) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  exact heq.closure hcont continuous_const (by simpa only [closure_Iio, mem_Iic] using ht)

theorem jet_zero_after {f : ℝ × E → F} (hf : ContDiff ℝ ∞ f) {a : ℝ}
    (hz : ∀ t, a ≤ t → ∀ X, f (t, X) = 0) (n : ℕ) {t : ℝ} (ht : a ≤ t) (X : E) :
    iteratedFDeriv ℝ n f (t, X) = 0 := by
  have heq : EqOn (fun t => iteratedFDeriv ℝ n f (t, X)) (fun _ => 0) (Ioi a) := by
    intro s hs
    have hev : f =ᶠ[𝓝 (s, X)] 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hs] with q hq
      exact hz q.1 hq.le q.2
    simpa using (hev.iteratedFDeriv ℝ n).eq_of_nhds
  have hcont : Continuous (fun t => iteratedFDeriv ℝ n f (t, X)) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  exact heq.closure hcont continuous_const (by simpa only [closure_Ioi, mem_Ici] using ht)

end VelocityDetection.UniformDerivatives
end

end OAI
