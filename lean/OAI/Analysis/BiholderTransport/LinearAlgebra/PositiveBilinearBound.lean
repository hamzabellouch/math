import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.StrictDividedAction
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactCrossing

namespace OAI

section
section
noncomputable section
open Set Metric

namespace WeakMTWTransport
section PositiveBilinearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_bilinear_positive_baseline (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E,v≠0 → 0 < B v v) :
    ∃ m>0,∀ v : E,m*‖v‖^2≤B v v := by
  let S := sphere (0:E) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hc : ContinuousOn (fun v:E => B v v) S :=
    (B.continuous.clm_apply continuous_id).continuousOn
  obtain ⟨m,hm,Hm⟩ : ∃ m>0,∀ v∈S,m≤B v v := by
    by_cases hne : S.Nonempty
    · obtain ⟨v,hv,Hv⟩ := hS.exists_isMinOn hne hc
      have hn : ‖v‖=1 := by simpa only [S,mem_sphere,dist_zero_right] using hv
      have hp : 0 < B v v := hB v (by intro he; simp [he] at hn)
      exact ⟨B v v,hp,fun w hw => Hv hw⟩
    · exact ⟨1,zero_lt_one,fun v hv => (hne ⟨v,hv⟩).elim⟩
  exact ⟨m,hm,bilinear_lower_of_unit B (fun v hv => Hm v (by simpa only [S,mem_sphere,dist_zero_right] using hv))⟩

end PositiveBilinearBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section DividedBaseline
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma divided_hessian_decrease {a : M} {r ξ : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s<1) :
    hessianValue a (s • r) ξ/s ≤ hessianValue a (t • r) ξ/t := by
  rcases eq_or_lt_of_le hts with h | h
  · simp only [h,le_refl]
  by_cases hξ : ξ=0
  · subst ξ
    rw [hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr (ht.trans h) hs),
      hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hr ht (h.trans hs))]
    simp only [map_zero,zero_div,le_refl]
  exact (divided_hessian_strict_decrease hr ht h hs hξ).le

lemma exists_divided_hessian_baseline {a : M} {r : TangentSpace 𝓘(ℝ,Model n) a}
    (hr : r∈minimizingVectors a) {t s0 : ℝ} (ht : 0 < t) (hts : t<s0) (hs0 : s0<1) :
    ∃ m>0,∀ s : ℝ,s0 ≤ s → s<1 → ∀ ξ : TangentSpace 𝓘(ℝ,Model n) a,
      m*‖ξ‖^2 ≤ hessianValue a (t • r) ξ/t-hessianValue a (s • r) ξ/s := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) a) := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := t⁻¹ • normalHessian a (t • r)-s0⁻¹ • normalHessian a (s0 • r)
  have hIDt := contracted_minimizer_mem_injectivityDomain hr ht (hts.trans hs0)
  have hIDs := contracted_minimizer_mem_injectivityDomain hr (ht.trans hts) hs0
  have hB (ξ : TangentSpace 𝓘(ℝ,Model n) a) : B ξ ξ=
      hessianValue a (t • r) ξ/t-hessianValue a (s0 • r) ξ/s0 := by
    rw [hessianValue_eq_normalHessian hIDt,hessianValue_eq_normalHessian hIDs]
    simp only [B,sub_apply,smul_apply,smul_eq_mul]
    ring
  obtain ⟨m,hm,Hm⟩ := exists_bilinear_positive_baseline B (fun ξ hξ => by
    rw [hB]
    exact sub_pos.mpr (divided_hessian_strict_decrease hr ht hts hs0 hξ))
  refine ⟨m,hm,?_⟩
  intro s hss hs1 ξ
  have H := Hm ξ
  rw [hB] at H
  have Hd := divided_hessian_decrease (ξ := ξ) hr (ht.trans hts) hss hs1
  linarith only [H,Hd]

end DividedBaseline
end WeakMTWTransport

end

end

end

end OAI
