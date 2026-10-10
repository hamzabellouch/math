import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapLinearStability

namespace OAI

/-! A compact parameter family sharing a fixed jet has one common
neighborhood of quantitative injectivity. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma compact_fixed_value_neighborhood {E F : Type*} [TopologicalSpace E]
    [PseudoMetricSpace F] {K : Set ℝ} (hK : IsCompact K)
    {f : ℝ × E → F} (hf : Continuous f) (p : E) (v : F)
    (hfix : ∀ t ∈ K, f (t,p) = v) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ ∀ t ∈ K, ∀ x ∈ U, dist (f (t,x)) v < ε := by
  let O : Set (ℝ × E) := f ⁻¹' ball v ε
  have hO : IsOpen O := isOpen_ball.preimage hf
  have hsub : K ×ˢ {p} ⊆ O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have he : x = p := hx
    subst x
    change f (t,p) ∈ ball v ε
    simpa [hfix t ht] using hε
  obtain ⟨V,U,hV,hU,hKV,hpU,hVU⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  refine ⟨U,hU,hpU (by simp),?_⟩
  intro t ht x hx
  exact hVU ⟨hKV ht,hx⟩

theorem compact_fixed_jet_injectivity {K : Set ℝ} (hK : IsCompact K)
    (F : ℝ → (Base × ℝ) → ProjectionTarget 3)
    (hF : ∀ t ∈ K, ContDiff ℝ ∞ (F t))
    (hD : Continuous (fun z : ℝ × (Base × ℝ) => fderiv ℝ (F z.1) z.2))
    (p : Base × ℝ) (L : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3)
    (hfix : ∀ t ∈ K, fderiv ℝ (F t) p = L.toContinuousLinearMap) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, (ball p r).InjOn (F t) := by
  let c := (2*(‖L.symm.toContinuousLinearMap‖+1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1 := by
    dsimp [c]
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [norm_nonneg L.symm.toContinuousLinearMap]
  obtain ⟨U,hU,hpU,hnear⟩ := compact_fixed_value_neighborhood hK hD p
    L.toContinuousLinearMap hfix hc
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU p hpU
  refine ⟨r,hr,?_⟩
  intro t ht
  apply near_equiv_derivative_injOn L (fun x _ => (hF t ht).differentiable (by simp) x)
    (convex_ball p r) hc.le hsmall
  intro x hx
  exact (show ‖fderiv ℝ (F t) x-L.toContinuousLinearMap‖ < c from by
    simpa only [dist_eq_norm] using hnear t ht x (hrU hx)).le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
