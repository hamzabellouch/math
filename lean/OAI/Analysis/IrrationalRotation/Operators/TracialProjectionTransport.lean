import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Analysis.ClosedRangeTransport
import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransport

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal

namespace Invariant233.TracialProjectionTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem vectorTrace_projection (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    vectorTrace ξ p.starProjection = (‖p.starProjection ξ‖ ^ 2 : ℂ) := by
  unfold vectorTrace
  calc
    inner ℂ ξ (p.starProjection ξ) =
        inner ℂ (p.starProjection ξ) (p.starProjection ξ) := by
      rw [Submodule.inner_starProjection_left_eq_right]
      rw [Submodule.starProjection_eq_self_iff.mpr (p.starProjection_apply_mem ξ)]
    _ = _ := inner_self_eq_norm_sq_to_K _

theorem vectorTrace_projection_re (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    (vectorTrace ξ p.starProjection).re = ‖p.starProjection ξ‖ ^ 2 := by
  rw [vectorTrace_projection]
  norm_cast

theorem vectorTrace_projection_nonneg (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    0 ≤ (vectorTrace ξ p.starProjection).re := by
  rw [vectorTrace_projection_re]
  positivity

theorem vectorTrace_projection_mono (ξ : H) {p q : Submodule ℂ H}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (hpq : p ≤ q) :
    (vectorTrace ξ p.starProjection).re ≤ (vectorTrace ξ q.starProjection).re := by
  rw [vectorTrace_projection_re, vectorTrace_projection_re]
  have hnorm := p.norm_starProjection_apply_le (q.starProjection ξ)
  have heq := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le hpq) ξ
  change p.starProjection (q.starProjection ξ) = p.starProjection ξ at heq
  rw [heq] at hnorm
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem vectorTrace_projection_orthogonal (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    vectorTrace ξ pᗮ.starProjection = (‖ξ‖ ^ 2 : ℂ) - vectorTrace ξ p.starProjection := by
  unfold vectorTrace
  rw [Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right]
  rw [inner_self_eq_norm_sq_to_K]
  rfl

theorem tendsto_vectorTrace {ι : Type*} {l : Filter ι}
    (ξ : H) (A : ι → H →L[ℂ] H) (B : H →L[ℂ] H)
    (h : Tendsto (fun n => A n ξ) l (𝓝 (B ξ))) :
    Tendsto (fun n => vectorTrace ξ (A n)) l (𝓝 (vectorTrace ξ B)) := by
  exact tendsto_const_nhds.inner h

theorem vectorTrace_le_of_cutoff_estimates
    (ξ : H) (p q : Submodule ℂ H)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (E : ℕ → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hE : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hbound : ∀ n, (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ q.starProjection).re) :
    (vectorTrace ξ p.starProjection).re ≤ (vectorTrace ξ q.starProjection).re := by
  have ht : Tendsto (fun n => inner ℂ ξ ((E n).starProjection ξ))
      atTop (𝓝 (inner ℂ ξ ξ)) := tendsto_const_nhds.inner hE
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  have he : Tendsto (fun n => (vectorTrace ξ (E n).starProjection).re)
      atTop (𝓝 (‖ξ‖ ^ 2)) := by
    have hnorm : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
    rw [hnorm] at hr
    exact hr
  have hlim : Tendsto (fun n => (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2) atTop
      (𝓝 ((vectorTrace ξ p.starProjection).re + ‖ξ‖ ^ 2 - ‖ξ‖ ^ 2)) :=
    (tendsto_const_nhds.add he).sub_const (‖ξ‖ ^ 2)
  have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa only [add_sub_cancel_right] using hle

theorem vectorTrace_eq_of_cutoff_estimates
    (ξ : H) (p q : Submodule ℂ H)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (E : ℕ → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hE : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hforward : ∀ n, (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ q.starProjection).re)
    (hbackward : ∀ n, (vectorTrace ξ pᗮ.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ qᗮ.starProjection).re) :
    vectorTrace ξ p.starProjection = vectorTrace ξ q.starProjection := by
  have hle := vectorTrace_le_of_cutoff_estimates ξ p q E hE hforward
  have hge := vectorTrace_le_of_cutoff_estimates ξ pᗮ qᗮ E hE hbackward
  rw [vectorTrace_projection_orthogonal, vectorTrace_projection_orthogonal] at hge
  have hre : (vectorTrace ξ p.starProjection).re =
      (vectorTrace ξ q.starProjection).re := by
    simp only [Complex.sub_re] at hge
    linarith
  rw [vectorTrace_projection_re, vectorTrace_projection_re] at hre
  rw [vectorTrace_projection, vectorTrace_projection]
  exact_mod_cast hre

theorem vectorTrace_closedRange_eq
    [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (p : Submodule ℂ H) [CompleteSpace p]
    (f : p →L[ℂ] H) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M)
    (hf : InvariantRotation.ClosedRangeTransport.forward p f ∈ M) :
    letI : IsClosed (f.range : Set H) := hc
    vectorTrace ξ p.starProjection = vectorTrace ξ f.range.starProjection := by
  exact InvariantRotation.ClosedRangeTransport.trace_range_eq M p f hinj hc hp hf
    (vectorTrace ξ) (fun a ha b hb => hξ.2.1 a b ha hb)


variable [CompleteSpace H]

def cutoffMap (T : H →ₗ.[ℂ] H) (r : Submodule ℂ H) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖) : r →L[ℂ] H :=
  (T.toFun.comp (Submodule.inclusion hrD)).mkContinuous K hupper

omit [CompleteSpace H] in

theorem cutoffMap_range_le_transported
    (T : H →ₗ.[ℂ] H) (p r : Submodule ℂ H) (hrp : r ≤ p) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖) :
    (cutoffMap T r hrD K hupper).range ≤
      InvariantRotation.AffiliatedTransport.transported T p := by
  rintro y ⟨x, rfl⟩
  apply (InvariantRotation.AffiliatedTransport.domainImage T p).le_topologicalClosure
  apply InvariantRotation.AffiliatedTransport.mem_domainImage.mpr
  exact ⟨⟨x, hrD x.property⟩, hrp x.property, rfl⟩

theorem cutoff_trace_le_transported
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (p r : Submodule ℂ H) [CompleteSpace r]
    (hrp : r ≤ p) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖)
    (L : ℝ≥0) (hlower : ∀ x : r, ‖x‖ ≤ L * ‖T ⟨x, hrD x.property⟩‖)
    (hr : r.starProjection ∈ M)
    (hf : InvariantRotation.ClosedRangeTransport.forward r
      (cutoffMap T r hrD K hupper) ∈ M) :
    (vectorTrace ξ r.starProjection).re ≤
      (vectorTrace ξ (InvariantRotation.AffiliatedTransport.transported T p).starProjection).re := by
  let f := cutoffMap T r hrD K hupper
  have hbounds := InvariantRotation.ClosedRangeTransport.injective_closedRange_of_bound
    r f L hlower
  let : IsClosed (f.range : Set H) := hbounds.2
  have htrace := vectorTrace_closedRange_eq M ξ hξ r f hbounds.1 hbounds.2 hr hf
  apply (congrArg Complex.re htrace).trans_le
  exact vectorTrace_projection_mono ξ
    (cutoffMap_range_le_transported T p r hrp hrD K hupper)


end Invariant233.TracialProjectionTransport

end

end OAI
