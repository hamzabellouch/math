import Mathlib
import OAI.Analysis.BiholderTransport.Duality.GeometricEnvelope

namespace OAI



noncomputable section
open Set Filter Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [Nonempty M] in
lemma scalar_normal_remainder {v : M → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    {φ : ℝ → ℝ} {x : M} {l : ℝ} (hφ : HasDerivAt φ l (v x)) :
    (fun h : TangentSpace 𝓘(ℝ,Model n) x =>
      φ (v (riemannianExp x h))-φ (v x)-l*(v (riemannianExp x h)-v x))
      =o[𝓝 0] (fun h => ‖h‖) := by
  have ht : Tendsto (fun h : TangentSpace 𝓘(ℝ,Model n) x => v (riemannianExp x h))
      (𝓝 0) (𝓝 (v x)) := by
    simpa only [Function.comp_def,riemannianExp_zero] using (hv.continuous.comp (continuous_riemannianExp (n := n) x)).continuousAt.tendsto (x := 0)
  have hO : (fun h : TangentSpace 𝓘(ℝ,Model n) x => v (riemannianExp x h)-v x)
      =O[𝓝 0] (fun h => ‖h‖) := by
    apply IsBigO.of_bound (L:ℝ)
    filter_upwards [] with h
    have H := hv.dist_le_mul (riemannianExp x h) x
    have H1 := mul_le_mul_of_nonneg_left (dist_riemannianExp_le x h) L.coe_nonneg
    rw [dist_comm x] at H1
    simpa only [Real.dist_eq,Real.norm_eq_abs,abs_norm] using H.trans H1
  simpa only [Function.comp_def,smul_eq_mul,mul_comm] using
    (hφ.isLittleO.comp_tendsto ht).trans_isBigO hO

omit [Nonempty M] in
lemma scalar_normalSubdifferential_inv {v : M → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) {φ : ℝ → ℝ} {x : M} {l : ℝ}
    (hφ : HasDerivAt φ l (v x)) (hl : 0<l)
    {r : TangentSpace 𝓘(ℝ,Model n) x}
    (hr : r∈normalSubdifferential (fun y => φ (v y)) x) :
    l⁻¹ • r∈normalSubdifferential v x := by
  intro ε hε
  have hres := scalar_normal_remainder (n := n) hv hφ
  filter_upwards [hr (l*ε/2) (by positivity),hres.bound (by positivity : 0<l*ε/2)] with h hh hR
  simp only [Real.norm_eq_abs,abs_norm] at hR
  have hR' := (abs_le.mp hR).2
  have H : inner ℝ r h-l*ε*‖h‖≤l*(v (riemannianExp x h)-v x) := by
    linarith only [hh,hR']
  have HI := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hl.le)
  simpa only [real_inner_smul_left,mul_sub,←mul_assoc,inv_mul_cancel₀ hl.ne',
    one_mul] using HI

lemma WeakMTW.modified_short_contact (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} {y : M} {l τ : ℝ}
    (hφ : HasDerivAt φ l (v y)) (hl : 0<l) (hl1 : l<1) (hτ : τ≠0)
    {r : TangentSpace 𝓘(ℝ,Model n) y} (hr : τ • r∈injectivityDomain y)
    (hmin : IsLocalMin (fun a => φ (v a)+cost a (riemannianExp y (τ • r))/τ) y) :
    l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (riemannianExp y (l⁻¹ • r))=0 ∧ r∈injectivityDomain y := by
  have hsub := scalar_normalSubdifferential_inv hv hφ hl
    (local_min_divided_cost_subgradient hτ hr hmin)
  have H := hmtw.subgradient_dual_contact hv.continuous hu ⟨hdual.2,hdual.1⟩ hsub
  refine ⟨H.1,H.2,?_⟩
  have HI := contracted_minimizer_mem_injectivityDomain H.1 hl hl1
  simpa only [smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using HI

end WeakMTWTransport

end

end OAI
