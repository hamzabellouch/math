import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
namespace Release061

def realComplexBlock (k : ℕ) : ((Fin k → ℝ) × (Fin k → ℝ)) ≃L[ℝ] (Fin k → ℂ) where
  toFun p i := (p.1 i : ℂ)+Complex.I*(p.2 i : ℂ)
  invFun z := (fun i => (z i).re,fun i => (z i).im)
  left_inv p := by ext i <;> simp
  right_inv z := by funext i; apply Complex.ext <;> simp
  map_add' p q := by ext i; simp; ring
  map_smul' r p := by ext i; simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma hasFDerivAt_realComplexBlock {k : ℕ} {D : (Fin k → ℝ) → Fin k → ℝ}
    (J : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ))
    (hD : HasFDerivAt D (J : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0) :
    HasFDerivAt (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      fun i => (p.1 i : ℂ)+Complex.I*(D p.2 i : ℂ))
      (((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr J).trans
        (realComplexBlock k)).toContinuousLinearMap 0 := by
  have hp := ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) (Fin k → ℝ)).hasFDerivAt (x := 0)).prodMk
    (hD.comp 0 (ContinuousLinearMap.snd ℝ (Fin k → ℝ) (Fin k → ℝ)).hasFDerivAt)
  exact (realComplexBlock k).hasFDerivAt.comp 0 hp

open scoped Topology
open Set Filter Metric

lemma uniformly_of_vanishing_error {ι E F : Type*} [PseudoMetricSpace F]
    {K : Set E} {f g : ι → E → F} {ψ : E → F} {l : Filter ι}
    (hf : TendstoUniformlyOn f ψ l K) {a : ι → ℝ} (ha : Tendsto a l (𝓝 0))
    (he : ∀ᶠ t in l, ∀ x ∈ K, dist (f t x) (g t x) ≤ a t) :
    TendstoUniformlyOn g ψ l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [he,(Metric.tendstoUniformlyOn_iff.mp hf) (ε/2) (half_pos hε),
    (tendsto_order.mp ha).2 (ε/2) (half_pos hε)] with t ht hf ha
  intro x hx
  exact (dist_triangle _ _ _).trans_lt (by linarith [ht x hx,hf x hx])

theorem choose_positive_C1_regularization
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {Ω : Set F} {R : ℝ → ℝ → E → F} {ψ : E → F}
    {a : ℝ} (ha : 0 < a)
    (hv : TendstoUniformlyOn (fun t => R t 0) ψ (𝓝[Ioi 0] 0) K)
    (hd : TendstoUniformlyOn (fun t => fderiv ℝ (R t 0)) (fderiv ℝ ψ) (𝓝[Ioi 0] 0) K)
    (hδv : ∀ t ∈ Ioo 0 a, TendstoUniformlyOn (R t) (R t 0) (𝓝[Ioi 0] 0) K)
    (hδd : ∀ t ∈ Ioo 0 a, TendstoUniformlyOn (fun δ => fderiv ℝ (R t δ))
      (fderiv ℝ (R t 0)) (𝓝[Ioi 0] 0) K)
    (hδi : ∀ t ∈ Ioo 0 a, ∀ᶠ δ in 𝓝[Ioi 0] 0,
      ∀ x ∈ K, t • R t δ x ∈ Ω ∧ DifferentiableAt ℝ (R t δ) x) :
    ∃ δ : ℝ → ℝ,
      (∀ t ∈ Ioo 0 a, 0 < δ t ∧ δ t < t ∧ ∀ x ∈ K,
        t • R t (δ t) x ∈ Ω ∧ DifferentiableAt ℝ (R t (δ t)) x) ∧
      TendstoUniformlyOn (fun t => R t (δ t)) ψ (𝓝[Ioi 0] 0) K ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (R t (δ t))) (fderiv ℝ ψ) (𝓝[Ioi 0] 0) K := by
  have hex (t : ℝ) (ht : t ∈ Ioo 0 a) : ∃ δ : ℝ, 0 < δ ∧ δ < t ∧
      (∀ x ∈ K, t • R t δ x ∈ Ω ∧ DifferentiableAt ℝ (R t δ) x) ∧
      (∀ x ∈ K, dist (R t 0 x) (R t δ x) < t) ∧
      (∀ x ∈ K, dist (fderiv ℝ (R t 0) x) (fderiv ℝ (R t δ) x) < t) := by
    have hb : ∀ᶠ δ in 𝓝[Ioi 0] 0, 0 < δ ∧ δ < t := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds] with δ hδ hdt
      exact ⟨hδ,hdt⟩
    have he := hb.and ((hδi t ht).and
      (((Metric.tendstoUniformlyOn_iff.mp (hδv t ht)) t ht.1).and
        ((Metric.tendstoUniformlyOn_iff.mp (hδd t ht)) t ht.1)))
    obtain ⟨δ,hδ,hi,hv,hd⟩ := he.exists
    exact ⟨δ,hδ.1,hδ.2,hi,hv,hd⟩
  let δ : ℝ → ℝ := fun t => if ht : t ∈ Ioo 0 a then (hex t ht).choose else 0
  have hs (t : ℝ) (ht : t ∈ Ioo 0 a) : 0 < δ t ∧ δ t < t ∧
      (∀ x ∈ K, t • R t (δ t) x ∈ Ω ∧ DifferentiableAt ℝ (R t (δ t)) x) ∧
      (∀ x ∈ K, dist (R t 0 x) (R t (δ t) x) < t) ∧
      (∀ x ∈ K, dist (fderiv ℝ (R t 0) x) (fderiv ℝ (R t (δ t)) x) < t) := by
    simpa only [δ,dite_eq_left ht] using (hex t ht).choose_spec
  have hsmall : ∀ᶠ t in 𝓝[Ioi 0] 0, t ∈ Ioo 0 a := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
    exact ⟨ht,hta⟩
  refine ⟨δ,fun t ht => ⟨(hs t ht).1,(hs t ht).2.1,(hs t ht).2.2.1⟩,?_,?_⟩
  · apply uniformly_of_vanishing_error hv (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [hsmall] with t ht
    intro x hx
    exact ((hs t ht).2.2.2.1 x hx).le
  · apply uniformly_of_vanishing_error hd (tendsto_id.mono_left nhdsWithin_le_nhds)
    filter_upwards [hsmall] with t ht
    intro x hx
    exact ((hs t ht).2.2.2.2 x hx).le

end Release061

end

end OAI
