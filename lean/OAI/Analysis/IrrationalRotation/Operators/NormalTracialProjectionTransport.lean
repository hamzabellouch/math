import OAI.Analysis.IrrationalRotation.Operators.VectorTraceNormality
import OAI.Analysis.IrrationalRotation.Operators.VectorProjectionNormality
import OAI.Analysis.IrrationalRotation.Operators.AffiliatedTransportSupplement

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233

namespace TracialState
variable {A : Type*} [CStarAlgebra A]

theorem apply_selfAdjoint_eq_re (τ : TracialState A) {a : A}
    (ha : IsSelfAdjoint a) : τ a = ((τ a).re : ℂ) := by
  apply (Complex.conj_eq_iff_re.mp ?_).symm
  change star (τ a) = τ a
  rw [← τ.map_star, ha.star_eq]

theorem projection_nonneg (τ : TracialState A) {p : A}
    (hp : IsStarProjection p) : 0 ≤ (τ p).re := by
  have h := τ.positive p
  rwa [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] at h

theorem projection_mono (τ : TracialState A) {p q : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = p) :
    (τ p).re ≤ (τ q).re := by
  have h := τ.projection_nonneg (hp.sub_of_mul_eq_left hq hpq)
  change 0 ≤ (τ.toContinuousLinearMap (q - p)).re at h
  rw [map_sub, Complex.sub_re] at h
  linarith

theorem projection_re_mem_Icc (τ : TracialState A) {p : A}
    (hp : IsStarProjection p) : (τ p).re ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨τ.projection_nonneg hp, ?_⟩
  have h := τ.projection_mono hp (IsStarProjection.one A) (mul_one p)
  simpa only [τ.map_one, Complex.one_re] using h

end TracialState

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace NormalTracialProjectionTransport

theorem tendsto_trace_projection_exhaustion
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    {ι : Type} [Preorder ι] [NeBot (atTop : Filter ι)]
    (K : ι → Submodule ℂ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : Monotone K) (hmem : ∀ i, (K i).starProjection ∈ M)
    (hdense : (⨆ i, K i).topologicalClosure = ⊤) :
    Tendsto (fun i => τ ⟨(K i).starProjection, hmem i⟩) atTop (𝓝 1) := by
  have h := hτ.tendsto_of_strong_small atTop
    (fun i => ⟨(K i).starProjection, hmem i⟩) 1
    ⟨1, fun i => (K i).starProjection_norm_le⟩ (fun x => ?_)
  · simpa only [τ.map_one] using h
  · simpa only [OneMemClass.coe_one, one_apply_eq_self] using
      Submodule.starProjection_tendsto_self K hK x (by rw [hdense])

theorem tendsto_trace_projection_exhaustion_re
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    {ι : Type} [Preorder ι] [NeBot (atTop : Filter ι)]
    (K : ι → Submodule ℂ H) [∀ i, (K i).HasOrthogonalProjection]
    (hK : Monotone K) (hmem : ∀ i, (K i).starProjection ∈ M)
    (hdense : (⨆ i, K i).topologicalClosure = ⊤) :
    Tendsto (fun i => (τ ⟨(K i).starProjection, hmem i⟩).re) atTop (𝓝 1) := by
  simpa only [Function.comp_def, Complex.one_re] using
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_trace_projection_exhaustion M τ hτ K hK hmem hdense)

theorem trace_eq_of_cutoff_estimates
    (M : VonNeumannAlgebra H) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (K : ℕ → Submodule ℂ H) [∀ n, (K n).HasOrthogonalProjection]
    (hK : Monotone K) (hmem : ∀ n, (K n).starProjection ∈ M)
    (hdense : (⨆ n, K n).topologicalClosure = ⊤)
    (hforward : ∀ n, (τ p).re + (τ ⟨(K n).starProjection, hmem n⟩).re - 1 ≤
      (τ q).re)
    (hbackward : ∀ n, (τ (1 - p)).re +
      (τ ⟨(K n).starProjection, hmem n⟩).re - 1 ≤ (τ (1 - q)).re) :
    τ p = τ q := by
  have he : Tendsto (fun n : ℕ => (τ ⟨(K n).starProjection, hmem n⟩).re)
      atTop (𝓝 1) :=
    tendsto_trace_projection_exhaustion_re M τ hτ (ι := ℕ) K hK hmem hdense
  have hbackward' : ∀ n, (1 - (τ p).re) +
      (τ ⟨(K n).starProjection, hmem n⟩).re - 1 ≤ 1 - (τ q).re := by
    intro n
    have h := hbackward n
    change (τ.toContinuousLinearMap (1 - p)).re + _ - 1 ≤
      (τ.toContinuousLinearMap (1 - q)).re at h
    simpa only [map_sub, Complex.sub_re, τ.map_one, Complex.one_re] using h
  have hre := Invariant233.AffiliatedTransport.trace_eq_of_cutoff_estimates
    he hforward hbackward'
  rw [τ.apply_selfAdjoint_eq_re hp.isSelfAdjoint,
    τ.apply_selfAdjoint_eq_re hq.isSelfAdjoint, hre]

end NormalTracialProjectionTransport
end Invariant233

end

end OAI
