import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorLogAverage
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPhysicalProjectorIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedProjectors
import OAI.Probability.InvariantIsing.Magnetic.RestrictedOrientationLog

namespace OAI

/-! The geometric cavity lower bound averaged over its physical Haar
disorder.  Full-rank compression and all logarithmic integrability
requirements are supplied by the actual finite model. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_haar_capped_log_increment {N n m d depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (l r : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val<r a)
    (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
      2*cavityCovarianceRate n (2*n+1) N
    (∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2) ∂μ.prod ν) +
      (∫ V, restrictedProjectorLogPartition S hS T c u (q V).1 ∂ν) ≤
    ∫ U, restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) T
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u
      ((cavitySpecialOrthogonal (cavityOrientationLift (by omega : 0<N+n) U))⁻¹) ∂μ := by
  intro A q c δ
  let B := cavityConcreteComplement es B₀
  let p := fun U => cavityPhysicalLabeledProjectors g B a₀ U
  let F := fun U => restrictedProjectorCappedLog S hS C hC T c u t cap δ (A U) (p U) +
    restrictedProjectorLogPartition S hS T c u (p U).1
  let R := fun U : Orthogonal (N+n) =>
    (cavitySpecialOrthogonal (cavityOrientationLift (by omega : 0<N+n) U))⁻¹
  let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t
  let J := fun U => restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) T eig (cavitySpectralGroup g) u (R U)
  have hav := restricted_physical_log_average S hS C hC g k ek e es B₀ a₀ l r hg hln hr μ ν T lam v u hu
    t cap δ hcap
  have hR : Measurable R :=
    (measurable_subtype_coe.subtype_mk.comp
      (measurable_cavityOrientationLift (by omega : 0<N+n))).inv
  have hiJ : Integrable J μ := by
    apply Integrable.of_bound
      ((measurable_restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) T eig (cavitySpectralGroup g) u).comp hR).aestronglyMeasurable
      (1+2*((∑ i, |eig i|)*(N+n)/2)^2+
        8*Real.exp (2*(4*((N+n)*perturbationScale (N+n)^2))))
    exact ae_of_all _ fun U => by
      rw [Real.norm_eq_abs]
      simpa only [Nat.cast_add, Function.comp_apply] using
        restrictedRotationLogMean_bound (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) T eig (cavitySpectralGroup g) u hu (R U)
  have hle : F ≤ᵐ[μ] J := by
    filter_upwards [cavityCompressionGrams_posDef_ae g l r hg hln hr μ] with U hU
    let V := cavityOrientationLift (by omega : 0<N+n) U
    have hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal V) a).PosDef := by
      simpa only [V, cavityOrientationLift_compression] using hU
    have hb := cavityConcreteComplement_gram g es B₀ (cavitySpecialOrthogonal V)
    have hbt := cavityConcreteComplement_perp g es B₀ (cavitySpecialOrthogonal V)
    have hh := restricted_physical_projector_increment hN S hS C hC g k ek e es V lam a₀ B hb hbt hA
      T v hv u hu t cap hcap
    dsimp only at hh
    rw [cavityOrientationLift_compression, cavityOrientationLift_projectors] at hh
    change F U ≤ J U
    exact hh
  have hiF : Integrable F μ := hav.1
  have hm := integral_mono_ae hiF hiJ hle
  rw [hav.2] at hm
  exact hm

end InvariantIsing

end

end OAI
