import OAI.Probability.InvariantIsing.Cavity.CavityHaarJointUniform
import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGG
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! Keep the complete finite spectral overlap block in the Haar
approximation, using its canonical compact embedding into real coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def spectralBlockReal {m r : ℕ} (x : SpectralBlock m r) :
    Fin r → Fin r → Fin m → ℝ := fun i j a => x i j a

def spectralBlockClamp {m r : ℕ} (x : Fin r → Fin r → Fin m → ℝ) : SpectralBlock m r :=
  fun i j a => Set.projIcc (-1) 1 (by norm_num) (x i j a)

lemma continuous_spectralBlockReal {m r : ℕ} :
    Continuous (spectralBlockReal (m := m) (r := r)) := by
  unfold spectralBlockReal
  fun_prop

lemma continuous_spectralBlockClamp {m r : ℕ} :
    Continuous (spectralBlockClamp (m := m) (r := r)) := by
  unfold spectralBlockClamp
  fun_prop

@[simp] lemma spectralBlockClamp_real {m r : ℕ} (x : SpectralBlock m r) :
    spectralBlockClamp (spectralBlockReal x) = x := by
  funext i j a
  apply Subtype.ext
  simp only [spectralBlockClamp, spectralBlockReal, Set.coe_projIcc]
  rw [min_eq_right (x i j a).property.2, max_eq_right (x i j a).property.1]

theorem cavityGroupHaarFrame_spectral_uniform {m r q : ℕ}
    (N : ℕ → Fin m → ℕ) (hN : ∀ a, Tendsto (fun k => N k a) atTop atTop)
    (μ : (k : ℕ) → (a : Fin m) → Measure (Orthogonal (N k a)))
    [∀ k a, IsProbabilityMeasure (μ k a)] [∀ k a, (μ k a).IsMulRightInvariant]
    (A₀ : (k : ℕ) → (a : Fin m) → Matrix (Fin (N k a)) (Fin q) ℝ)
    (hA₀ : ∀ k a, (A₀ k a).transpose * A₀ k a = 1)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ)
    (C : ℝ) :
    ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ (v : (a : Fin m) → Fin r → Fin (N k a) → ℝ) (x : SpectralBlock (m + 1) r),
      (∀ a i j, |cavityGroupReplicaGram v a i j| ≤ C) →
      |(∫ U, F (x, cavityGroupMatrixProjection v (cavityGroupHaarFrames (A₀ k) U))
          ∂Measure.pi (μ k)) -
        ∫ y, F (x, y) ∂multivariateGaussian 0
          (cavityGroupReplicaCovariance q (cavityGroupReplicaGram v))| < ε := by
  let G : (Fin r → Fin r → Fin (m + 1) → ℝ) ×
      EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ :=
    F.compContinuous ⟨fun p => (spectralBlockClamp p.1, p.2),
      (continuous_spectralBlockClamp.comp continuous_fst).prodMk continuous_snd⟩
  have hK : IsCompact (Set.range (spectralBlockReal (m := m + 1) (r := r))) :=
    isCompact_range continuous_spectralBlockReal
  intro ε hε
  have hu := cavityGroupHaarFrame_labeled_uniform _ hK N hN μ A₀ hA₀ G C ε hε
  filter_upwards [hu] with k hk
  intro v x hv
  simpa only [G, BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    spectralBlockClamp_real] using hk v (spectralBlockReal x) (Set.mem_range_self x) hv

lemma measurable_cavityGroupHaarFrame_spectral_mean {m r q : ℕ}
    {X : Type*} [MeasurableSpace X] (N : Fin m → ℕ)
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (l : X → SpectralBlock (m + 1) r) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (F : SpectralBlock (m + 1) r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) →ᵇ ℝ) :
    Measurable (fun x => ∫ U, F (l x, cavityGroupMatrixProjection (v x)
      (cavityGroupHaarFrames A₀ U)) ∂Measure.pi μ) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hcont : Continuous (fun p :
      ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) =>
      cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  have hm := F.continuous.measurable.comp
    ((hl.comp measurable_fst).prodMk (hcont.measurable.comp
      ((hv.comp measurable_fst).prodMk ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd))))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI
