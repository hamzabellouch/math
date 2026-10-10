import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # Finite mesh representation of the atomic background on a radial window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem AxialBackground.integral_cell_eq_sum {K α γ μ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (x : JetPrototype.Space) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂AxialBackground.cell K α γ μ t x.2) =
      ∑ a : Bool, (1/4)*JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x := by
  rw [AxialBackground.integral_cell hK hα hγ hμ ht]
  simp only [Fintype.sum_bool,JetPrototype.sign,Bool.false_eq_true,ite_false,ite_true]
  unfold AxialBackground.weight JetCoreDensity.limitingCoefficient
  ring

theorem GeometricBackground.integral_finite_window {θ η l K α γ t δ R : ℝ}
    (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η) (hη : 0 < η) (hδ : 0 < δ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (x : JetPrototype.Space) (hlo : δ ≤ ‖x.1‖) (hhi : ‖x.1‖ ≤ R) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂background θ η l K α γ t x) =
      ∑ a : Bool, ∑ k ∈ Finset.Icc (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η),
        if l < GeometricMesh.point θ η k then
          JetCoreDensity.limitingCoefficient K α γ (GeometricMesh.point θ η k) t
            (JetPrototype.sign a) ψ x*
              ((JetGeometry.scaleShell η (GeometricMesh.point θ η k)).indicator
                (fun _ => (1:ℝ)) x.1*(1/4)) else 0 := by
  classical
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  by_cases ha : active θ η l x.1
  · let j := GeometricMesh.index (‖x.1‖/θ) η
    have hs : scale θ η x.1 = GeometricMesh.point θ η j := rfl
    have hy : x.1 ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η j) := by
      simpa only [hs] using ha.2
    have hl : l < GeometricMesh.point θ η j := by simpa only [hs] using ha.1
    have hj := GeometricMesh.shell_index_window hθ₁ hθ₂ hη hδ hy hlo hhi
    rw [background_on_shell hθ hη hy hl,AxialBackground.integral_cell_eq_sum
      hK hα hγ (GeometricMesh.point_pos hθ η j) ht]
    apply Finset.sum_congr rfl
    intro a _
    symm
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left hl,indicator_of_mem hy]
      ring
    · intro k _ hkj
      have hn : x.1 ∉ JetGeometry.scaleShell η (GeometricMesh.point θ η k) := by
        intro hk
        exact hkj (GeometricMesh.shell_index hθ hη hk).symm
      simp only [indicator_of_notMem hn,zero_mul,mul_zero,ite_self]
    · intro hj'
      exact (hj' (Finset.mem_Icc.mpr hj)).elim
  · rw [background,ite_eq_right ha,integral_zero_measure]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hl : l < GeometricMesh.point θ η k
    · have hn : x.1 ∉ JetGeometry.scaleShell η (GeometricMesh.point θ η k) := by
        intro hk
        apply ha
        rw [active,scale_eq_of_shell hθ hη hk]
        exact ⟨hl,hk⟩
      simp only [hl,ite_true,indicator_of_notMem hn,zero_mul,mul_zero]
    · simp only [hl,ite_false]

end BoltzmannNonuniqueness

end

end

section

/-! # Finite sums of weak L1 limits -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.finset_sum {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) {f : ι → ℕ → X → ℝ} {g : ι → X → ℝ}
    (h : ∀ i ∈ s, WeakL1Converges μ (f i) (g i))
    (hf : ∀ i ∈ s, ∀ n, Integrable (f i n) μ) :
    WeakL1Converges μ (fun n x => ∑ i ∈ s, f i n x) (fun x => ∑ i ∈ s, g i x) := by
  refine ⟨Finset.measurable_sum s (fun i hi => (h i hi).1),
    integrable_finsetSum s (fun i hi => (h i hi).2.1),?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have heq (u : ι → X → ℝ) (hu : ∀ i ∈ s, Integrable (u i) μ) :
      (∫ x, ψ x*(∑ i ∈ s, u i x) ∂μ) = ∑ i ∈ s, ∫ x, ψ x*u i x ∂μ := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum s (fun i hi =>
      (hu i hi).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
  have ht := tendsto_finsetSum s (fun i hi => (h i hi).2.2 ψ hψ ⟨C,hC⟩)
  simp_rw [heq (fun i => f i _) (fun i hi => hf i hi _),
    heq g (fun i hi => (h i hi).2.1)]
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A finite limiting horizon keeps the attained and original scales comparable -/
noncomputable section
open Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.radius_horizon_ratio (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hfinite : E.horizon < ⊤) :
    0 < E.horizon.toReal⁻¹ ∧ E.horizon.toReal⁻¹ ≤ 1 ∧
      Tendsto (fun n => S.radius (E.indices n)/shrinkingHorizon F.horizonScale (E.indices n))
        atTop (𝓝 E.horizon.toReal⁻¹) := by
  have hge : 1 ≤ E.horizon.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hfinite.ne E.horizon_ge
  have hpos : 0 < E.horizon.toReal := lt_of_lt_of_le zero_lt_one hge
  have ht := (ENNReal.tendsto_toReal hfinite.ne).comp E.horizon_limit
  change Tendsto (fun n => (S.normalizedHorizon (E.indices n)).toReal) atTop
    (𝓝 E.horizon.toReal) at ht
  have he (n) : (S.normalizedHorizon (E.indices n)).toReal =
      shrinkingHorizon F.horizonScale (E.indices n)/S.radius (E.indices n) :=
    ENNReal.toReal_ofReal (div_nonneg
      (shrinkingHorizon_pos F.horizonScale_pos _).le (S.radius_pos hs₀ _).le)
  simp_rw [he] at ht
  refine ⟨inv_pos.mpr hpos,(inv_le_one₀ hpos).mpr hge,?_⟩
  simpa only [inv_div] using ht.inv₀ hpos.ne'

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
