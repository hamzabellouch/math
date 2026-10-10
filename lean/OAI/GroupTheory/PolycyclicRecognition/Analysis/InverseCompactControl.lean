import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseSection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiberIncrementBound

namespace OAI

/-! # Compact regions in the inverse coupling

A compact family of evaluation points yields common compact averaging and
increment regions. Integrals on an inverse-chart strip are bounded by a
fixed Haar mass times the original section integral.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace PolycyclicRecognition

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] {Λ : ℝ≥0}

omit [IsIsometricSMul G G] in
/-- Uniform compact regions for the centers, their translated averaging
regions, and the resulting difference parameters. -/
theorem exists_inverse_compact_regions {Q B : Set G} (hQ : IsCompact Q) (hB : IsCompact B) :
    ∃ C T : Set G, IsCompact C ∧ IsCompact T ∧
      (∀ y ∈ Q, ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C) ∧
      (∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T) := by
  let Q₁ : Set G := (fun q : NormalizedPair G Λ × G => q.1.val.1 q.2) '' (univ ×ˢ Q)
  have hQ₁ : IsCompact Q₁ := (isCompact_univ.prod hQ).image (by fun_prop)
  refine ⟨Q₁ * B, B⁻¹ * (Q₁ * B), hQ₁.mul hB, hB.inv.mul (hQ₁.mul hB), ?_, ?_⟩
  · intro y hy p x hx
    apply Set.mul_mem_mul
    · exact ⟨(p, y), ⟨mem_univ p, hy⟩, rfl⟩
    · exact hx
  · intro x₂ hx₂ x₁ hx₁
    exact Set.mul_mem_mul (Set.inv_mem_inv.mpr hx₂) hx₁

/-- The first-coordinate projection of a compact strip in inverse
coordinates. Its Haar mass is the constant in the local error bound. -/
def inverseStripBase (B : Set G) : Set G :=
  Prod.fst '' (pairChartTransition.symm '' (univ ×ˢ B : Set (NormalizedPair G Λ × G)))

theorem inverseStripBase_compact {B : Set G} (hB : IsCompact B) :
    IsCompact (inverseStripBase (Λ := Λ) B) :=
  (((isCompact_univ.prod hB).image pairChartTransition.symm.continuous).image continuous_fst)

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

/-- Product coordinates bound every inverse-strip integral by the Haar mass
of one compact base projection times its section integral. -/
theorem inverse_strip_lintegral_le
    (m : Measure G) [SFinite m]
    (μ ν : Measure (NormalizedPair G Λ)) [SFinite μ] [SFinite ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (B : Set G) (f : NormalizedPair G Λ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, ∫⁻ x in B, f (pairChartTransition.symm (p, x)).2 ∂m ∂ν) ≤
      m (inverseStripBase (Λ := Λ) B) * ∫⁻ p, f p ∂μ := by
  let e : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) := pairChartTransition
  have he : MeasurePreserving e.symm (ν.prod m) (m.prod μ) := by
    rw [← hprod]
    exact MeasurableEquiv.measurePreserving_symm (m.prod μ) e.toMeasurableEquiv
  have hmeas : Measurable (fun q : NormalizedPair G Λ × G => f (e.symm q).2) :=
    hf.comp (measurable_snd.comp e.symm.continuous.measurable)
  calc
    _ = ∫⁻ q in (univ ×ˢ B : Set (NormalizedPair G Λ × G)), f (e.symm q).2 ∂(ν.prod m) := by
      rw [setLIntegral_prod _ hmeas.aemeasurable, Measure.restrict_univ]
    _ = ∫⁻ q in e.symm '' (univ ×ˢ B : Set (NormalizedPair G Λ × G)), f q.2 ∂(m.prod μ) :=
      he.setLIntegral_comp_emb e.symm.measurableEmbedding (fun q => f q.2) _
    _ ≤ ∫⁻ q in (inverseStripBase (Λ := Λ) B) ×ˢ univ, f q.2 ∂(m.prod μ) := by
      apply lintegral_mono_set
      intro q hq
      exact ⟨⟨q, hq, rfl⟩, mem_univ _⟩
    _ = _ := by
      rw [setLIntegral_prod (fun q : G × NormalizedPair G Λ => f q.2) (hf.comp measurable_snd).aemeasurable,
        Measure.restrict_univ]
      dsimp only [Prod.snd]
      rw [setLIntegral_const, mul_comm]

end PolycyclicRecognition

end

end OAI
