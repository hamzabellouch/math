import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! The relative half-plane proper-arc consequence of the published
Jordan--Schönflies theorem.  Reference: C. Thomassen, *The Jordan-Schönflies
Theorem and the Classification of Surfaces*, Amer. Math. Monthly 99 (1992),
116--130, Theorem 3.1, p. 123, DOI 10.1080/00029890.1992.11995820.

The consequence used here is obtained by compactifying at infinity and
applying the extension theorem to the two Jordan curves consisting of the
proper arc and each real half-axis; the two extensions agree on their common
arc and glue.  The real boundary is prescribed pointwise.  We parameterize
this precise topological input explicitly.  It contains no SLE, ribbon,
Brownian probability, harmonic measure or angle estimate. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

def PublishedHalfPlaneCrosscutStraightening : Prop :=
  ∀ β : ℝ≥0 → ℂ, Continuous β → Function.Injective β → β 0 = 0 →
    (∀ t : ℝ≥0, 0 < t → β t ∈ upperHalfPlane) →
    Tendsto β atTop (cocompact ℂ) →
    ∃ h : ℂ ≃ₜ ℂ, (∀ x : ℝ, h (x : ℂ) = (x : ℂ)) ∧
      MapsTo h upperHalfPlane upperHalfPlane ∧
      ∀ t : ℝ≥0, h (β t) = (t : ℂ) * Complex.I

namespace CrosscutSides

/-- Straightening identifies the entire interior zero set, including
nonlocal pieces of the original access guide. -/
theorem straightened_real_zero_iff
    (β : ℝ≥0 → ℂ) (h : ℂ ≃ₜ ℂ)
    (hH : MapsTo h upperHalfPlane upperHalfPlane)
    (hβ : ∀ t : ℝ≥0, h (β t) = (t : ℂ) * Complex.I)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    (h z).re = 0 ↔ ∃ t : ℝ≥0, 0 < t ∧ β t = z := by
  constructor
  · intro hre
    have him : 0 < (h z).im := hH hz
    let t : ℝ≥0 := ⟨(h z).im, him.le⟩
    refine ⟨t, by exact_mod_cast him, h.injective ?_⟩
    rw [hβ]
    have ht : (t : ℂ) = ((h z).im : ℂ) := by norm_cast
    rw [ht]
    apply Complex.ext <;> simp [hre]
  · rintro ⟨t, _, rfl⟩
    rw [hβ]
    simp

theorem straightening_preserves_real_exit_limit
    {ι : Type*} {l : Filter ι} (h : ℂ ≃ₜ ℂ)
    (hreal : ∀ x : ℝ, h (x : ℂ) = (x : ℂ))
    (f : ι → ℂ) (x : ℝ) (hf : Tendsto f l (𝓝 (x : ℂ))) :
    Tendsto (fun i => (h (f i)).re) l (𝓝 x) := by
  simpa only [Function.comp_def, hreal, Complex.ofReal_re] using
    (Complex.continuous_re.continuousAt.comp h.continuous.continuousAt).tendsto.comp hf

end CrosscutSides
end SLEExactGauge

end

end OAI
