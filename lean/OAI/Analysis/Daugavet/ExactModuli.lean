import OAI.Analysis.Daugavet.EquivalentNorm

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The renorming obstruction is a consequence of the weak-neighborhood geometry, not merely
of the vanishing inherited-norm one-sided modulus. -/
theorem no_equivalent_auc (hinf : ¬ FiniteDimensional ℝ X) (hsp : UnitSliceProperty X)
    (N : Seminorm ℝ X) (hN : EquivalentNorm N) : ¬ AUC N := by
  obtain ⟨R, hRpos, hRball, hRapprox⟩ := equivalentNorm_supremum hinf hN
  obtain ⟨a, b, ha, hb, hab⟩ := hN
  have hN' : EquivalentNorm N := ⟨a, b, ha, hb, hab⟩
  let t := a / (4 * b)
  have ht : 0 < t := by dsimp [t]; positivity
  have hmod : oneSidedModulus N t ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hx, hopt⟩ := hRapprox ε hε
    have hNx : 0 < N x := by have := (hab x).1; rw [hx, mul_one] at this; linarith
    have hxN : N ((N x)⁻¹ • x) = 1 := seminorm_normalize N hNx
    have hD := normD_bound_at_original_unit hsp N ha hb hab hRball hx
    have hopt' : R < N x * (1 + ε) := (div_lt_iff₀ (by linarith)).mp hopt
    have hquot : R / N x - 1 ≤ ε := by
      have : R / N x < 1 + ε := (div_lt_iff₀ hNx).mpr (by nlinarith)
      linarith
    have hinf := csInf_le (normD_centers_bddBelow hinf hN' ht.le)
      ⟨(N x)⁻¹ • x, hxN, rfl⟩
    change oneSidedModulus N t ≤ D N ((N x)⁻¹ • x) t at hinf
    change D N ((N x)⁻¹ • x) t ≤ R / N x - 1 at hD
    simpa only [zero_add] using hinf.trans (hD.trans hquot)
  intro hauc
  exact (hauc t ht).not_ge hmod

theorem exact_main {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ))
    (_hclosed : IsClosed (E : Set (Lp ℝ 1 μ))) (hdim : ¬ FiniteDimensional ℝ E)
    (hprecompact : MeasurePrecompactBall μ E) (hdaugavet : Daugavet E) :
    (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
      H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
      D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
    (∀ t : ℝ, 0 < t →
      averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
      oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
    (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N) := by
  exact ⟨fun x hx t ht => exact_pointwise E hdim hprecompact hdaugavet hx ht,
    fun t ht => exact_center_infima E hdim hprecompact hdaugavet ht,
    no_equivalent_auc hdim (daugavet_unitSlice hdaugavet)⟩

end ExactModuli

end

end OAI
