import OAI.Analysis.KadisonKastler.RegularCoreMonomials
import OAI.Analysis.KadisonKastler.CoreTraceSymmetry

namespace OAI

/-! # Reduction of corner trace symmetry to regular monomials -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def cornerCompressionLinear (p : H →L[ℂ] H) :
    (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := p * T * p
  map_add' A B := by rw [mul_add, add_mul]
  map_smul' z A := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

theorem coreTraceSymmetry_of_monomials
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M : VonNeumannAlgebra H)
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (C : RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H)
    (ξ : RegularCoreHilbert H)
    (p : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hmono : ∀ a ∈ M, ∀ s : Multiplicative ℝ,
      p * regularCoreMonomial U hU a s * p ∈ coreTraceSymmetrySpace C ξ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M) :
    p * T * p ∈ coreTraceSymmetrySpace C ξ := by
  classical
  let A := StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M)
  let L := cornerCompressionLinear p
  have hsub : A.toSubalgebra.toSubmodule ≤ (coreTraceSymmetrySpace C ξ).comap L := by
    rw [show A = StarAlgebra.adjoin ℂ (regularCoreGenerators U hU M) from rfl,
      regularCore_adjoin_eq_span_monomials U hU M hM]
    apply Submodule.span_le.mpr
    rintro x ⟨a, ha, s, rfl⟩
    exact hmono a ha s
  have ht : T ∈ Set.centralizer (Set.centralizer (A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))) := by
    change T ∈ (generatedVonNeumannAlgebra A :
      Set (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net A T ht
  apply coreTraceSymmetry_of_weak_limit C ξ (l := (atTop : Filter (Finset (RegularCoreHilbert H) × ℕ)))
    (fun i => p * (a i).val * p) (p * T * p)
  · intro i
    exact hsub (a i).property
  · intro x y
    have hv := p.continuous.continuousAt.tendsto.comp (ha (p x))
    have hh := ((continuous_const (y := y)).inner (𝕜 := ℂ) continuous_id).continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, id_eq, mul_apply_eq_comp] using hh

end

end KadisonKastler

end OAI
