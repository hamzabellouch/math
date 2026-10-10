import OAI.Analysis.KadisonKastler.RescaledTomitaGraph
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # Closability of the concrete Tomita graph

A separating vector is cyclic for the commutant. The commutant matrix
coefficients then show that the closed graph has no vertical vector.
This is the first operator-theoretic step toward modular spectral resolution.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Commutant coefficients identify the second graph coordinate on the dense
algebraic graph and, by continuity, on its closure. -/
theorem rescaledGraph_commutant_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (b : Algebra M.commutant) (ξ : TomitaGraphHilbert H)
    (hξ : ξ ∈ rescaledGraphSubspace M J Ω c) :
    inner ℂ (J (b.val Ω)) (ξ 1) = (c : ℂ) * inner ℂ (star b.val Ω) (ξ 0) := by
  have h0 : Continuous (fun v : TomitaGraphHilbert H => v 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => H) 0
  have h1 : Continuous (fun v : TomitaGraphHilbert H => v 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => H) 1
  have hc : IsClosed {v : TomitaGraphHilbert H |
      inner ℂ (J (b.val Ω)) (v 1) = (c : ℂ) * inner ℂ (star b.val Ω) (v 0)} :=
    isClosed_eq (continuous_const.inner h1) (continuous_const.mul (continuous_const.inner h0))
  apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω c)) ?_ hc hξ
  rintro _ ⟨a, rfl⟩
  change inner ℂ (J (b.val Ω)) ((c : ℂ) • J (star a.val Ω)) =
    (c : ℂ) * inner ℂ (star b.val Ω) (a.val Ω)
  rw [inner_smul_right, conjugateIsometry_inner]
  change (c : ℂ) * (starRingEnd ℂ) (inner ℂ (b.val Ω) (star a.val Ω)) = _
  rw [inner_conj_symm]
  congr 1
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp b.property a.val a.property
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ Ω (T Ω)) hcomm

/-- The closure of the graph is single-valued whenever the vector separates
M. No modular conjugation or spectral theorem is assumed. -/
theorem rescaledGraph_no_vertical (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (ξ : TomitaGraphHilbert H) (hξ : ξ ∈ rescaledGraphSubspace M J Ω c)
    (hzero : ξ 0 = 0) : ξ = 0 := by
  have hdense := Generator.commutant_orbit_dense M Ω (fun a ha => by
    apply hsep
    exact ha)
  have hcoeff (b : Algebra M.commutant) : inner ℂ (J (b.val Ω)) (ξ 1) = 0 := by
    have h := rescaledGraph_commutant_coefficient J Ω c b ξ hξ
    simpa only [hzero, inner_zero_right, mul_zero] using h
  have hclosed : IsClosed {v : H | inner ℂ (J v) (ξ 1) = 0} :=
    isClosed_eq (J.continuous.inner continuous_const) continuous_const
  have hsub : Set.range (fun b : Algebra M.commutant => b.val Ω) ⊆
      {v : H | inner ℂ (J v) (ξ 1) = 0} := by
    rintro _ ⟨b, rfl⟩
    exact hcoeff b
  have hz := closure_minimal hsub hclosed (hdense (J.symm (ξ 1)))
  change inner ℂ (J (J.symm (ξ 1))) (ξ 1) = 0 at hz
  have hz' : ξ 1 = 0 := inner_self_eq_zero.mp (by
    simpa only [J.apply_symm_apply] using hz)
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hzero
  · exact hz'

/-- Projection onto the first coordinate is injective on the closed graph. -/
theorem rescaledGraph_first_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c : ℝ)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective (fun ξ : rescaledGraphSubspace M J Ω c => ξ.val 0) := by
  intro ξ η he
  have hz := rescaledGraph_no_vertical J Ω c hsep (ξ.val - η.val)
    ((rescaledGraphSubspace M J Ω c).sub_mem ξ.property η.property)
    (by simpa only [PiLp.sub_apply] using sub_eq_zero.mpr he)
  exact Subtype.ext (sub_eq_zero.mp hz)

end

end KadisonKastler

end OAI
