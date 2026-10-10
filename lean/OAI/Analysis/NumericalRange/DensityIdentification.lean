import OAI.Analysis.NumericalRange.TestingAlgebra

namespace OAI

universe u_251 u_252

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_251} {m : Type u_252} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
lemma resolvent_density_testing (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y)
    (ij : m × m) (k : ℤ) :
    tensorTesting X Y (∫ t : UnitAddCircle, D.resolventField A t ⊗ₖ matrixFourierTrace ij k t
      ∂AddCircle.haarAddCircle) = (a/b:ℝ)*
      inner ℂ (densityField (μ := AddCircle.haarAddCircle) L X Y)
        (D.cauchy (hsTraceLp (matrixFourierTrace ij k))) := by
  obtain ⟨v,hv,hc,he⟩ := D.fourier_cauchy ij k
  rw [hc]
  unfold hsTraceLp
  rw [densityField_testing L hL,← hrep v hv,← D.fourier_resolvent_eval A hA ij k he]
  exact tensorTesting_similarity hS hu ha hb hX hY A v
lemma resolvent_density_identification (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    {S : Matrix n n ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (L : C(UnitAddCircle,Matrix n n ℂ)) (hL : ∀ t, (L t).IsHermitian)
    (hrep : ∀ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, L t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle)
    {X Y : Matrix n m ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hX : S*X = (a:ℂ) • X) (hY : S*Y = (b:ℂ) • Y) :
    densityField (μ := AddCircle.haarAddCircle)
      (hermitianField ⟨D.resolventField A,D.resolvent_continuous A hA⟩) X Y =
      ((a/b:ℝ):ℂ) • D.cauchy.adjoint (densityField L X Y) +
      ((b/a:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star (densityField L X Y))) := by
  apply density_adjoint_identification
  intro ij k
  rw [densityField_testing_sum]
  simp only [ContinuousMap.coe_mk]
  rw [D.resolvent_density_testing A hA hS hu L hL hrep ha hb hX hY ij k]
  simp_rw [matrixFourierTrace_star]
  rw [D.resolvent_density_testing A hA hS hu L hL hrep hb ha hY hX ij.swap (-k)]
  rw [densityField_star L hL,hsTrace_matrixFourier_star]
  simp only [map_mul,Complex.conj_ofReal]
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
