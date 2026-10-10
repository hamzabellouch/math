import OAI.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates

namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U : Type*}

theorem scaleMvPolynomialAxes_eq_eval₂Hom (T : U → ℝ) (P : MvPolynomial U ℝ) :
    scaleMvPolynomialAxes T P = eval₂Hom C (fun i => C (T i) * X i) P := by
  apply MvPolynomial.funext
  intro u
  rw [scaleMvPolynomialAxes_eval]
  have he : (eval u).comp (eval₂Hom C (fun i => C (T i) * X i)) =
      eval (fun i => T i * u i) := by
    ext <;> simp
  exact (RingHom.congr_fun he P).symm

theorem scaleMvPolynomialAxes_eval_div (T u : U → ℝ)
    (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ) :
    eval (fun i => u i / T i) (scaleMvPolynomialAxes T P) = eval u P := by
  rw [scaleMvPolynomialAxes_eval]
  apply congrArg (fun v => eval v P)
  funext i
  exact mul_div_cancel₀ (u i) (hT i).ne'

theorem realPolynomialMass_scaleMvPolynomialAxes [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ) {d : ℕ}
    (hdegree : P.totalDegree ≤ d) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ α, |P.coeff α| * monomialScale T α ≤ M) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤
      M * ((Fintype.card U : ℝ) + 1) ^ d := by
  have hcard : (P.support.card : ℝ) ≤ ((Fintype.card U : ℝ) + 1) ^ d := by
    exact_mod_cast mvPolynomial_support_card_le_totalDegree P hdegree
  calc
    _ ≤ P.support.card * M := scaleMvPolynomialAxes_mass_le T hT P (fun α =>
      (le_div_iff₀ (monomialScale_pos T hT α)).mpr (hP α))
    _ ≤ ((Fintype.card U : ℝ) + 1) ^ d * M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := mul_comm _ _

theorem realPolynomialMass_scaleMvPolynomialAxes_of_div [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ) {d : ℕ}
    (hdegree : P.totalDegree ≤ d) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ α, |P.coeff α| ≤ M / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤
      M * ((Fintype.card U : ℝ) + 1) ^ d := by
  apply realPolynomialMass_scaleMvPolynomialAxes T hT P hdegree hM
  intro α
  exact (le_div_iff₀ (monomialScale_pos T hT α)).mp (hP α)

namespace NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : U → ℕ)

theorem realSymbolCoordinate_totalDegree_le (hw : ∀ i, 0 < w i)
    (x : F.RealPolynomialSymbol w) (i : ι) {d : ℕ} (hi : ω i ≤ d) :
    (F.realSymbolCoordinate b ω hlayers w x i).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro α hα
  have hwα := F.realSymbolCoordinate_isWeightedHomogeneous b ω hlayers w x i
    (MvPolynomial.mem_support_iff.mp hα)
  calc
    _ ≤ Finsupp.weight w α := by
      simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
      exact Finset.sum_le_sum (fun j _ => Nat.le_mul_of_pos_right _ (hw j))
    _ = ω i := hwα
    _ ≤ d := hi

theorem realSymbolCoordinate_slow_normalized_mass [Fintype U]
    (hw : ∀ i, 0 < w i) (T : U → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolSlowBound b ω hlayers w T M g) (i : ι) {d : ℕ} (hi : ω i ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (F.realSymbolCoordinate b ω hlayers w g.coord i)) ≤
      M * ((Fintype.card U : ℝ) + 1) ^ d := by
  exact realPolynomialMass_scaleMvPolynomialAxes_of_div T hT _
    (F.realSymbolCoordinate_totalDegree_le b ω hlayers w hw g.coord i hi) hM
    (fun α => F.realSymbolCoordinate_slow_coefficients b ω hlayers w T hT hM g hg α i)

end NilpotentLieFiltration
end Erdos3

end

end OAI
