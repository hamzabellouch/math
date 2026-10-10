import OAI.NumberTheory.CubicMoment.Estimates.NormSeries
import OAI.NumberTheory.CubicGram.LatticePoisson

namespace OAI

/-!
# The published additive large-sieve input over the Eisenstein integers

M. N. Huxley, *The large sieve inequality for algebraic number fields*,
Mathematika 15 (1968), 178–187. The precise imaginary-quadratic form used
here is displayed in P. Gao and L. Zhao, *The large sieve with power moduli
in imaginary quadratic number fields*, IJNT 18 (2022), 1713–1733,
arXiv:2101.00811v2, equation (1.2).

This is an explicit hypothesis type. The primitive multiplicative
character inequality is to be derived by finite Gauss expansion and
orthogonality; it is not assumed here.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Gao–Zhao's additive character `e_K(nh/q)`, with `sqrt(D_K)=traceLambda`. -/
def huxleyPhase (q h n : Eisenstein) : ℂ :=
  let z : ℂ := (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ))
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(z+star z))

def additiveSievePolynomial (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    (q h : Eisenstein) : ℂ :=
  ∑ n ∈ N, v n*huxleyPhase q h n

def huxleyModulusMass (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : ℝ :=
  ∑' h : Residues q, if IsUnit h then
    ‖additiveSievePolynomial N v q (residueRepresentative q h)‖^2 else 0

def huxleySieveMass (Q Z : ℝ) (v : Eisenstein → ℂ) : ℝ :=
  ∑ q ∈ nonzeroNormBall Q, huxleyModulusMass q (nonzeroNormBall Z) v

lemma huxleyModulusMass_nonneg (q : Eisenstein) (N : Finset Eisenstein)
    (v : Eisenstein → ℂ) : 0 ≤ huxleyModulusMass q N v := by
  apply tsum_nonneg
  intro h
  split_ifs <;> positivity

/-- Exact `Q²+Z` input, with neither a conductor power loss nor an
invented multiplicative-character estimate hidden in the hypothesis. -/
def HuxleyAdditiveLargeSieve : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q Z : ℝ, 1 ≤ Q → 1 ≤ Z →
    ∀ v : Eisenstein → ℂ,
      huxleySieveMass Q Z v ≤ C*(Q^2+Z)*∑ n ∈ nonzeroNormBall Z, ‖v n‖^2

lemma norm_huxleyPhase (q h n : Eisenstein) : ‖huxleyPhase q h n‖ = 1 := by
  unfold huxleyPhase
  rw [Complex.norm_exp]
  generalize (n:ℂ)*(h:ℂ)/(traceLambda*(q:ℂ)) = z
  simp [Complex.mul_re,Complex.mul_im]

end CubicFirstMoment

end

end OAI
