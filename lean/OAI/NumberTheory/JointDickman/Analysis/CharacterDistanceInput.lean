import OAI.NumberTheory.JointDickman.Amplification.PublishedInputs
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace OAI

/-! # The published Dirichlet-character distance estimate

Only the fixed-modulus consequence of Klurman--Mangerel--Teräväinen,
*Multiplicative functions in short arithmetic progressions*, Proc. London
Math. Soc. 127 (2023), 366--446, Lemma 7.8, is assumed here. That lemma
bounds the infimum over `|t| ≤ 10X` by
`(1/4) log (log X / log (2 conductor χ)) + O(1)`.
For a fixed character the conductor term is absorbed in the constant.
The primes dividing the modulus only add nonnegative terms to our distance.
No modified character, bin label, or short average occurs in this input.
Source: https://doi.org/10.1112/plms.12546, arXiv:1909.12280, Lemma 7.8.
-/
namespace JointDickman
open Classical

noncomputable def characterArithmetic {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else χ (n : ZMod q),by simp⟩

theorem characterArithmetic_prime {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    characterArithmetic χ p = χ (p : ZMod q) := by
  simp only [characterArithmetic,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false]

theorem characterArithmetic_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖characterArithmetic χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa only [characterArithmetic,ArithmeticFunction.coe_mk,hn,ite_false] using χ.norm_le_one (n : ZMod q)

theorem characterArithmetic_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (characterArithmetic χ).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_,?_⟩
  · simp [characterArithmetic]
  · intro m n hm hn _
    simp only [characterArithmetic,ArithmeticFunction.coe_mk,hm,hn,mul_ne_zero hm hn,
      ite_false,Nat.cast_mul,map_mul]

namespace PublishedInputs

def CharacterDistanceInput : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∃ C : ℝ, ∀ X : ℝ, 10 ≤ X → (q : ℝ) ≤ X → ∀ t : ℝ, |t| ≤ X →
      Real.log (Real.log X)/4-C ≤ primeDistanceSquared (characterArithmetic χ) X t

end PublishedInputs
open Filter PublishedInputs
open scoped Topology

def CharacterDistanceDivergence : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ R : ℝ, ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, |t| ≤ X →
      R ≤ primeDistanceSquared (characterArithmetic χ) X t

/-- The quantitative character-distance bound implies qualitative divergence. -/
theorem characterDistanceDivergence_of_published (hKMT : CharacterDistanceInput) :
    CharacterDistanceDivergence := by
  intro q _ χ hχ R
  obtain ⟨C,hC⟩ := hKMT q χ hχ
  have hlog := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (10:ℝ),eventually_ge_atTop (q:ℝ),
    hlog.eventually_ge_atTop (4*(R+C))] with X hX hq hlarge
  intro t ht
  have hh := hC X hX hq t ht
  dsimp only [Function.comp_def] at hlarge
  linarith


end JointDickman

end OAI
