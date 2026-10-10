import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Conditional strong stability for injective represented algebras

The hypothesis `ChristensenMutual` is the mutual near-inclusion
consequence of Cameron–Christensen–Sinclair–Smith–White–Wiggins,
*Kadison–Kastler stable factors*, Duke Math. J. 163 (2014), Theorem 3.3(i),
building on Christensen, *Near inclusions of C*-algebras* (1980).
The stability theorem is conditional on this near-inclusion property.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Injectivity in the given representation, expressed as a contractive linear
projection of the ambient bounded operators onto the algebra. Normality of the
projection is not required. -/
def IsInjective (M : VonNeumannAlgebra H) : Prop :=
  ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
    ‖E‖ ≤ 1 ∧ (∀ x, E x ∈ M) ∧ ∀ x ∈ M, E x = x

/-- The strict near-inclusion convention of the published input. Approximants
belong to the algebra, but need not lie in its unit ball. -/
def NearInclusion (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∃ γ' : ℝ, γ' < γ ∧ ∀ x ∈ unitBall M,
    Metric.infDist x (N : Set (H →L[ℂ] H)) ≤ γ'

theorem nearInclusion_of_kkDistance_lt {M N : VonNeumannAlgebra H} {γ : ℝ}
    (h : kkDistance M N < γ) : NearInclusion M N γ := by
  obtain ⟨γ', hdist, hγ'⟩ := exists_between h
  refine ⟨γ', hγ', ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_unitBall_approx hx hdist
  exact (Metric.infDist_le_dist_of_mem hy.1).trans
    (le_of_lt (by simpa only [dist_eq_norm] using hxy))

/-- Precise published input: the mutual case of CCSSWW (2014), Theorem 3.3(i).
The location of the unitary in `(M ∪ N)''` is omitted because this application
does not use it. The equality conclusion applies for `γ < 1/101`. -/
def ChristensenMutual : Prop :=
  ∀ (M N : VonNeumannAlgebra H) (γ : ℝ), IsInjective M →
    NearInclusion M N γ → NearInclusion N M γ → γ < 1 / 101 →
    ∃ v : unitary (H →L[ℂ] H),
      Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ ≤ 150 * γ

/-- The concrete tolerance used in conditional injective-class stability.
It depends only on the requested displacement, not on the represented
algebras or on their Hilbert space. -/
theorem injective_nearConjugacy_of_kkDistance_lt
    (hChristensen : ChristensenMutual (H := H)) {ε : ℝ} (hε : 0 < ε)
    {M N : VonNeumannAlgebra H} (hM : IsInjective M)
    (hdist : kkDistance M N < min (1 / 202) (ε / 300)) :
    NearConjugacy M N ε := by
  have hsmall : min (1 / 202) (ε / 300) < 1 / 101 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hreverse : kkDistance N M < min (1 / 202) (ε / 300) := by
    rwa [kkDistance_comm]
  obtain ⟨v, hv, hnorm⟩ := hChristensen M N (min (1 / 202) (ε / 300)) hM
    (nearInclusion_of_kkDistance_lt hdist)
    (nearInclusion_of_kkDistance_lt hreverse) hsmall
  refine ⟨v, hv, hnorm.trans_lt ?_⟩
  have hδε : min (1 / 202) (ε / 300) ≤ ε / 300 := min_le_right _ _
  linarith

/-- Conditional injective strong stability in a fixed representation. -/
theorem injective_strong_stability (hChristensen : ChristensenMutual (H := H))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M N : VonNeumannAlgebra H,
      IsInjective M → kkDistance M N < δ → NearConjugacy M N ε := by
  refine ⟨min (1 / 202) (ε / 300), lt_min (by norm_num) (by positivity), ?_⟩
  intro M N hM hdist
  exact injective_nearConjugacy_of_kkDistance_lt hChristensen hε hM hdist

/-- Conditional strong stability uniformly over the injective class and all
Hilbert-space representations. The tolerance is chosen before the Hilbert space. -/
theorem universal_injective_strong_stability
    (hChristensen : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ChristensenMutual (H := H)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ∀ M N : VonNeumannAlgebra H,
          IsInjective M → kkDistance M N < δ → NearConjugacy M N ε := by
  intro ε hε
  refine ⟨min (1 / 202) (ε / 300), lt_min (by norm_num) (by positivity), ?_⟩
  intro H _ _ _ M N hM hdist
  exact injective_nearConjugacy_of_kkDistance_lt (hChristensen H) hε hM hdist

end KadisonKastler

end OAI
