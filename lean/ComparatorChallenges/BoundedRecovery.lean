import Mathlib

namespace OAI

/-! Nondegenerate spectral calculus, the closed Tomita graph, and bounded recovery. -/

universe u

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spectralCharacter (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => Complex.exp (((t * u : ℝ) : ℂ) * Complex.I))
    (by fun_prop) 1 (by intro u; simp [Complex.norm_exp])

def halfExponentialCutoff (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u : ℝ => (Real.exp (min (n : ℝ) u / 2) : ℂ))
    (by fun_prop) (Real.exp ((n : ℝ) / 2)) (by
      intro u
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

structure RealSpectralCalculus (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  calculus : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)
  nondegenerate : Dense {h : H | ∃ f : BoundedContinuousFunction ℝ ℂ,
    HasCompactSupport (f : ℝ → ℂ) ∧ ∃ k : H, calculus f k = h}

namespace RealSpectralCalculus

def unitary (D : RealSpectralCalculus H) (t : ℝ) : H →L[ℂ] H :=
  D.calculus (spectralCharacter t)

def halfGraph (D : RealSpectralCalculus H) : Set (H × H) :=
  {p | Tendsto (fun n : ℕ => D.calculus (halfExponentialCutoff n) p.1) atTop (𝓝 p.2)}

def HasSpectralSupport (D : RealSpectralCalculus H) (I : Set ℝ) (h : H) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℂ, (∀ u ∈ I, f u = 0) → D.calculus f h = 0

end RealSpectralCalculus

structure StandardModularData (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  M : VonNeumannAlgebra H
  xi : H
  norm_xi : ‖xi‖ = 1
  cyclic : Dense {h : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ a xi = h}
  separating : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0
  D : RealSpectralCalculus H
  J : H ≃ₗᵢ⋆[ℂ] H
  conjugation : Function.Involutive J
  tomita_graph : closure {p : H × H | ∃ a : H →L[ℂ] H,
      a ∈ M ∧ p = (a xi, (star a) xi)} =
    {p | ∃ q : H, (p.1, q) ∈ D.halfGraph ∧ p.2 = J q}

namespace StandardModularData

def sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  S.D.unitary t * a * S.D.unitary (-t)

def ScalarCentralizer (S : StandardModularData H) : Prop :=
  ∀ a : H →L[ℂ] H, a ∈ S.M → (∀ t : ℝ, S.sigma t a = a) →
    ∃ c : ℂ, a = c • (1 : H →L[ℂ] H)

end StandardModularData

def symmetricAverage (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ))⁻¹ * ∫ t in -(k : ℝ)..(k : ℝ), f t

def fixedMean (omega : Ultrafilter ℕ) (f : ℝ → ℝ) : ℝ :=
  Filter.limUnder (omega : Filter ℕ) (symmetricAverage f)

def RecoveryConclusion (S : StandardModularData H) (T : H →L[ℂ] H)
    (s : ℝ) (delta : ℕ → ℝ) : Prop :=
  ∃ (nj : ℕ → ℕ) (_ : StrictMono nj) (v : ℕ → (H →L[ℂ] H)) (C eta : ℝ),
    0 < eta ∧ ∀ j : ℕ, v j ∈ S.M ∧ ‖v j‖ ≤ C ∧ eta ≤ ‖T (v j S.xi)‖ ∧
      S.D.HasSpectralSupport (Icc (s - 4 * delta (nj j)) (s + 4 * delta (nj j)))
        (v j S.xi)

theorem bounded_recovery (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    (omega : Ultrafilter ℕ) (hfree : (omega : Filter ℕ) ≤ Filter.atTop)
    (T : H →L[ℂ] H) (s : ℝ) (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hdelta0 : Tendsto delta atTop (𝓝 0)) (h : ℕ → H) (hunit : ∀ n, ‖h n‖ = 1)
    (hband : ∀ n, S.D.HasSpectralSupport (Icc (s - delta n) (s + delta n)) (h n))
    (hpositive : 0 < Filter.limsup
      (fun n => fixedMean omega (fun t => ‖T (S.D.unitary t (h n))‖ ^ 2)) atTop) :
    RecoveryConclusion S T s delta := by
  sorry

end BoundedRecovery

end

end OAI
