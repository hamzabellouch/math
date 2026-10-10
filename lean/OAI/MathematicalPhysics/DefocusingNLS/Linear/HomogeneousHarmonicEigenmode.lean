import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicChannels

namespace OAI

/-! # The radial equation of an actual semigroup eigenvector -/

open Set
open scoped ContDiff Laplacian NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

def IsHarmonicRadialEigenpair (a b : ℝ) (m : ℕ) (Q : ℝ → ℂ)
    (eta lam : ℂ) (f g : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r →
    (lam * f r = Complex.I * (deriv (deriv f) r + ((11 / r : ℝ) : ℂ) * deriv f r -
      eta / (r ^ 2 : ℝ) * f r) - (r / 2 : ℝ) * deriv f r +
      (-(a : ℂ) + Complex.I * (b : ℂ)) * f r - Complex.I *
        ((((m + 1 : ℕ) : ℂ) * Q r ^ m * star (Q r) ^ m) * f r +
          ((m : ℂ) * Q r ^ (m + 1) * star (Q r) ^ (m - 1)) * g r)) ∧
    (lam * g r = -Complex.I * (deriv (deriv g) r + ((11 / r : ℝ) : ℂ) * deriv g r -
      eta / (r ^ 2 : ℝ) * g r) - (r / 2 : ℝ) * deriv g r +
      (-(a : ℂ) - Complex.I * (b : ℂ)) * g r + Complex.I *
        (star (((m + 1 : ℕ) : ℂ) * Q r ^ m * star (Q r) ^ m) * g r +
          star ((m : ℂ) * Q r ^ (m + 1) * star (Q r) ^ (m - 1)) * f r))

theorem homogeneous_eigenvector_harmonic_channels (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q : HomogeneousY a k) (Q : ℝ → ℂ)
    (hq : ∀ x : E, homogeneousPhysicalCLM a k ha ha1 hk q x = Q ‖x‖)
    (w : HomogeneousY a k × HomogeneousY a k) (lam : ℂ)
    (hw : ∀ t : ℝ≥0, homogeneousComplexLinearizedStep a b k ha ha1 hk m q t w =
      Complex.exp (((t : ℝ) : ℂ) * lam) • w)
    (Y : E → ℂ) (eta : ℂ)
    (hY : ∀ x : E, x ≠ 0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0 < t → Y (t • x) = Y x)
    (hEigen : ∀ x : E, x ≠ 0 → Δ Y x = -(eta / (‖x‖ ^ 2 : ℝ)) * Y x) :
    let f := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk w.1 x)
    let g := harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk w.2 x)
    ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ IsHarmonicRadialEigenpair a b m Q eta lam f g := by
  have hd := hasDerivWithinAt_semigroup_eigenvector
    (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) lam w hw
  obtain ⟨hf, hg, he⟩ := homogeneous_generator_harmonic_channels
    a b k ha ha1 hk m q Q hq w (lam • w) hd Y eta hY hRay hEigen
  refine ⟨hf, hg, ?_⟩
  intro r hr
  have h := he r hr
  simpa only [Prod.smul_fst, Prod.smul_snd, homogeneous_harmonic_smul] using h

end DefocusingNLS

end OAI
