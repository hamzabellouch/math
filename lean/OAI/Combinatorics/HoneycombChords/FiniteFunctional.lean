import OAI.Combinatorics.HoneycombChords.InterpolationDefinitions

namespace OAI

/-! The finite strip functional and its polynomial and hyperbolic interpolation space.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section
namespace CriticalHoneycomb.FiniteFunctional
/-- Entire real continuation of cosh(t sqrt x), also at negative x. -/
noncomputable def C (t x : ℝ) : ℂ :=
  if 0 ≤ x then (Real.cosh (t * Real.sqrt x) : ℂ)
  else (Real.cos (t * Real.sqrt (-x)) : ℂ)

noncomputable def D (x : ℝ) : ℂ := 2 * C angle x - 1
noncomputable def aStar : ℂ := 2 * (Real.cos (2*angle) : ℂ) - 1

/-- Both blocks of the exact 2N-dimensional interpolation space. -/
noncomputable def M (N : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ
    (Set.range (fun j : Fin N => fun x : ℝ => (x : ℂ)^j.val) ∪
     Set.range (fun j : Fin N => fun x : ℝ =>
       iteratedDeriv j.val (fun t : ℝ => C t x) angle))

/-- Integral of the entire cosine continuation, with removable value `g 0 = angle`. -/
noncomputable def g (x : ℝ) : ℂ := ∫ t in (0:ℝ)..angle, C t x

noncomputable def admissibleDensity (N : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  M N ⊔ Submodule.span ℂ {g}

/-- Bilinear pairing for the positive strip measure, without complex conjugation. -/
noncomputable def pairing (H f : ℝ → ℂ) : ℂ :=
  ∫ z in Set.Ioi (0:ℝ),
    H (z^2) * f (z^2) *
      ((z : ℂ) * D (z^2) / (Real.sinh (4*angle*z) : ℂ))

noncomputable def value (ρ : ℂ) (f H : ℝ → ℂ) : ℂ :=
  4*aStar*H (-4) + ρ*H 0 + pairing H f

/-- Representation of the physical bridge mass by the finite strip functional. -/
def PhysicalFiniteFunctional : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ (B : ℝ) (ρ : ℂ) (f : ℝ → ℂ),
    0 ≤ B ∧ bridgeMass N = ENNReal.ofReal B ∧
    f ∈ admissibleDensity N ∧
    (∀ H ∈ M N, value ρ f H = 0) ∧
    value ρ f (C (angle/2)) = 0 ∧
    value ρ f (fun x => C (3*angle/2) x - C (angle/2) x / D x) = 0 ∧
    2*(B:ℂ) = value ρ f (fun x => (D x)⁻¹)


end CriticalHoneycomb.FiniteFunctional

end

end OAI
