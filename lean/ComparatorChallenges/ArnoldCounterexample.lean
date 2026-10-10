import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample

abbrev CV := Fin 5 → ℂ

def quadricPolynomial (z : CV) : ℂ := ∑ j, z j ^ 2

def normSquared (z : CV) : ℝ := ∑ j, Complex.normSq (z j)

def IsUnitQuadric (z : CV) : Prop :=
  normSquared z = 1 ∧ quadricPolynomial z = 0

abbrev UnitQuadric := {z : CV // IsUnitQuadric z}

/-- The literal projective quadric sum z_j^2 = 0 in CP^4. -/
def Q3 := {q : Projectivization ℂ CV //
  ∃ (z : CV) (hz : z ≠ 0), Projectivization.mk ℂ z hz = q ∧
    quadricPolynomial z = 0}

def project (z : UnitQuadric) : Q3 := by
  have hz : (z : CV) ≠ 0 := by
    intro h
    have hunit := z.property.1
    simp [normSquared, h] at hunit
  exact ⟨Projectivization.mk ℂ z hz, z, hz, rfl, z.property.2⟩

/-- Horizontal lifts of the real tangent of Q3 at [z]. -/
def Horizontal (z v : CV) : Prop :=
  (∑ j, star (z j) * v j) = 0 ∧ (∑ j, z j * v j) = 0

/-- The restricted Fubini--Study form, evaluated on horizontal lifts. -/
def omega (v w : CV) : ℝ := 2 * (∑ j, star (v j) * w j).im

/-- A local smooth extension of the pullback of h to the unit isotropic cone. -/
def LocalFunctionLift (h : Q3 → ℝ) (z : UnitQuadric)
    (U : Set CV) (g : CV → ℝ) : Prop :=
  IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
    ∀ y : UnitQuadric, (y : CV) ∈ U → g y = h (project y)

def IsSmoothFunction (h : Q3 → ℝ) : Prop :=
  ∀ z : UnitQuadric, ∃ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g

structure SmoothFunction where
  toFun : Q3 → ℝ
  smooth : IsSmoothFunction toFun

/-- dh_q = 0, expressed using all local lifts, independent of normal extensions. -/
def IsCritical (h : Q3 → ℝ) (q : Q3) : Prop :=
  ∀ z : UnitQuadric, project z = q →
    ∀ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g →
      ∀ v : CV, Horizontal z v → fderiv ℝ g z v = 0

def criticalSet (h : SmoothFunction) : Set Q3 := {q | IsCritical h.toFun q}

/-- The minimum critical number, including degenerate functions (ENat allows infinity). -/
def criticalNumber : ℕ∞ := ⨅ h : SmoothFunction, (criticalSet h).encard

/-- An explicit smooth lift of a Hamiltonian isotopy, with inverse and generator.
The Hamiltonian equation uses i_X omega = dH. -/
structure HamiltonianPath (φ : Q3 ≃ Q3) where
  forward : ℝ × CV → CV
  backward : ℝ × CV → CV
  hamiltonian : ℝ × CV → ℝ
  forward_smooth : ContDiff ℝ ∞ forward
  backward_smooth : ContDiff ℝ ∞ backward
  hamiltonian_smooth : ContDiff ℝ ∞ hamiltonian
  forward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (forward (t, z))
  backward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (backward (t, z))
  forward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → forward (t, a • (z : CV)) = a • forward (t, z)
  backward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → backward (t, a • (z : CV)) = a • backward (t, z)
  hamiltonian_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → hamiltonian (t, a • (z : CV)) = hamiltonian (t, z)
  left_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    backward (t, forward (t, z)) = z
  right_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    forward (t, backward (t, z)) = z
  start : ∀ z : UnitQuadric, forward (0, z) = z
  finish : ∀ z : UnitQuadric,
    project ⟨forward (1, z), forward_preserves 1 (by norm_num) z⟩ = φ (project z)
  equation : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric, ∀ v : CV,
    Horizontal (forward (t, z)) v →
      omega (deriv (fun s : ℝ => forward (s, z)) t) v =
        fderiv ℝ (fun w : CV => hamiltonian (t, w)) (forward (t, z)) v

def IsHamiltonian (φ : Q3 ≃ Q3) : Prop := Nonempty (HamiltonianPath φ)

def fixedSet (φ : Q3 ≃ Q3) : Set Q3 := {q | φ q = q}

/-- Eigenvalue 1 in the derivative on the quotient tangent, not an ambient
  spurious vertical eigenvector. v is nonzero and horizontal. -/
def HasDegenerateFixedPoint (φ : Q3 ≃ Q3) : Prop :=
  ∃ (z : UnitQuadric) (v : CV), φ (project z) = project z ∧ v ≠ 0 ∧
    Horizontal z v ∧ ∃ (U : Set CV) (G : CV → CV),
      IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ G U ∧ G z = z ∧
      (∀ y : UnitQuadric, (y : CV) ∈ U →
        ∃ hy : IsUnitQuadric (G y), project ⟨G y, hy⟩ = φ (project y)) ∧
      ∃ a : ℝ, fderiv ℝ G z v - v = a • (Complex.I • (z : CV))

/-- The Hamiltonian counterexample, with the complete fixed set, the lower bound
for all smooth functions, and a genuine nonzero quotient-tangent eigenvector. -/
theorem main :
    ∃ φ : Q3 ≃ Q3, IsHamiltonian φ ∧ (fixedSet φ).encard = 3 ∧
      (3 : ℕ∞) < 4 ∧ 4 ≤ criticalNumber ∧ HasDegenerateFixedPoint φ := by
  sorry

end ArnoldCounterexample

end

end OAI
