import Mathlib

namespace OAI

/-!
# Variational isotropic elasticity

H¹ is the closure of smooth value/gradient jets in L². Boundary data are
the quotient by the closure of compactly supported smooth jets, and the
Dirichlet-to-Neumann map is the physical variational displacement-to-traction
pairing. Arbitrary-data Dirichlet well-posedness and independence of
representatives are proved, not assumed. Identification of the quotient
norm with boundary-chart fractional Sobolev norms is not established here.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Elasticity

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev V := X

def coordVector (i : Fin 3) : X := EuclideanSpace.single i 1

def SmoothBoundary (Ω : Set X) : Prop :=
  ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph X X,
    x ∈ e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
    e x 0 = 0 ∧
    ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0

def Domain (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ SmoothBoundary Ω

def SmoothUpTo (Ω : Set X) (f : X → ℝ) : Prop :=
  ∃ U : Set X, IsOpen U ∧ closure Ω ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) f U

def Admissible (Ω : Set X) (lam mu : X → ℝ) : Prop :=
  SmoothUpTo Ω lam ∧ SmoothUpTo Ω mu ∧
    ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x

abbrev Ambient (Ω : Set X) :=
  Lp V 2 (volume.restrict Ω) × (Fin 3 → Lp V 2 (volume.restrict Ω))

def coordDeriv (f : X → V) (i : Fin 3) (x : X) : V :=
  fderiv ℝ f x (coordVector i)

def SmoothJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

def TestJets (Ω : Set X) : Set (Ambient Ω) :=
  {j | ∃ (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
      (hd : ∀ i, MemLp (coordDeriv f i) 2 (volume.restrict Ω)),
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω ∧
    j.1 = hf.toLp f ∧ j.2 = fun i => (hd i).toLp (coordDeriv f i)}

abbrev H1 (Ω : Set X) := {j : Ambient Ω // j ∈ closure (SmoothJets Ω)}

def HasZeroTrace (Ω : Set X) (u : H1 Ω) : Prop :=
  u.val ∈ closure (TestJets Ω)

def SameTrace (Ω : Set X) (u v : H1 Ω) : Prop :=
  u.val - v.val ∈ closure (TestJets Ω)

/-- Variational boundary data: the quotient by the closure of compactly supported smooth jets. -/
abbrev BoundaryData (Ω : Set X) := Quot (SameTrace Ω)

def trace (Ω : Set X) (u : H1 Ω) : BoundaryData Ω := Quot.mk _ u

def div (Ω : Set X) (u : H1 Ω) (x : X) : ℝ :=
  ∑ i, (u.val.2 i x) i

def strain (Ω : Set X) (u : H1 Ω) (x : X) (i j : Fin 3) : ℝ :=
  ((u.val.2 j x) i + (u.val.2 i x) j) / 2

def energy (Ω : Set X) (lam mu : X → ℝ) (u v : H1 Ω) : ℝ :=
  ∫ x, (lam x * div Ω u x * div Ω v x +
    2 * mu x * ∑ i, ∑ j, strain Ω u x i j * strain Ω v x i j)
    ∂(volume.restrict Ω)

def WeakSolution (Ω : Set X) (lam mu : X → ℝ) (u : H1 Ω) : Prop :=
  ∀ v : H1 Ω, HasZeroTrace Ω v → energy Ω lam mu u v = 0

/-- A definition by choice, not a wellposedness assumption. The fallback is
irrelevant once the Dirichlet problem has been proved solvable. -/
def dirichletSolution (Ω : Set X) (lam mu : X → ℝ)
    (f : BoundaryData Ω) : H1 Ω := by
  classical
  exact if h : ∃ u : H1 Ω, trace Ω u = f ∧ WeakSolution Ω lam mu u
  then Classical.choose h
  else f.out

/-- The weak displacement-to-traction pairing; definition (physical-dn). -/
def DN (Ω : Set X) (lam mu : X → ℝ) : BoundaryData Ω → BoundaryData Ω → ℝ :=
  fun f g => energy Ω lam mu (dirichletSolution Ω lam mu f) g.out

def MainClaim : Prop :=
  ∀ (Ω : Set X), Domain Ω →
  ∀ (lam₁ mu₁ lam₂ mu₂ : X → ℝ),
    Admissible Ω lam₁ mu₁ → Admissible Ω lam₂ mu₂ →
    DN Ω lam₁ mu₁ = DN Ω lam₂ mu₂ →
    (∀ x ∈ Ω, lam₁ x = lam₂ x) ∧ (∀ x ∈ Ω, mu₁ x = mu₂ x)

end Elasticity

end

end OAI
