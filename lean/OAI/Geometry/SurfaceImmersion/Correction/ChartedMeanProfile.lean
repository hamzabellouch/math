import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData

namespace OAI

/-! Numerical and compact geometric data kept fixed while scales and maps
vary in the small-increment construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

structure ChartedMeanProfile {n : ℕ} (P : Fin 3 → Fin n → Expression) where
  U : Set Base
  O : Set LowJet
  Q : Set LowJet
  V : Set SmallModes.Base
  openU : IsOpen U
  openO : IsOpen O
  openV : IsOpen V
  compact : IsCompact Q
  subsetDomain : Q ⊆ O
  smoothP : ∀ k l, (P k l).SmoothCoeffs O
  C : ℕ → ℝ
  D : ℕ → ℝ
  J : ℕ → ℝ
  inv : ℕ → ℝ
  forms : ℕ → ℝ
  psi : ℕ → ℝ
  normal : ℕ → ℝ
  B : ℕ → ℝ
  F : ℕ → ℝ
  nonnegC : ∀ m, 0 ≤ C m
  oneLEJ : ∀ m, 1 ≤ J m
  oneLEInv : ∀ m, 1 ≤ inv m
  oneLEForms : ∀ m, 1 ≤ forms m
  oneLEPsi : ∀ m, 1 ≤ psi m
  oneLENormal : ∀ m, 1 ≤ normal m
  oneLEB : ∀ m, 1 ≤ B m
  nonnegF : ∀ m, 0 ≤ F m

namespace ChartedMeanProfile
variable {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ε τ : ℝ} {s : ℝ≥0}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ} {K : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

structure Fits (d : ChartedMeanData c r ρ R reference) : Prop where
  domain : c.U = p.U
  coefficients : c.C = p.C
  perturbation : c.D = p.D
  coordinates : c.J = p.J
  target : c.e.target = p.V
  inverse : d.budgets.inv = p.inv
  forms : d.budgets.forms = p.forms
  cutoff : d.budgets.psi = p.psi
  normal : d.budgets.normal = p.normal
  jets : d.B = p.B
  phase : d.F = p.F
  range : d.compactJets = p.Q

end ChartedMeanProfile
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
