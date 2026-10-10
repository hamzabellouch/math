import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ScalarConductivity

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev JetFiber := EuclideanSpace ℝ (Fin 4)
def ball : Set R3 := Metric.ball 0 3
def ballMeasure : Measure R3 := volume.restrict ball
abbrev JetSpace := Lp JetFiber 2 ballMeasure

def smoothJet (f : R3 → ℝ) (x : R3) : JetFiber :=
  WithLp.toLp 2 (Fin.cases (f x) (fun i => gradient f x i))

def smoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def compactSmoothJets : Set JetSpace :=
  { z | ∃ (f : R3 → ℝ) (_ : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (_ : HasCompactSupport f) (_ : tsupport f ⊆ ball)
      (hf : MemLp (smoothJet f) 2 ballMeasure), z = hf.toLp (smoothJet f) }

def H1Space : Submodule ℝ JetSpace :=
  (Submodule.span ℝ smoothJets).topologicalClosure
abbrev H1 := H1Space

def zeroTraceAmbient : Submodule ℝ JetSpace :=
  (Submodule.span ℝ compactSmoothJets).topologicalClosure

def H10 : Submodule ℝ H1 := zeroTraceAmbient.comap H1Space.subtype

instance H10_isClosed : IsClosed (H10 : Set H1) := by
  exact (Submodule.isClosed_topologicalClosure
    (Submodule.span ℝ compactSmoothJets)).preimage continuous_subtype_val

abbrev TraceSpace := H1 ⧸ H10
abbrev TraceDual := TraceSpace →L[ℝ] ℝ
abbrev DNOperator := TraceSpace →L[ℝ] TraceDual

def trace (u : H1) : TraceSpace := H10.mkQ u

def weakGradient (u : H1) (x : R3) : R3 :=
  WithLp.toLp 2 (fun i => (u.val x) i.succ)

def energy (γ : R3 → ℝ) (u v : H1) : ℝ :=
  ∫ x, γ x * inner ℝ (weakGradient u x) (weakGradient v x) ∂ballMeasure

def Harmonic (γ : R3 → ℝ) (u : H1) : Prop :=
  ∀ h : H1, h ∈ H10 → energy γ u h = 0

def IsDirichletToNeumann (γ : R3 → ℝ) (Λ : DNOperator) : Prop :=
  ∀ f : TraceSpace, ∃ u : H1,
    trace u = f ∧ Harmonic γ u ∧
    (∀ u' : H1, trace u' = f → Harmonic γ u' → u' = u) ∧
    ∀ v : H1, Λ f (trace v) = energy γ u v

def EqualOneNearBoundary (γ : R3 → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 3 ∧ ∀ᵐ x ∂ballMeasure, r < ‖x‖ → γ x = 1

def MainStatement : Prop :=
  ∃ (γ₀ γ₁ : R3 → ℝ) (c C : ℝ) (Λ : DNOperator),
    0 < c ∧ c < C ∧
    Measurable γ₀ ∧ Measurable γ₁ ∧
    MemLp γ₀ ∞ ballMeasure ∧ MemLp γ₁ ∞ ballMeasure ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₀ x ∧ γ₀ x ≤ C) ∧
    (∀ᵐ x ∂ballMeasure, c ≤ γ₁ x ∧ γ₁ x ≤ C) ∧
    EqualOneNearBoundary γ₀ ∧ EqualOneNearBoundary γ₁ ∧
    0 < ballMeasure {x | γ₀ x ≠ γ₁ x} ∧
    IsDirichletToNeumann γ₀ Λ ∧ IsDirichletToNeumann γ₁ Λ

theorem main_nonuniqueness : MainStatement := by
  sorry

end ScalarConductivity
end

end OAI
