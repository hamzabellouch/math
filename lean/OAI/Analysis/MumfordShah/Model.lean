import Mathlib

namespace OAI

/-! MumfordShah model. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

abbrev Plane := ℂ

abbrev lengthMeasure : Measure Plane := Measure.hausdorffMeasure 1

def CompactlyContained (S V : Set Plane) : Prop :=
  IsCompact (closure S) ∧ closure S ⊆ V

def essentialSupport (f : Plane → ℝ) : Set Plane :=
  {x | ∀ r : ℝ, 0 < r → ¬ (∀ᵐ y ∂volume.restrict (ball x r), f y = 0)}

def HasWeakGradientOn (u : Plane → ℝ) (m : Plane → Plane) (U : Set Plane) : Prop :=
  ∀ ψ : Plane → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∀ a : Plane,
      (∫ x in U, u x * fderiv ℝ ψ x a) =
        -(∫ x in U, inner ℝ (m x) a * ψ x)

def SobolevOn (u : Plane → ℝ) (m : Plane → Plane) (U : Set Plane) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp m 2 (volume.restrict U) ∧
    HasWeakGradientOn u m U

structure Pair where
  u : Plane → ℝ
  K : Set Plane
  grad : Plane → Plane

def Admissible (Ω : Set Plane) (p : Pair) : Prop :=
  p.K ⊆ Ω ∧ IsClosed {x : Ω | (x : Plane) ∈ p.K} ∧
  lengthMeasure p.K < ⊤ ∧ MemLp p.u 2 (volume.restrict Ω) ∧
  SobolevOn p.u p.grad (Ω \ p.K)

def fidelityEnergy (g : Plane → ℝ) (p : Pair) (V : Set Plane) : ℝ≥0∞ :=
  (∫⁻ x in V \ p.K, ENNReal.ofReal (‖p.grad x‖ ^ 2)) +
    lengthMeasure (p.K ∩ V) +
    (∫⁻ x in V, ENNReal.ofReal (|p.u x - g x| ^ 2))

def IsCompactComparison (p q : Pair) (V : Set Plane) : Prop :=
  CompactlyContained
    ((q.K ∆ p.K) ∪ essentialSupport (fun x => q.u x - p.u x)) V

def AbsoluteMinimizer (Ω : Set Plane) (g : Plane → ℝ) (p : Pair) : Prop :=
  Admissible Ω p ∧
  ∀ V : Set Plane, IsOpen V → CompactlyContained V Ω →
    ∀ q : Pair, Admissible Ω q → IsCompactComparison p q V →
      fidelityEnergy g p V ≤ fidelityEnergy g q V

def Reduced (Ω K : Set Plane) : Prop :=
  K ⊆ Ω ∧ ∀ x ∈ Ω, x ∈ K ↔
    ∀ r : ℝ, 0 < r → lengthMeasure (K ∩ ball x r) ≠ 0

def Rectifiable (H : Set Plane) : Prop :=
  ∃ γ : ℕ → ℝ → Plane, (∀ n, ∃ C : ℝ≥0, LipschitzWith C (γ n)) ∧
    lengthMeasure (H \ ⋃ n, Set.range (γ n)) = 0

def GlobalAdmissible (p : Pair) : Prop :=
  IsClosed p.K ∧ Rectifiable p.K ∧
    (∀ R : ℝ, 0 < R → lengthMeasure (p.K ∩ ball (0 : Plane) R) < ⊤) ∧
    ∀ U : Set Plane, IsOpen U → Bornology.IsBounded U →
      SobolevOn p.u p.grad (U \ p.K)

def homogeneousEnergy (p : Pair) (V : Set Plane) : ℝ≥0∞ :=
  (∫⁻ x in V \ p.K, ENNReal.ofReal (‖p.grad x‖ ^ 2)) + lengthMeasure (p.K ∩ V)

def GlobalAbsoluteMinimizer (p : Pair) : Prop :=
  GlobalAdmissible p ∧
  ∀ V : Set Plane, IsOpen V → Bornology.IsBounded V →
    ∀ q : Pair, GlobalAdmissible q → IsCompactComparison p q V →
      homogeneousEnergy p V ≤ homogeneousEnergy q V

def PositivelySeparated (A B : Set Plane) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ a ∈ A, ∀ b ∈ B, d ≤ dist a b

def ContainsOpenC1Arc (A H : Set Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧
  ∃ γ : ℝ → Plane,
    ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧
    (∀ s ∈ Ioo (-1 : ℝ) 1, deriv γ s ≠ 0) ∧
    Topology.IsEmbedding (fun s : Ioo (-1 : ℝ) 1 => γ s) ∧
    H ∩ U = γ '' Ioo (-1 : ℝ) 1 ∧ H ∩ U ⊆ A

def CompactPieceExclusion : Prop :=
  ∀ p : Pair, GlobalAbsoluteMinimizer p → IsConnected p.Kᶜ →
    (∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in ball (0 : Plane) R, ‖p.grad x‖ ^ 2) ≤ C * (1 + R)) →
    ¬ ∃ A : Set Plane, IsCompact A ∧ A ⊆ p.K ∧ 0 < lengthMeasure A ∧
      IsClosed (p.K \ A) ∧ PositivelySeparated A (p.K \ A) ∧
      ContainsOpenC1Arc A p.K

def BoundedLipschitzDomain (Ω : Set Plane) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧
    ∀ x ∈ frontier Ω, ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
      ∃ κ : ℝ → ℝ, ∃ C : ℝ≥0, ∃ r : ℝ,
        0 < r ∧ LipschitzWith C κ ∧ κ 0 = 0 ∧
        ∀ z ∈ ball x r, z ∈ Ω ↔ κ (R (z - x)).re < (R (z - x)).im

def RegularHolderArc (α a b : ℝ) (γ : ℝ → Plane) : Prop :=
  a < b ∧
  (∃ ε : ℝ, 0 < ε ∧ ContDiffOn ℝ 1 γ (Ioo (a - ε) (b + ε))) ∧
  Set.InjOn γ (Icc a b) ∧
  (∀ s ∈ Icc a b, deriv γ s ≠ 0) ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    ‖deriv γ s - deriv γ t‖ ≤ C * |s - t| ^ α

def InteriorArcModel (K W : Set Plane) (x : Plane) (α : ℝ) : Prop :=
  ∃ γ : ℝ → Plane, RegularHolderArc α (-1) 1 γ ∧
    γ 0 = x ∧ K ∩ W = γ '' Ioo (-1 : ℝ) 1

def EndpointArcModel (K W : Set Plane) (x : Plane) (α : ℝ) : Prop :=
  ∃ γ : ℝ → Plane, RegularHolderArc α 0 1 γ ∧
    γ 0 = x ∧ K ∩ W = γ '' Ico (0 : ℝ) 1

def TripleJunctionModel (K W : Set Plane) (x : Plane) (α : ℝ) : Prop :=
  ∃ γ : Fin 3 → ℝ → Plane,
    (∀ i, RegularHolderArc α 0 1 (γ i) ∧ γ i 0 = x) ∧
    K ∩ W = ⋃ i, γ i '' Ico (0 : ℝ) 1 ∧
    (∀ i j, i ≠ j →
      (γ i '' Ico (0 : ℝ) 1) ∩ (γ j '' Ico (0 : ℝ) 1) = {x}) ∧
    ∀ i j, i ≠ j →
      inner ℝ (deriv (γ i) 0) (deriv (γ j) 0) =
        -(‖deriv (γ i) 0‖ * ‖deriv (γ j) 0‖) / 2

def InteriorLocalModels (Ω K : Set Plane) : Prop :=
  ∀ x ∈ K, ∃ W : Set Plane, IsOpen W ∧ x ∈ W ∧ CompactlyContained W Ω ∧
    ∃ α : ℝ, 0 < α ∧
      (InteriorArcModel K W x α ∨ EndpointArcModel K W x α ∨
        TripleJunctionModel K W x α)

def ComponentsMeeting (K U : Set Plane) : Set (Set Plane) :=
  {C | (∃ x ∈ K, C = connectedComponentIn K x) ∧ (C ∩ U).Nonempty}

def InteriorRegularity : Prop :=
  ∀ Ω : Set Plane, BoundedLipschitzDomain Ω →
    ∀ g : Plane → ℝ, MemLp g ⊤ (volume.restrict Ω) →
      ∀ p : Pair, AbsoluteMinimizer Ω g p → Reduced Ω p.K →
        InteriorLocalModels Ω p.K ∧
          ∀ U : Set Plane, IsOpen U → CompactlyContained U Ω →
            (ComponentsMeeting p.K U).Finite

end MumfordShah
end

end OAI
