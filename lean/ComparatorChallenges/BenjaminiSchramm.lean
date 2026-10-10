import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

def Adj (G : BondGraph V E) (x y : V) : Prop := ∃ e, G e = s(x, y)

def LocallyFinite (G : BondGraph V E) : Prop := ∀ x, {e | x ∈ G e}.Finite

def Connected (G : BondGraph V E) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adj G) x y

def IsAut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E) : Prop :=
  ∀ e, G (b e) = (G e).map a

def QuasiTransitive (G : BondGraph V E) : Prop :=
  ∃ representatives : Finset V, ∀ x, ∃ o ∈ representatives,
    ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a o = x

def vertexBoundary (G : BondGraph V E) (A : Finset V) : Set V :=
  {y | y ∉ A ∧ ∃ x ∈ A, Adj G x y}

noncomputable def hV (G : BondGraph V E) : ℝ :=
  sInf {r | ∃ A : Finset V, A.Nonempty ∧
    r = (vertexBoundary G A).ncard / (A.card : ℝ)}

def Conn (G : BondGraph V E) (ω : Set E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ ω, G e = s(a, b)) x y

def cluster (G : BondGraph V E) (ω : Set E) (x : V) : Set V :=
  {y | Conn G ω x y}

def infiniteClusters (G : BondGraph V E) (ω : Set E) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = cluster G ω x}

noncomputable def law (p : unitInterval) : Measure (Set E) :=
  setBernoulli Set.univ p

noncomputable def pc (G : BondGraph V E) : unitInterval :=
  sInf {p | 0 < law p {ω | (infiniteClusters G ω).Nonempty}}

noncomputable def pu (G : BondGraph V E) : unitInterval :=
  sInf {p | law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1}

noncomputable def twoPoint (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  (law p {ω | Conn G ω x y}).toReal

noncomputable abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

noncomputable def HasKernel [DecidableEq V]
    (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = (twoPoint G p x y : ℂ)

noncomputable def OperatorBounded (G : BondGraph V E) (p : unitInterval) : Prop := by
  classical
  exact ∃ A : Hilbert V →L[ℂ] Hilbert V, HasKernel G p A

noncomputable def operatorNorm (G : BondGraph V E) (p : unitInterval) : ℝ≥0∞ := by
  classical
  exact sInf {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
    HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖}

noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

def MainConclusion (G : BondGraph V E) : Prop :=
  (sSup {r | ∃ p : unitInterval, p < pc G ∧ r = operatorNorm G p} =
    operatorNorm G (pc G)) ∧
  operatorNorm G (pc G) < ⊤ ∧
  pc G < ptwo G ∧ ptwo G ≤ pu G ∧
  ∃ p₁ p₂ : unitInterval, pc G < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters G (openEdges labels p)).Infinite

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable

def openSimpleGraph (G : BondGraph V E) (ω : Set E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ ω, G e = s(x,y)
  symm := ⟨by
    rintro x y ⟨hxy, e, he, h⟩
    exact ⟨hxy.symm, e, he, h.trans (Sym2.eq_swap ..)⟩⟩
  loopless := ⟨by simp⟩

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def susceptibility (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ :=
  ∑' y, twoPoint G p x y

end Percolation

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.decEq

noncomputable def triangleDiagram (G : BondGraph V E) (p : unitInterval) (x : V) : ℝ≥0∞ :=
  ∑' ab : V × V, ENNReal.ofReal
    (twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2 * twoPoint G p ab.2 x)

noncomputable def graphDistance (G : BondGraph V E) (x y : V) : ℕ :=
  (openSimpleGraph G Set.univ).dist x y

def ExponentialDecay (G : BondGraph V E) (p : unitInterval) : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧ ∀ x y,
    twoPoint G p x y ≤ A * Real.exp (-a * graphDistance G x y)

noncomputable def pexp (G : BondGraph V E) : unitInterval :=
  sSup {p | ExponentialDecay G p}

def PowerTail (f : ℕ → ℝ) (exponent : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 0 < n →
    c * (n : ℝ) ^ (-exponent) ≤ f n ∧ f n ≤ C * (n : ℝ) ^ (-exponent)

def volumeEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | (n : ℕ∞) ≤ (cluster G ω x).encard}

def intrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ (openSimpleGraph G ω).dist x y}

def extrinsicRadiusEvent (G : BondGraph V E) (x : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ y ∈ cluster G ω x, n ≤ graphDistance G x y}

noncomputable def criticalTail (G : BondGraph V E)
    (A : V → ℕ → Set (Set E)) (x : V) (n : ℕ) : ℝ :=
  (law (pc G) (A x n)).toReal

def CriticalTailLaws (G : BondGraph V E) : Prop :=
  ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2) ∧
    PowerTail (criticalTail G (intrinsicRadiusEvent G) x) 1 ∧
    PowerTail (criticalTail G (extrinsicRadiusEvent G) x) 1

def SusceptibilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, p < pc G → (pc G : ℝ) - p < δ →
      c / ((pc G : ℝ) - p) ≤ susceptibility G p x ∧
      susceptibility G p x ≤ C / ((pc G : ℝ) - p)

noncomputable def percolationProbability (G : BondGraph V E) (p : unitInterval)
    (x : V) : ℝ := (law p {ω | (cluster G ω x).Infinite}).toReal

def PercolationProbabilityLaw (G : BondGraph V E) : Prop :=
  ∀ x, ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧
    ∀ p : unitInterval, pc G < p → (p : ℝ) - pc G < δ →
      c * ((p : ℝ) - pc G) ≤ percolationProbability G p x ∧
      percolationProbability G p x ≤ C * ((p : ℝ) - pc G)

end Percolation.BenjaminiSchramm

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u v
variable {V : Type u} {E : Type v}

def CriticalLawsConclusion (G : BondGraph V E) : Prop :=
  (∀ x, triangleDiagram G (pc G) x ≤ operatorNorm G (pc G) ^ 3 ∧
    triangleDiagram G (pc G) x < ⊤) ∧
  SusceptibilityLaw G ∧ PercolationProbabilityLaw G ∧ CriticalTailLaws G ∧
  (pc G < ptwo G ∧ ptwo G ≤ pexp G) ∧
  ∀ p : unitInterval, p < ptwo G → ExponentialDecay G p

end Percolation.BenjaminiSchramm

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

namespace Percolation.BenjaminiSchramm
universe u
variable {Λ : Type u} [Group Λ]
attribute [local instance] Classical.decEq

abbrev CayleyEdge (S : Finset Λ) := (SimpleGraph.mulCayley (S : Set Λ)).edgeSet

def cayleyBond (S : Finset Λ) : BondGraph Λ (CayleyEdge S) := Subtype.val

def FolnerAmenable (Λ : Type u) [Group Λ] : Prop :=
  ∀ K : Finset Λ, ∀ ε : ℝ, 0 < ε → ∃ A : Finset Λ, A.Nonempty ∧
    ∀ k ∈ K, (((A.image (fun x => x * k)) \ A).card : ℝ) < ε * A.card

end Percolation.BenjaminiSchramm

namespace Percolation.BenjaminiSchramm

universe u v

/-- Critical operator boundedness, the threshold gap, and simultaneous nonuniqueness. -/
theorem full_main {V : Type u} {E : Type v} [Infinite V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : MainConclusion G := by
  sorry

/-- Critical mean-field laws and uniform exponential connectivity below the operator threshold. -/
theorem critical_laws {V : Type u} {E : Type v} [Infinite V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : CriticalLawsConclusion G := by
  sorry

/-- Nonuniqueness for every prescribed finite symmetric Cayley generating set. -/
theorem cayley_main {Λ : Type u} [Group Λ]
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite := by
  sorry

end Percolation.BenjaminiSchramm

end OAI
