import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
local instance namedAtLeastTwoTwo : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Rows (d : ℕ) := Fin (d/16) → Fin d → ℝ
noncomputable def radial {d : ℕ} (x : Ambient d) : Ambient d := ‖x‖⁻¹ • x
noncomputable def sphereProbability (d : ℕ) : Measure (Ambient d) :=
  ((volume (ball (0 : Ambient d) 1))⁻¹ • volume.restrict (ball (0 : Ambient d) 1)).map radial
noncomputable def J {d : ℕ} (ν : Measure (Ambient d)) (s : Ambient d) : ℝ≥0∞ :=
  ∫⁻ u,((ENNReal.ofReal ‖u-s‖)⁻¹)^(2*(d/16)) ∂ν
noncomputable def B {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  ∫ s, Real.log ((J ν s).toReal) ∂ν
noncomputable def Phi {d : ℕ} (ν : Measure (Ambient d)) : ℝ :=
  (InformationTheory.klDiv ν (sphereProbability d)).toReal - B ν

def BoundedDensity {d : ℕ} (ν : Measure (Ambient d)) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ν ≤ ENNReal.ofReal H • sphereProbability d

noncomputable def rowLaw (d : ℕ) : Measure (Rows d) :=
  Measure.pi (fun _ : Fin (d/16) => Measure.pi (fun _ : Fin d => gaussianReal 0 1))
noncomputable def labels {d : ℕ} (a : Rows d) (s : Ambient d) : Fin (d/16) → ℝ :=
  fun i => ∑ j,a i j*s j
structure BlockRule (d N : ℕ) where
  prob : (Fin N × (Rows d × (Fin (d/16) → ℝ))) → Fin N → ℝ
  measurable_prob : ∀ w, Measurable (fun x => prob x w)
  nonneg_prob : ∀ x w, 0 ≤ prob x w
  sum_prob : ∀ x, ∑ w,prob x w=1

noncomputable def outgoingLaw {d N : ℕ} (μ : Measure (Ambient d × Fin N))
    (rule : BlockRule d N) : Measure (Ambient d × Fin N) :=
  ∑ w : Fin N, ((μ.prod (rowLaw d)).withDensity (fun x =>
    ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w))).map (fun x => (x.1.1,w))
noncomputable def component {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (μ.restrict {x|x.2=v}).map Prod.fst
noncomputable def posterior {d N : ℕ} (μ : Measure (Ambient d × Fin N)) (v : Fin N) :
    Measure (Ambient d) := (component μ v univ)⁻¹ • component μ v
noncomputable def averagePhi {d N : ℕ} (μ : Measure (Ambient d × Fin N)) : ℝ :=
  ∑ v : Fin N, (component μ v univ).toReal * Phi (posterior μ v)

def CoercivityStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ ν : Measure (Ambient d), IsProbabilityMeasure ν → BoundedDensity ν →
      (1/2:ℝ)*(InformationTheory.klDiv ν (sphereProbability d)).toReal-C*d ≤ Phi ν) ∧
    Phi (sphereProbability d) ≤ (2*(d/16):ℕ)*Real.log 2 ∧
    (∀ (q : ℕ) (w : Fin q → ℝ), (∀ i,0 ≤ w i) → (∑ i,w i)=1 →
      ∀ ν : Fin q → Measure (Ambient d), (∀ i,IsProbabilityMeasure (ν i)) →
      (∀ i,BoundedDensity (ν i)) →
      Phi (∑ i,ENNReal.ofReal (w i) • ν i) ≤ ∑ i,w i*Phi (ν i))

def DriftStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, 1 ≤ N →
    Real.log N ≤ (d:ℝ)^2 → ∀ μ : Measure (Ambient d × Fin N), IsProbabilityMeasure μ →
    μ.map Prod.fst=sphereProbability d → ∀ rule : BlockRule d N,
      averagePhi (outgoingLaw μ rule) ≤ averagePhi μ+C*d

open Filter
open scoped Topology NNReal

end KernelPotential

end OAI
