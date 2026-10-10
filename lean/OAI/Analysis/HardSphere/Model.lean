import OAI.Analysis.HardSphere.CondensationDefinitions

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere

abbrev HilbertJet (N : ℕ) (L : Length) :=
  PiLp 2 (fun _ : Option (Direction N) ↦ ScalarL2 N L)

def Condensation : Prop :=
  ∃ ε₀ c₀ : ℝ, 0 < ε₀ ∧ 0 < c₀ ∧
    ∀ (a ρ : ℝ), 0 < a → 0 < ρ → ρ * a ^ 3 < ε₀ →
    ∀ (N : ℕ → ℕ) (L : ℕ → Length) (hN : ∀ k, 0 < N k),
      Tendsto N atTop atTop →
      Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k : ℝ) / (L k).val ^ 3) atTop (𝓝 ρ) →
      ∀ (Ψ : (k : ℕ) → Jet (N k) (L k)),
        (∀ k, IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀ ≤ Filter.liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop

lemma scalarL2_norm_exponent : Fact (1 ≤ (2 : ℝ≥0∞)) := inferInstance

attribute [local instance] scalarL2_norm_exponent

abbrev scalarL2_normedAddCommGroup (N : ℕ) (L : Length) :
    NormedAddCommGroup (ScalarL2 N L) := inferInstance

attribute [local instance] scalarL2_normedAddCommGroup

abbrev scalarL2_addCommMonoid (N : ℕ) (L : Length) : AddCommMonoid (ScalarL2 N L) :=
  (scalarL2_normedAddCommGroup N L).toAddCommMonoid

abbrev scalarL2_innerProductSpace (N : ℕ) (L : Length) :
    InnerProductSpace ℂ (ScalarL2 N L) := inferInstance

attribute [local instance] scalarL2_innerProductSpace

abbrev scalarL2_module (N : ℕ) (L : Length) : Module ℂ (ScalarL2 N L) :=
  (scalarL2_innerProductSpace N L).toNormedSpace.toModule

attribute [local instance] scalarL2_module

lemma scalarL2_completeSpace (N : ℕ) (L : Length) : CompleteSpace (ScalarL2 N L) :=
  inferInstance

end HardSphere
end
end
end

end OAI
