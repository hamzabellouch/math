import Mathlib

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

abbrev ClockAmbient := EuclideanSpace ℝ (Fin 2)

abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)

abbrev StandardClock := Metric.sphere (0 : ClockAmbient) (1 : ℝ)

abbrev StandardSphere2 := Metric.sphere (0 : SphereAmbient) (1 : ℝ)

abbrev CounterexampleManifold (q : ℕ) :=
  StandardClock × (Fin (q + 1) → StandardSphere2)

abbrev CounterexampleAmbient (q : ℕ) :=
  ClockAmbient × (Fin (q + 1) → SphereAmbient)

def standardEmbedding (q : ℕ) :
    CounterexampleManifold q → CounterexampleAmbient q :=
  fun x => (x.1.1, fun i => (x.2 i).1)

def IsC1SelfMap (q : ℕ) (f : CounterexampleManifold q → CounterexampleManifold q) : Prop :=
  Continuous f ∧
    ∀ x : CounterexampleManifold q,
      ∃ U : Set (CounterexampleAmbient q),
        IsOpen U ∧ standardEmbedding q x ∈ U ∧
          ∃ F : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 F U ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ U →
                  standardEmbedding q (f y) = F (standardEmbedding q y)

def continuousMapOf {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : ContinuousMap X Y :=
  ⟨f, hf⟩

abbrev RealSingularHomology (n : ℕ) (X : Type) [TopologicalSpace X] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).obj (TopCat.of X))

def realHomologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : X → Y) (hf : Continuous f) :
    RealSingularHomology n X →ₗ[ℝ] RealSingularHomology n Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map
      (TopCat.ofHom (continuousMapOf f hf))).hom

def totalRealHomologySpectralRadius {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) : ℝ :=
  sSup {r : ℝ |
    ∃ n : ℕ, ∃ a b : ℝ,
      ∃ u v : RealSingularHomology n X,
        (u ≠ 0 ∨ v ≠ 0) ∧
        realHomologyMap n f hf u = a • u - b • v ∧
        realHomologyMap n f hf v = b • u + a • v ∧
        r = Real.sqrt (a ^ 2 + b ^ 2)}

theorem exists_C1_entropy_counterexample :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  sorry

end Problem340

end

end OAI
