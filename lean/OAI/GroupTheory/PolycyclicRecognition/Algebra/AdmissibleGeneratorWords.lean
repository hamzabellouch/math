import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowAffinity
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes

namespace OAI

/-! # Generator words whose entire path stays in an open set -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {G V I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def generatorWordBase (U : Set G) (Exp : V → G) (X : I → V) :
    List (I × ℝ) → Set G
  | [] => U
  | (i, t) :: w => flowLineBase U Exp (t • X i) 1 ∩
      (fun g => g * Exp (t • X i)) ⁻¹' generatorWordBase U Exp X w

theorem isOpen_generatorWordBase (U : Set G) (hU : IsOpen U)
    (Exp : V → G) (hExp : Continuous Exp) (X : I → V) (w : List (I × ℝ)) :
    IsOpen (generatorWordBase U Exp X w) := by
  induction w with
  | nil => exact hU
  | cons p w ih =>
    exact (isOpen_flowLineBase U hU Exp hExp (p.2 • X p.1) 1).inter
      (ih.preimage (by fun_prop))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem generatorWordBase_subset (U : Set G) (Exp : V → G) (hExp0 : Exp 0 = 1)
    (X : I → V) (w : List (I × ℝ)) : generatorWordBase U Exp X w ⊆ U := by
  cases w with
  | nil => exact Subset.rfl
  | cons p w =>
    intro g hg
    simpa [hExp0] using hg.1 0 (show (0 : ℝ) ∈ Icc 0 1 by simp)

theorem eventually_short_flowLineBase
    {U : Set G} (hU : IsOpen U) {Exp : V → G} (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (v : V) {g : G} (hg : g ∈ U) :
    ∀ᶠ t in 𝓝 (0 : ℝ), g ∈ flowLineBase U Exp (t • v) 1 := by
  let F : ℝ → C(ℝ, G) := fun t =>
    ⟨fun r => g * Exp (r • (t • v)), by fun_prop⟩
  have hc : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ℝ => g * Exp (p.2 • (p.1 • v)))
    fun_prop
  have ho := ContinuousMap.continuous_compactOpen.mp hc
    (Icc (0 : ℝ) 1) isCompact_Icc U hU
  apply ho.mem_nhds
  intro r _hr
  simpa [F, hExp0] using hg

theorem eventually_prefix_generatorWordBase
    (U : Set G) (hU : IsOpen U) (Exp : V → G) (hExp : Continuous Exp)
    (hExp0 : Exp 0 = 1) (X : I → V) (w : List (I × ℝ))
    {g : G} (hg : g ∈ generatorWordBase U Exp X w) (i : I) :
    ∀ᶠ t in 𝓝 (0 : ℝ), g ∈ generatorWordBase U Exp X ((i, t) :: w) := by
  have ht : ∀ᶠ t in 𝓝 (0 : ℝ), g * Exp (t • X i) ∈ generatorWordBase U Exp X w := by
    have hc : Continuous (fun t : ℝ => g * Exp (t • X i)) := by fun_prop
    have hc0 : Tendsto (fun t : ℝ => g * Exp (t • X i)) (𝓝 0) (𝓝 g) := by
      simpa [hExp0] using hc.tendsto 0
    exact hc0.eventually ((isOpen_generatorWordBase U hU Exp hExp X w).mem_nhds hg)
  exact (eventually_short_flowLineBase hU hExp hExp0 (X i)
    (generatorWordBase_subset U Exp hExp0 X w hg)).and ht

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem eq_on_admissible_generatorWord
    {W : Type*} (f : G → W) (U : Set G) (Exp : V → G) (X : I → V)
    (hflow : ∀ (i : I) (g : G) (t : ℝ), g ∈ flowLineBase U Exp (t • X i) 1 →
      f (g * Exp (t • X i)) = f g)
    (w : List (I × ℝ)) {g : G} (hg : g ∈ generatorWordBase U Exp X w) :
    f (g * generatorGroupWord X Exp w) = f g := by
  induction w generalizing g with
  | nil => simp [generatorGroupWord]
  | cons p w ih =>
    rw [generatorGroupWord_cons, ← mul_assoc, ih hg.2, hflow p.1 g p.2 hg.1]

end PolycyclicRecognition

end

end OAI
