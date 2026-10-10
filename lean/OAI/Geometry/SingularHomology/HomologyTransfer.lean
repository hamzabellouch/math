import OAI.Geometry.SingularHomology.HomologyNaturality

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem realHomologyMap_id (n : ℕ) :
    realHomologyMap n (id : X → X) continuous_id = LinearMap.id := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map (𝟙 (TopCat.of X))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem realHomologyMap_comp (n : ℕ) (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) :
    realHomologyMap n (g ∘ f) (hg.comp hf) =
      (realHomologyMap n g hg).comp (realHomologyMap n f hf) := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)).map
      (TopCat.ofHom (continuousMapOf f hf) ≫ TopCat.ofHom (continuousMapOf g hg))).hom = _
  rw [Functor.map_comp]
  rfl

theorem realHomologyMap_surjective_of_section (n : ℕ)
    (p : X → Y) (s : Y → X) (hp : Continuous p) (hs : Continuous s)
    (hps : Function.LeftInverse p s) :
    Function.Surjective (realHomologyMap n p hp) := by
  intro v
  refine ⟨realHomologyMap n s hs v, ?_⟩
  have hcomp : p ∘ s = id := funext hps
  have hmap := realHomologyMap_comp n s p hs hp
  simp only [hcomp, realHomologyMap_id] at hmap
  exact congrArg (fun k => k v) hmap.symm

theorem realHomologyMap_injective_of_retraction (n : ℕ)
    (s : Y → X) (p : X → Y) (hs : Continuous s) (hp : Continuous p)
    (hps : Function.LeftInverse p s) :
    Function.Injective (realHomologyMap n s hs) := by
  have hcomp : p ∘ s = id := funext hps
  have hmap := realHomologyMap_comp n s p hs hp
  simp only [hcomp, realHomologyMap_id] at hmap
  apply Function.LeftInverse.injective (g := realHomologyMap n p hp)
  intro v
  exact congrArg (fun k => k v) hmap.symm

theorem realHomologyMap_eigenvector_of_section_homotopy (n : ℕ)
    (f : X → X) (g : Y → Y) (s : Y → X) (p : X → Y)
    (hf : Continuous f) (hg : Continuous g) (hs : Continuous s) (hp : Continuous p)
    (hps : Function.LeftInverse p s)
    (H : ContinuousMap.Homotopy
      (continuousMapOf (f ∘ s) (hf.comp hs))
      (continuousMapOf (s ∘ g) (hs.comp hg)))
    (c : ℝ) (v : RealSingularHomology n Y) (hv : v ≠ 0)
    (heig : realHomologyMap n g hg v = c • v) :
    ∃ w : RealSingularHomology n X, w ≠ 0 ∧ realHomologyMap n f hf w = c • w := by
  refine ⟨realHomologyMap n s hs v, ?_, ?_⟩
  · intro hzero
    apply hv
    apply realHomologyMap_injective_of_retraction n s p hs hp hps
    simpa using hzero
  · have hmap := realHomologyMap_eq_of_homotopy n (hf.comp hs) (hs.comp hg) H
    rw [realHomologyMap_comp n s f hs hf, realHomologyMap_comp n g s hg hs] at hmap
    have heq := congrArg (fun k => k v) hmap
    simpa [heig] using heq

end Problem340

end

end OAI
