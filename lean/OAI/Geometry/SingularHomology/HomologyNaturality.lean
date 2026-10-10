import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realHomologyMap_eq_of_homotopy {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (H : ContinuousMap.Homotopy (continuousMapOf f hf) (continuousMapOf g hg)) :
    realHomologyMap n f hf = realHomologyMap n g hg := by
  have h := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat ℝ) (f := TopCat.ofHom (continuousMapOf f hf))
    (g := TopCat.ofHom (continuousMapOf g hg)) H (ModuleCat.of ℝ ℝ) n
  exact congrArg (fun k => k.hom) h

theorem realHomologyMap_homotopy_intertwines {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f : X → X} {g : Y → Y} {p : X → Y}
    (hf : Continuous f) (hg : Continuous g) (hp : Continuous p)
    (H : ContinuousMap.Homotopy (continuousMapOf (p ∘ f) (hp.comp hf))
      (continuousMapOf (g ∘ p) (hg.comp hp))) :
    (realHomologyMap n p hp).comp (realHomologyMap n f hf) =
      (realHomologyMap n g hg).comp (realHomologyMap n p hp) := by
  let T := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)
  have hpf : realHomologyMap n (p ∘ f) (hp.comp hf) =
      (realHomologyMap n p hp).comp (realHomologyMap n f hf) := by
    exact congrArg (fun k => k.hom)
      (T.map_comp (TopCat.ofHom (continuousMapOf f hf))
        (TopCat.ofHom (continuousMapOf p hp)))
  have hgp : realHomologyMap n (g ∘ p) (hg.comp hp) =
      (realHomologyMap n g hg).comp (realHomologyMap n p hp) := by
    exact congrArg (fun k => k.hom)
      (T.map_comp (TopCat.ofHom (continuousMapOf p hp))
        (TopCat.ofHom (continuousMapOf g hg)))
  rw [← hpf, ← hgp]
  exact realHomologyMap_eq_of_homotopy n (hp.comp hf) (hg.comp hp) H

theorem realHomologyMap_eq_of_homotopic {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (H : ContinuousMap.Homotopic (continuousMapOf f hf) (continuousMapOf g hg)) :
    realHomologyMap n f hf = realHomologyMap n g hg := by
  obtain ⟨H⟩ := H
  exact realHomologyMap_eq_of_homotopy n hf hg H

end Problem340

end

end OAI
