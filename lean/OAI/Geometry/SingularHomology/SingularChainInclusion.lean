import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realSingularChainMap_injective
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) (n : ℕ) :
    Function.Injective ((realSingularChainMap f hf).f n).hom := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℝ)).obj
    (ModuleCat.of ℝ ℝ)
  let g : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom (continuousMapOf f hf)
  have : Mono g := (TopCat.mono_iff_injective g).mpr hinj
  have : Mono (F.map g) := inferInstance
  exact (ModuleCat.mono_iff_injective ((F.map g).f n)).mp inferInstance

theorem realSingularChainMap_d
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (n m : ℕ)
    (z : (realSingularChainComplex X).X n) :
    ((realSingularChainComplex Y).d n m).hom
        (((realSingularChainMap f hf).f n).hom z) =
      ((realSingularChainMap f hf).f m).hom
        (((realSingularChainComplex X).d n m).hom z) := by
  exact congrArg (fun k : (realSingularChainComplex X).X n ⟶
      (realSingularChainComplex Y).X m => k.hom z)
    ((realSingularChainMap f hf).comm n m)

theorem realSingularChainMap_cycle_iff
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) (n m : ℕ)
    (z : (realSingularChainComplex X).X n) :
    ((realSingularChainComplex Y).d n m).hom
        (((realSingularChainMap f hf).f n).hom z) = 0 ↔
      ((realSingularChainComplex X).d n m).hom z = 0 := by
  rw [realSingularChainMap_d]
  exact map_eq_zero_iff _ (realSingularChainMap_injective f hf hinj m)

theorem realSingularChainMap_exists_cycle_lift
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f) (n m : ℕ)
    (z : (realSingularChainComplex Y).X n)
    (hz : ((realSingularChainComplex Y).d n m).hom z = 0)
    (hs : z ∈ LinearMap.range ((realSingularChainMap f hf).f n).hom) :
    ∃ w : (realSingularChainComplex X).X n,
      ((realSingularChainComplex X).d n m).hom w = 0 ∧
      ((realSingularChainMap f hf).f n).hom w = z := by
  obtain ⟨w, hw⟩ := hs
  refine ⟨w, ?_, hw⟩
  apply (realSingularChainMap_cycle_iff f hf hinj n m w).mp
  rw [hw]
  exact hz

end Problem340

end

end OAI
