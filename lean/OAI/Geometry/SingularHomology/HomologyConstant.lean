import OAI.Geometry.SingularHomology.HomologyNaturality

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

theorem realSingularHomology_subsingleton_of_totallyDisconnected
    (n : ℕ) (hn : n ≠ 0) (X : Type) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : Subsingleton (RealSingularHomology n X) := by
  exact ModuleCat.subsingleton_of_isZero
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℝ) n (ModuleCat.of ℝ ℝ) (TopCat.of X) hn)

theorem realHomologyMap_const
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (y : Y) :
    realHomologyMap n (fun _ : X => y) continuous_const = 0 := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)
  let a : TopCat.of X ⟶ TopCat.of PUnit :=
    TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let b : TopCat.of PUnit ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have hz : CategoryTheory.Limits.IsZero (H.obj (TopCat.of PUnit)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℝ) n (ModuleCat.of ℝ ℝ) (TopCat.of PUnit) hn
  have hb : H.map b = 0 := hz.eq_zero_of_src (H.map b)
  change (H.map (a ≫ b)).hom = 0
  rw [Functor.map_comp, hb, Limits.comp_zero, ModuleCat.hom_zero]

theorem realHomologyMap_eq_zero_of_nullhomotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (hn : n ≠ 0) (f : X → Y) (hf : Continuous f)
    (h : (continuousMapOf f hf).Nullhomotopic) : realHomologyMap n f hf = 0 := by
  obtain ⟨y, hy⟩ := h
  exact (realHomologyMap_eq_of_homotopic n hf continuous_const hy).trans
    (realHomologyMap_const n hn y)

theorem realSingularHomology_subsingleton_of_contractible
    (n : ℕ) (hn : n ≠ 0) (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : Subsingleton (RealSingularHomology n X) := by
  have hz : realHomologyMap n (id : X → X) continuous_id = 0 :=
    realHomologyMap_eq_zero_of_nullhomotopic n hn id continuous_id (id_nullhomotopic X)
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℝ) n).obj
    (ModuleCat.of ℝ ℝ)
  have hid : realHomologyMap n (id : X → X) continuous_id = LinearMap.id :=
    congrArg (fun k => k.hom) (H.map_id (TopCat.of X))
  have hid0 : (LinearMap.id : RealSingularHomology n X →ₗ[ℝ]
      RealSingularHomology n X) = 0 := hid.symm.trans hz
  constructor
  intro x y
  have hx := LinearMap.congr_fun hid0 x
  have hy := LinearMap.congr_fun hid0 y
  exact hx.trans hy.symm

theorem realHomologyMap_comp_eq_zero_of_contractible
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [ContractibleSpace Y] (n : ℕ) (hn : n ≠ 0)
    (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    realHomologyMap n (g ∘ f) (hg.comp hf) = 0 := by
  apply realHomologyMap_eq_zero_of_nullhomotopic n hn (g ∘ f) (hg.comp hf)
  exact ((id_nullhomotopic Y).comp_left (continuousMapOf f hf)).comp_right
    (continuousMapOf g hg)

end Problem340

end

end OAI
