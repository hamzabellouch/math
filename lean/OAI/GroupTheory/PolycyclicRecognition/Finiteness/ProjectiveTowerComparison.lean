import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTowerCohomology

namespace OAI

/-! # Independence of the projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace IntegralProjectiveTower
namespace Map
variable {T U V : IntegralProjectiveTower G}

theorem cohomologyMap_identity (T : IntegralProjectiveTower G) (p : ℕ) :
    (identity T).cohomologyMap p = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [cohomologyMap_of]
  change Module.DirectLimit.of ℤ ℕ _ (T.forward p) n
    (((groupCohomology.functor ℤ G (n + p)).map (𝟙 (T.obj n))).hom z) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cohomologyMap_comp (f : Map T U) (g : Map U V) (p : ℕ) :
    (f.comp g).cohomologyMap p = (g.cohomologyMap p).comp (f.cohomologyMap p) := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  simp only [cohomologyMap_of, LinearMap.comp_apply]
  change Module.DirectLimit.of ℤ ℕ _ (V.forward p) n
    (((groupCohomology.functor ℤ G (n + p)).map (f.app n ≫ g.app n)).hom z) = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

theorem cohomologyMap_eq_of_stable_eq (f g : Map T U)
    (h : stableRepresentationClass _ _ (f.app 0) = stableRepresentationClass _ _ (g.app 0))
    (p : ℕ) : f.cohomologyMap p = g.cohomologyMap p := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  have hs : stableRepresentationClass _ _ (f.app n - g.app n) = 0 := by
    rw [map_sub, f.stable_eq g h n, sub_self]
  have hc := cohomologyConnecting_projective_factor (U.sequence n) (U.shortExact n)
    (n + p) (n + 1 + p) (by omega) (f.app n - g.app n) hs
  have hz := ConcreteCategory.congr_hom hc z
  change (U.connecting p n).hom
    (((groupCohomology.functor ℤ G (n + p)).map (f.app n - g.app n)).hom z) = 0 at hz
  rw [CategoryTheory.Functor.map_sub] at hz
  have hstep : U.forward p n (n + 1) (Nat.le_succ n)
      (f.stageMap p n z - g.stageMap p n z) = 0 := by
    change Nat.leRecOn (C := U.cohomologyStage p) (Nat.le_succ n)
      (fun {k} => (U.connecting p k).hom) _ = 0
    rw [Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
    exact hz
  have he := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ) (G := U.cohomologyStage p)
    (f := U.forward p) (hij := Nat.le_succ n) (x := f.stageMap p n z - g.stageMap p n z)
  rw [hstep, map_zero] at he
  rw [cohomologyMap_of, cohomologyMap_of, ← sub_eq_zero, ← map_sub]
  exact he.symm

end Map

def cohomologyEquiv {T U : IntegralProjectiveTower G} (e : T.obj 0 ≅ U.obj 0) (p : ℕ) :
    T.Cohomology p ≃ₗ[ℤ] U.Cohomology p := by
  let f := liftMap T U e.hom
  let g := liftMap U T e.inv
  refine LinearEquiv.ofLinearMap (f.cohomologyMap p) (g.cohomologyMap p) ?_ ?_
  · rw [← Map.cohomologyMap_comp]
    have h : stableRepresentationClass _ _ ((g.comp f).app 0) =
        stableRepresentationClass _ _ ((Map.identity U).app 0) := by
      change stableRepresentationClass _ _ (e.inv ≫ e.hom) = stableRepresentationClass _ _ (𝟙 _)
      rw [e.inv_hom_id]
    rw [Map.cohomologyMap_eq_of_stable_eq (g.comp f) (Map.identity U) h, Map.cohomologyMap_identity]
  · rw [← Map.cohomologyMap_comp]
    have h : stableRepresentationClass _ _ ((f.comp g).app 0) =
        stableRepresentationClass _ _ ((Map.identity T).app 0) := by
      change stableRepresentationClass _ _ (e.hom ≫ e.inv) = stableRepresentationClass _ _ (𝟙 _)
      rw [e.hom_inv_id]
    rw [Map.cohomologyMap_eq_of_stable_eq (f.comp g) (Map.identity T) h, Map.cohomologyMap_identity]

end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
