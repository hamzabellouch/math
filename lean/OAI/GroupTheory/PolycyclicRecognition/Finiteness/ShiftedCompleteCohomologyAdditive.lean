import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCompleteCohomologyVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyAdditive

namespace OAI

/-! # Additivity in nonnegative complete-cohomology degrees -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomology_connecting_zero_of_projective_factor_of_eq
    {U V : Rep.{0} ℤ G} (i j : ℕ) (h : i + 1 = j) (f : U ⟶ V)
    (hf : stableRepresentationClass U V f = 0) :
    (groupCohomology.functor ℤ G i).map f ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact V) i j h = 0 := by
  subst j
  exact cohomology_connecting_zero_of_projective_factor i f hf

theorem shiftedCompletedCohomologyMap_add (p : ℕ) {A B : Rep.{0} ℤ G} (f g : A ⟶ B) :
    shiftedCompletedCohomologyMap p (f + g) = shiftedCompletedCohomologyMap p f + shiftedCompletedCohomologyMap p g := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let F := iteratedNormalizedSyzygy (G := G) n
  let H := groupCohomology.functor ℤ G (n + p)
  let a := F.map (f + g)
  let b := F.map f + F.map g
  have he : stableRepresentationClass _ _ a = stableRepresentationClass _ _ b := by
    change stableRepresentationClass _ _ (F.map (f + g)) = _
    rw [← normalizedStableSyzygyIterate_class n (f + g), map_add, map_add,
      normalizedStableSyzygyIterate_class, normalizedStableSyzygyIterate_class, map_add]
  have hd : stableRepresentationClass _ _ (a - b) = 0 := by
    rw [map_sub, he, sub_self]
  have hδ := cohomology_connecting_zero_of_projective_factor_of_eq (n + p) (n + 1 + p) (by omega) (a - b) hd
  have hstep : (shiftedSyzygyConnecting p B n).hom
      (shiftedCohomologyStageMap p (f + g) n z -
        (shiftedCohomologyStageMap p f n z + shiftedCohomologyStageMap p g n z)) = 0 := by
    have hz := ConcreteCategory.congr_hom hδ z
    change (shiftedSyzygyConnecting p B n).hom ((H.map (a - b)).hom z) = 0 at hz
    have hm : H.map (a - b) = H.map a - (H.map (F.map f) + H.map (F.map g)) := by
      simp only [b, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_add]
    rw [hm] at hz
    exact hz
  let w := shiftedCohomologyStageMap p (f + g) n z -
    (shiftedCohomologyStageMap p f n z + shiftedCohomologyStageMap p g n z)
  have hw : shiftedCohomologyForward p B n (n + 1) (Nat.le_succ n) w = 0 := by
    change Nat.leRecOn (C := shiftedCohomologyStage p B) (Nat.le_succ n)
      (fun {k} => (shiftedSyzygyConnecting p B k).hom) w = 0
    rw [Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
    exact hstep
  have hc := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := shiftedCohomologyStage p B) (f := shiftedCohomologyForward p B)
    (hij := Nat.le_succ n) (x := w)
  rw [hw, map_zero] at hc
  change shiftedCompletedCohomologyMap p (f + g) _ = shiftedCompletedCohomologyMap p f _ + shiftedCompletedCohomologyMap p g _
  simp only [shiftedCompletedCohomologyMap_of]
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  exact hc.symm

instance shiftedCompletedCohomologyFunctor_additive (p : ℕ) :
    (shiftedCompletedCohomologyFunctor p (G := G)).Additive where
  map_add {A B f g} := by
    apply ModuleCat.hom_ext
    exact shiftedCompletedCohomologyMap_add p f g


end PolycyclicRecognition

end

end OAI
