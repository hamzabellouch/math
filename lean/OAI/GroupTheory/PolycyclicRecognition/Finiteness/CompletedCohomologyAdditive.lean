import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedStableSyzygyMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCompleteIdentity

namespace OAI

/-! # Additivity of complete cohomology

The free-cover construction is nonlinear, but its error is a projective factor.
The next connecting homomorphism kills that error, so the limit is additive.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomology_connecting_zero_of_projective_factor
    {U V : Rep.{0} ℤ G} (n : ℕ) (f : U ⟶ V)
    (hf : stableRepresentationClass U V f = 0) :
    (groupCohomology.functor ℤ G n).map f ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact V) n (n + 1) rfl = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let := hP
  let F := groupCohomology.functor ℤ G n
  let δ : F.obj V ⟶ groupCohomology (normalizedSyzygy V) (n + 1) :=
    groupCohomology.δ (normalizedSyzygySequence_shortExact V) n (n + 1) rfl
  change F.map f ≫ δ = 0
  have hn := groupCohomology.δ_naturality (normalizedSyzygySequence_shortExact P)
    (normalizedSyzygySequence_shortExact V) (normalizedSyzygySequenceMap v) n (n + 1) rfl
  rw [normalizedSyzygy_delta_eq_zero P n, zero_comp] at hn
  change 0 = F.map v ≫ δ at hn
  rw [← huv, CategoryTheory.Functor.map_comp, Category.assoc, ← hn, comp_zero]

theorem completedCohomologyMap_add {A B : Rep.{0} ℤ G} (f g : A ⟶ B) :
    completedCohomologyMap (f + g) = completedCohomologyMap f + completedCohomologyMap g := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  let F := iteratedNormalizedSyzygy (G := G) n
  let H := groupCohomology.functor ℤ G n
  let a := F.map (f + g)
  let b := F.map f + F.map g
  have he : stableRepresentationClass _ _ a = stableRepresentationClass _ _ b := by
    change stableRepresentationClass _ _ (F.map (f + g)) = _
    rw [← normalizedStableSyzygyIterate_class n (f + g), map_add, map_add,
      normalizedStableSyzygyIterate_class, normalizedStableSyzygyIterate_class, map_add]
  have hd : stableRepresentationClass _ _ (a - b) = 0 := by
    rw [map_sub, he, sub_self]
  have hδ := cohomology_connecting_zero_of_projective_factor n (a - b) hd
  have hstep : (normalizedSyzygyConnecting B n).hom
      (normalizedCohomologyStageMap (f + g) n z -
        (normalizedCohomologyStageMap f n z + normalizedCohomologyStageMap g n z)) = 0 := by
    have hz := ConcreteCategory.congr_hom hδ z
    change (normalizedSyzygyConnecting B n).hom ((H.map (a - b)).hom z) = 0 at hz
    have hm : H.map (a - b) = H.map a - (H.map (F.map f) + H.map (F.map g)) := by
      simp only [b, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_add]
    rw [hm] at hz
    exact hz
  let w := normalizedCohomologyStageMap (f + g) n z -
    (normalizedCohomologyStageMap f n z + normalizedCohomologyStageMap g n z)
  have hw : normalizedCohomologyForward B n (n + 1) (Nat.le_succ n) w = 0 := by
    change Nat.leRecOn (C := normalizedCohomologyStage B) (Nat.le_succ n)
      (fun {k} => (normalizedSyzygyConnecting B k).hom) w = 0
    rw [Nat.leRecOn_succ (le_refl n), Nat.leRecOn_self]
    exact hstep
  have hc := Module.DirectLimit.of_f (R := ℤ) (ι := ℕ)
    (G := normalizedCohomologyStage B) (f := normalizedCohomologyForward B)
    (hij := Nat.le_succ n) (x := w)
  rw [hw, map_zero] at hc
  change completedCohomologyMap (f + g) _ = completedCohomologyMap f _ + completedCohomologyMap g _
  simp only [completedCohomologyMap_of]
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  exact hc.symm

instance completedCohomologyFunctor_additive :
    (completedCohomologyFunctor (G := G)).Additive where
  map_add {A B f g} := by
    apply ModuleCat.hom_ext
    exact completedCohomologyMap_add f g

end PolycyclicRecognition

end

end OAI
