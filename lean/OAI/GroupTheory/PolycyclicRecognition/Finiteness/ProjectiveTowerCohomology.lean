import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralProjectiveTower
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCompleteCohomologyAdditive

namespace OAI

/-! # Cohomology along a projective syzygy tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem cohomologyConnecting_projective_factor
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) {A : Rep.{0} ℤ G} (f : A ⟶ S.X₃)
    (hf : stableRepresentationClass _ _ f = 0) :
    (groupCohomology.functor ℤ G i).map f ≫ groupCohomology.δ hS i j hij = 0 := by
  let F := groupCohomology.functor ℤ G i
  let δ : F.obj S.X₃ ⟶ groupCohomology S.X₁ j := groupCohomology.δ hS i j hij
  change F.map f ≫ δ = 0
  let : Epi S.g := hS.epi_g
  obtain ⟨P, hP, u, v, huv⟩ := (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let : Projective P := hP
  let l := Projective.factorThru v S.g
  have hl : l ≫ S.g = v := Projective.factorThru_comp _ _
  have hz := (groupCohomology.mapShortComplex₃ hS hij).zero
  change F.map S.g ≫ δ = 0 at hz
  rw [← huv, ← hl, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc, hz, comp_zero, comp_zero]

namespace IntegralProjectiveTower

abbrev cohomologyStage (T : IntegralProjectiveTower G) (p n : ℕ) : Type :=
  groupCohomology (T.obj n) (n + p)

def connecting (T : IntegralProjectiveTower G) (p n : ℕ) :
    groupCohomology (T.obj n) (n + p) ⟶ groupCohomology (T.obj (n + 1)) (n + 1 + p) :=
  groupCohomology.δ (T.shortExact n) (n + p) (n + 1 + p) (by omega)

def forward (T : IntegralProjectiveTower G) (p i j : ℕ) (h : i ≤ j) :
    T.cohomologyStage p i →ₗ[ℤ] T.cohomologyStage p j where
  toFun := Nat.leRecOn h (fun {k} => (T.connecting p k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (T.connecting p j).hom.map_smul r _

instance (T : IntegralProjectiveTower G) (p : ℕ) :
    DirectedSystem (T.cohomologyStage p) (fun i j h => T.forward p i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

abbrev Cohomology (T : IntegralProjectiveTower G) (p : ℕ) :=
  Module.DirectLimit (T.cohomologyStage p) (T.forward p)

namespace Map
variable {T U : IntegralProjectiveTower G}

def stageMap (f : Map T U) (p n : ℕ) : T.cohomologyStage p n →ₗ[ℤ] U.cohomologyStage p n :=
  ((groupCohomology.functor ℤ G (n + p)).map (f.app n)).hom

theorem connecting_natural (f : Map T U) (p n : ℕ) :
    T.connecting p n ≫ (groupCohomology.functor ℤ G (n + 1 + p)).map (f.app (n + 1)) =
      (groupCohomology.functor ℤ G (n + p)).map (f.app n) ≫ U.connecting p n :=
  groupCohomology.δ_naturality (T.shortExact n) (U.shortExact n)
    (f.sequenceMap n) (n + p) (n + 1 + p) (by omega)

theorem forward_natural (f : Map T U) (p i j : ℕ) (h : i ≤ j) (x : T.cohomologyStage p i) :
    f.stageMap p j (T.forward p i j h x) = U.forward p i j h (f.stageMap p i x) := by
  induction h with
  | refl =>
    simp only [forward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change f.stageMap p (j + 1)
      (Nat.leRecOn (C := T.cohomologyStage p) _ (fun {k} => (T.connecting p k).hom) x) =
      Nat.leRecOn (C := U.cohomologyStage p) _ (fun {k} => (U.connecting p k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := ConcreteCategory.congr_hom (f.connecting_natural p j) (T.forward p i j h x)
    change f.stageMap p (j + 1) ((T.connecting p j).hom _) =
      (U.connecting p j).hom (f.stageMap p j (T.forward p i j h x)) at hn
    change f.stageMap p (j + 1) ((T.connecting p j).hom (T.forward p i j h x)) =
      (U.connecting p j).hom (U.forward p i j h (f.stageMap p i x))
    rw [hn, ih]

def cohomologyMap (f : Map T U) (p : ℕ) : T.Cohomology p →ₗ[ℤ] U.Cohomology p :=
  Module.DirectLimit.map (f := T.forward p) (f' := U.forward p) (f.stageMap p)
    (fun i j h => by apply LinearMap.ext; exact f.forward_natural p i j h)

@[simp]
theorem cohomologyMap_of (f : Map T U) (p n : ℕ) (x : T.cohomologyStage p n) :
    f.cohomologyMap p (Module.DirectLimit.of ℤ ℕ _ (T.forward p) n x) =
      Module.DirectLimit.of ℤ ℕ _ (U.forward p) n (f.stageMap p n x) :=
  Module.DirectLimit.map_apply_of (f.stageMap p)
    (fun i j h => by apply LinearMap.ext; exact f.forward_natural p i j h) x

end Map
end IntegralProjectiveTower
end PolycyclicRecognition

end

end OAI
