import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology

namespace OAI

section

/-! # Gluing the geometric horn into its actual realization -/

namespace Thomason.Construction.HornBarycentric

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

def faceRegion {n : ℕ} (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) :
    Set (horn i) := {x | x.val.weights j.val = 0}

theorem faceRegion_closed {n : ℕ} (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) :
    IsClosed (faceRegion i j) :=
  isClosed_eq ((StdSimplex.continuous_weights_apply ℝ j.val).comp continuous_subtype_val)
    continuous_const

theorem faceRegion_cover {n : ℕ} (i : Fin (n+2)) :
    (⋃ j, faceRegion i j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j, hj, hz⟩ := x.property
  exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hz⟩

/-- A continuous chart on each closed face. -/
def faceChart {n : ℕ} (i : Fin (n+2)) (j : {j : Fin (n+2) // j ≠ i}) :
    C(faceRegion i j, SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) where
  toFun x := faceValue i j.val j.property x.val.val
  continuous_toFun := by
    apply (RealizationPrism.leg (Λ[n+1, i] : SSet.{0})
      (faceIndex i j.val j.property)).hom.continuous.comp
    apply continuous_uliftUp.comp
    exact (StdSimplex.continuous_map ℝ (deletion j.val)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

theorem faceChart_overlap {n : ℕ} (i : Fin (n+2))
    (j k : {j : Fin (n+2) // j ≠ i}) (x : horn i)
    (hj : x ∈ faceRegion i j) (hk : x ∈ faceRegion i k) :
    faceChart i j ⟨x, hj⟩ = faceChart i k ⟨x, hk⟩ :=
  faceValue_overlap i j.val k.val j.property k.property x.val hj hk

/-- The continuous map from the geometric horn to the actual realization. -/
def toRealization {n : ℕ} (i : Fin (n+2)) :
    C(horn i, SSet.toTop.obj (Λ[n+1, i] : SSet.{0})) where
  toFun := Set.liftCover (faceRegion i) (fun j => faceChart i j)
    (faceChart_overlap i) (faceRegion_cover i)
  continuous_toFun := by
    apply (locallyFinite_of_finite (faceRegion i)).continuous
      (faceRegion_cover i) (faceRegion_closed i)
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (faceRegion i j).domRestrict
        (Set.liftCover (faceRegion i) (fun j => faceChart i j)
          (faceChart_overlap i) (faceRegion_cover i)) = faceChart i j := by
      funext x
      exact Set.liftCover_coe x
    rw [he]
    exact (faceChart i j).continuous

theorem toRealization_face {n : ℕ} (i j : Fin (n+2)) (hj : j ≠ i)
    (x : horn i) (hx : x.val.weights j = 0) :
    toRealization i x = faceValue i j hj x.val := by
  change Set.liftCover (faceRegion i) (fun j => faceChart i j)
    (faceChart_overlap i) (faceRegion_cover i) x = _
  exact Set.liftCover_of_mem (S := faceRegion i) (f := fun j => faceChart i j)
    (hf := faceChart_overlap i) (hS := faceRegion_cover i) (i := ⟨j, hj⟩) hx

end

end Thomason.Construction.HornBarycentric

end

end OAI
