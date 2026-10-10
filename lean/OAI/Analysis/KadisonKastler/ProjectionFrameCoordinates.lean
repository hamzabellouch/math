import OAI.Analysis.KadisonKastler.ProjectionRangeFrame

namespace OAI

/-! # Fixed Hilbert coordinates on each measurable rank stratum -/

namespace KadisonKastler

open MeasureTheory InnerProductSpace

noncomputable section

/-- Increasing enumeration identifies a finite rank stratum with `Fin n`. -/
def finiteFrameIndexEquiv (p : ℕ → Prop) (n : ℕ)
    (h : ∀ k, frameIndexAvailable p k ↔ k < n) : Fin n ≃ {m // p m} :=
  (show Fin n ≃ {k // frameIndexAvailable p k} from {
    toFun := fun i => ⟨i, (h i).mpr i.isLt⟩
    invFun := fun i => ⟨i, (h i).mp i.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (frameIndexEquiv p)

/-- Increasing enumeration identifies an infinite rank stratum with `ℕ`. -/
def infiniteFrameIndexEquiv (p : ℕ → Prop) (h : ∀ k, frameIndexAvailable p k) :
    ℕ ≃ {m // p m} :=
  (show ℕ ≃ {k // frameIndexAvailable p k} from {
    toFun := fun i => ⟨i, h i⟩
    invFun := fun i => i
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }).trans (frameIndexEquiv p)

@[simp] theorem finiteFrameIndexEquiv_val (p : ℕ → Prop) (n : ℕ)
    (h : ∀ k, frameIndexAvailable p k ↔ k < n) (i : Fin n) :
    (finiteFrameIndexEquiv p n h i).val = Nat.nth p i := rfl

@[simp] theorem infiniteFrameIndexEquiv_val (p : ℕ → Prop)
    (h : ∀ k, frameIndexAvailable p k) (i : ℕ) :
    (infiniteFrameIndexEquiv p h i).val = Nat.nth p i := rfl

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Reindex a Hilbert basis while retaining its concrete vectors. -/
def reindexedHilbertBasis (b : HilbertBasis I ℂ H) (e : J ≃ I) : HilbertBasis J ℂ H :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    rw [e.surjective.range_comp b, b.dense_span])

@[simp] theorem reindexedHilbertBasis_apply (b : HilbertBasis I ℂ H) (e : J ≃ I) (j : J) :
    reindexedHilbertBasis b e j = b (e j) := by
  simp only [reindexedHilbertBasis, HilbertBasis.coe_mk, Function.comp_apply]

variable {X : Type*} (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)

/-- The finite-dimensional coordinate basis on the rank `n` stratum. -/
def finiteProjectionBasis (n : ℕ) (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) (n + 1)) :
    HilbertBasis (Fin n) ℂ (P x).range := by
  letI : CompleteSpace (P x).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x)).completeSpace_coe
  exact reindexedHilbertBasis (projectionRangeHilbertBasis (P x) (hP x) b hb)
    (finiteFrameIndexEquiv _ n (frameDimensionStratum_finite_iff _ hx))

/-- The infinite-dimensional coordinate basis on the infinite rank stratum. -/
def infiniteProjectionBasis (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) 0) :
    HilbertBasis ℕ ℂ (P x).range := by
  letI : CompleteSpace (P x).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hP x)).completeSpace_coe
  exact reindexedHilbertBasis (projectionRangeHilbertBasis (P x) (hP x) b hb)
    (infiniteFrameIndexEquiv _ hx)

@[simp] theorem finiteProjectionBasis_coe (n : ℕ) (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) (n + 1))
    (i : Fin n) :
    (finiteProjectionBasis P hP b hb n x hx i : H) = enumeratedProjectionFrame P b x i := by
  simp only [finiteProjectionBasis, reindexedHilbertBasis_apply,
    projectionRangeHilbertBasis_apply, projectionRangeFrame,
    enumeratedProjectionFrame, measurableProjectionFrame]
  rfl

@[simp] theorem infiniteProjectionBasis_coe (x : X)
    (hx : x ∈ frameDimensionStratum (fun x i => measurableProjectionFrame P b x i ≠ 0) 0)
    (i : ℕ) :
    (infiniteProjectionBasis P hP b hb x hx i : H) = enumeratedProjectionFrame P b x i := by
  simp only [infiniteProjectionBasis, reindexedHilbertBasis_apply,
    projectionRangeHilbertBasis_apply, projectionRangeFrame,
    enumeratedProjectionFrame, measurableProjectionFrame]
  rfl

end

end KadisonKastler

end OAI
