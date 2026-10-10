import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

section SupportCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A nonzero real functional has full range. -/
theorem real_functional_surjective (ell : E →L[ℝ] ℝ) (hne : ell ≠ 0) :
    Function.Surjective ell := by
  have hx : ∃ x, ell x ≠ 0 := by
    by_contra h
    apply hne
    ext x
    simpa using not_exists.mp h x
  obtain ⟨x, hx⟩ := hx
  intro r
  refine ⟨(r / ell x) • x, ?_⟩
  simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]

/- A nonzero support is strictly positive at every interior point. -/
theorem support_pos_of_interior {F : Set E} (ell : E →L[ℝ] ℝ) (hne : ell ≠ 0)
    (hs : ∀ y ∈ F, 0 ≤ ell y) {w : E} (hw : w ∈ interior F) : 0 < ell w := by
  have hopen : IsOpen (ell '' interior F) :=
    ell.toLinearMap.isOpenMap_of_finiteDimensional (real_functional_surjective ell hne) _ isOpen_interior
  have hi : ell w ∈ interior (Set.Ici (0 : ℝ)) := by
    apply hopen.subset_interior_iff.mpr ?_ ⟨w, hw, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    exact hs x (interior_subset hx)
  simpa only [interior_Ici, Set.mem_Ioi] using hi

variable [FiniteDimensional ℝ E]

/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/
def splitFunctionalEquiv (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) :
    E ≃L[ℝ] ℝ × ell.ker :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => (ell x, ⟨x - (ell x) • w, by simp [hw]⟩)
    invFun := fun p => p.1 • w + p.2
    left_inv := by intro x; simp
    right_inv := by
      rintro ⟨r, z⟩
      have hz : ell z = 0 := z.property
      ext
      · simp [hw, hz]
      · simp [hw, hz]
    map_add' := by
      intro x y
      ext
      · simp
      · simp [add_smul]; abel
    map_smul' := by
      intro a x
      ext
      · simp
      · simp [smul_sub, smul_smul] }

@[simp] theorem splitFunctionalEquiv_fst (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) (x : E) :
    (splitFunctionalEquiv ell w hw x).1 = ell x := rfl

@[simp] theorem splitFunctionalEquiv_w (ell : E →L[ℝ] ℝ) (w : E) (hw : ell w = 1) :
    splitFunctionalEquiv ell w hw w = (1, 0) := by
  ext <;> simp [splitFunctionalEquiv, hw]

/- Coordinates which keep the support as the first coordinate and send a
chosen interior point of a convex fiber to (1,0). Scaling the support, rather
than translating the body, preserves the ambient origin and all recession rays. -/
theorem exists_support_coordinates {m : ℕ} {F : Set (Space m)}
    (hi : (interior F).Nonempty) (ell : Space m →L[ℝ] ℝ) (hne : ell ≠ 0)
    (hs : ∀ y ∈ F, 0 ≤ ell y) :
    ∃ (d : ℕ) (A : Space m ≃L[ℝ] ℝ × Space d),
      m = d + 1 ∧ (∀ y ∈ F, 0 ≤ (A y).1) ∧
      (1, 0) ∈ interior (A '' F) := by
  classical
  obtain ⟨w, hw⟩ := hi
  have hp := support_pos_of_interior ell hne hs hw
  let f : Space m →L[ℝ] ℝ := (ell w)⁻¹ • ell
  have hwf : f w = 1 := by simp [f, hp.ne']
  let d := Module.finrank ℝ f.ker
  let L : f.ker ≃L[ℝ] Space d :=
    (stdOrthonormalBasis ℝ f.ker).repr.toContinuousLinearEquiv
  let A : Space m ≃L[ℝ] ℝ × Space d :=
    (splitFunctionalEquiv f w hwf).trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L)
  have hAw : A w = (1, 0) := by simp [A]
  refine ⟨d, A, ?_, ?_, ?_⟩
  · have he := A.toLinearEquiv.finrank_eq
    simpa [Module.finrank_prod, d, add_comm] using he
  · intro y hy
    change 0 ≤ (ell w)⁻¹ * ell y
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hs y hy)
  · have himage : A w ∈ A.toHomeomorph '' interior F := ⟨w, hw, rfl⟩
    rw [A.toHomeomorph.image_interior] at himage
    simpa [hAw] using himage

end SupportCoordinates

/- Append one real base coordinate, placing it first in Fin (k+1). -/
def extendBaseEquiv (k : ℕ) : (Space k × ℝ) ≃L[ℝ] Space (k+1) :=
  (((ContinuousLinearEquiv.prodComm ℝ (Space k) ℝ).trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin k) ℝ))).trans
      (Fin.consLinearEquiv ℝ (fun _ : Fin (k+1) => ℝ)).toContinuousLinearEquiv).trans
    (EuclideanSpace.equiv (Fin (k+1)) ℝ).symm

def reorderThinEquiv (k d : ℕ) : (Space k × (ℝ × Space d)) ≃L[ℝ] (Space (k+1) × Space d) :=
  (ContinuousLinearEquiv.prodAssoc ℝ (Space k) ℝ (Space d)).symm.trans
    ((extendBaseEquiv k).prodCongr (ContinuousLinearEquiv.refl ℝ (Space d)))

@[simp] theorem reorderThin_zero {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (reorderThinEquiv k d p).1 0 = p.2.1 := rfl

@[simp] theorem reorderThin_succ {k d : ℕ} (p : Space k × (ℝ × Space d)) (i : Fin k) :
    (reorderThinEquiv k d p).1 i.succ = p.1 i := rfl

@[simp] theorem reorderThin_snd {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (reorderThinEquiv k d p).2 = p.2.2 := rfl

@[simp] theorem reorderThin_sum {k d : ℕ} (p : Space k × (ℝ × Space d)) :
    (∑ i : Fin (k+1), (reorderThinEquiv k d p).1 i) = (∑ i : Fin k, p.1 i) + p.2.1 := by
  rw [Fin.sum_univ_succ]
  simp [add_comm]

end AffineBernstein
end

end OAI
