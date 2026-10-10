import OAI.NumberTheory.DukePrimeDegree.Geometry.IndexedLinearShear

namespace OAI

/-! # Finite compositions of the elementary remaining-root shears -/

noncomputable section
open MeasureTheory Function
namespace DukePrimeDegree
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def iteratedCoordinateShear (source : ι → ι) (r : ℝ) : List ι → (ι → ℝ) → (ι → ℝ)
  | [], x => x
  | i::l, x => indexedLinearShear i (source i) r (iteratedCoordinateShear source r l x)

omit [Fintype ι] in
lemma iteratedCoordinateShear_apply_outside (source : ι → ι) (r : ℝ)
    (l : List ι) (x : ι → ℝ) (k : ι) (hk : k ∉ l) :
    iteratedCoordinateShear source r l x k = x k := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have hi : k ≠ i := fun he => hk (he ▸ List.mem_cons_self)
      have hl : k ∉ l := fun h => hk (List.mem_cons_of_mem i h)
      simp only [iteratedCoordinateShear,indexedLinearShear,Function.update_of_ne hi]
      exact ih hl

omit [Fintype ι] in
lemma iteratedCoordinateShear_apply (source : ι → ι) (r : ℝ)
    (l : List ι) (hl : l.Nodup) (hsource : ∀ i ∈ l, source i ∉ l)
    (x : ι → ℝ) (k : ι) :
    iteratedCoordinateShear source r l x k = if k ∈ l then x k+r*x (source k) else x k := by
  induction l with
  | nil => simp [iteratedCoordinateShear]
  | cons i l ih =>
      obtain ⟨hi,hl⟩ := List.nodup_cons.mp hl
      have hs : ∀ j ∈ l, source j ∉ l := fun j hj hj' =>
        hsource j (List.mem_cons_of_mem i hj) (List.mem_cons_of_mem i hj')
      by_cases hki : k = i
      · subst k
        have hsi : source i ∉ l := fun h => hsource i List.mem_cons_self
          (List.mem_cons_of_mem i h)
        simp only [iteratedCoordinateShear,indexedLinearShear,Function.update_self,
          List.mem_cons_self,ite_true]
        rw [iteratedCoordinateShear_apply_outside source r l x i hi,
          iteratedCoordinateShear_apply_outside source r l x (source i) hsi]
      · simp only [iteratedCoordinateShear,indexedLinearShear,Function.update_of_ne hki]
        rw [ih hl hs]
        simp [hki]

theorem iteratedCoordinateShear_preserves (source : ι → ι) (r : ℝ) (l : List ι)
    (ν : ι → Measure ℝ) [∀ k, SigmaFinite (ν k)]
    (hsource : ∀ i ∈ l, source i ≠ i)
    (hinv : ∀ i ∈ l, ν (source i) = Measure.dirac 0 ∨
      ∀ a : ℝ, (ν i).map (fun t => t+a) = ν i) :
    MeasurePreserving (iteratedCoordinateShear source r l) (Measure.pi ν) (Measure.pi ν) := by
  induction l with
  | nil => exact MeasurePreserving.id _
  | cons i l ih =>
      exact (indexedLinearShear_preserves i (source i) (hsource i List.mem_cons_self) r ν
        (hinv i List.mem_cons_self)).comp
        (ih (fun j hj => hsource j (List.mem_cons_of_mem i hj))
          (fun j hj => hinv j (List.mem_cons_of_mem i hj)))

end DukePrimeDegree

end

end OAI
