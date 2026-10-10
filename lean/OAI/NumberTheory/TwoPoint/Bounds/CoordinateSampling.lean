import OAI.NumberTheory.TwoPoint.Walks.DisjointCoordinates
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Factor the full independent law into controls, pivots and outside coordinates. -/

namespace TwoPointCorrelations

open Finset Matrix

namespace FiniteLaw

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype A]

/-- A bijection of coordinate names preserves a constant independent law. -/
lemma independent_average_equiv (e : ι ≃ κ) (μ : FiniteLaw A)
    (f : (κ → A) → ℝ) :
    (independent (fun _ : κ => μ)).average f =
      (independent (fun _ : ι => μ)).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent (fun _ : κ => μ)).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent (fun _ : κ => μ)).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, μ.weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, μ.weight (x i)) * f (fun k => x (e.symm k))
      exact congrArg (fun r => r * f (fun k => x (e.symm k)))
        (e.symm.prod_comp (fun i => μ.weight (x i)))

/-- Independence on a sum of coordinate types is the product of the two
independent laws. -/
lemma independent_average_sum (μ : FiniteLaw A) (f : (ι ⊕ κ → A) → ℝ) :
    (independent (fun _ : ι ⊕ κ => μ)).average f =
      (independent (fun _ : ι => μ)).average (fun x =>
        (independent (fun _ : κ => μ)).average (fun y => f (Sum.elim x y))) := by
  let E := Equiv.sumArrowEquivProdArrow ι κ A
  calc
    _ = ∑ xy : (ι → A) × (κ → A),
        (independent (fun _ : ι ⊕ κ => μ)).weight (Sum.elim xy.1 xy.2) *
          f (Sum.elim xy.1 xy.2) :=
      (E.symm.sum_comp (fun x => (independent (fun _ : ι ⊕ κ => μ)).weight x * f x)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, independent, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, average, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring

end FiniteLaw

variable {α ρ A : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

abbrev OutsideIndex (control pivot : ρ → α) := {z : α // z ∈ outsideCoordinates control pivot}

def coordinateIndex (control pivot : ρ → α) : ρ ⊕ (ρ ⊕ OutsideIndex control pivot) → α :=
  Sum.elim control (Sum.elim pivot Subtype.val)

omit [DecidableEq ρ] in
lemma coordinateIndex_bijective (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) :
    Function.Bijective (coordinateIndex control pivot) := by
  classical
  have hout (z : OutsideIndex control pivot) :
      (∀ i, (z : α) ≠ control i) ∧ (∀ i, (z : α) ≠ pivot i) := by
    have hz : (z : α) ∉ controlCoordinates control ∧ (z : α) ∉ controlCoordinates pivot := by
      simpa only [outsideCoordinates, mem_compl, mem_union, not_or] using z.property
    constructor
    · intro i h
      exact hz.1 (mem_image.mpr ⟨i, mem_univ _, h.symm⟩)
    · intro i h
      exact hz.2 (mem_image.mpr ⟨i, mem_univ _, h.symm⟩)
  constructor
  · intro x y hxy
    rcases x with i | (i | z) <;> rcases y with j | (j | z')
    · exact congrArg Sum.inl (hc hxy)
    · exact False.elim (hdisjoint j i hxy.symm)
    · exact False.elim ((hout z').1 i hxy.symm)
    · exact False.elim (hdisjoint i j hxy)
    · exact congrArg (Sum.inr ∘ Sum.inl) (hp hxy)
    · exact False.elim ((hout z').2 i hxy.symm)
    · exact False.elim ((hout z).1 j hxy)
    · exact False.elim ((hout z).2 j hxy)
    · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hxy)
  · intro z
    by_cases hz : z ∈ controlCoordinates control
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hz
      exact ⟨Sum.inl i, rfl⟩
    · by_cases hz' : z ∈ controlCoordinates pivot
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hz'
        exact ⟨Sum.inr (Sum.inl i), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨z, by simp [outsideCoordinates, hz, hz']⟩), rfl⟩

noncomputable def coordinateEquiv (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) :
    ρ ⊕ (ρ ⊕ OutsideIndex control pivot) ≃ α :=
  Equiv.ofBijective (coordinateIndex control pivot) (coordinateIndex_bijective control pivot hc hp hdisjoint)

noncomputable def coordinateAssignment (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (base : OutsideIndex control pivot → A) (c y : ρ → A) : α → A :=
  fun z => Sum.elim c (Sum.elim y base) ((coordinateEquiv control pivot hc hp hdisjoint).symm z)

omit [DecidableEq ρ] in
lemma coordinateAssignment_index (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j)
    (base : OutsideIndex control pivot → A) (c y : ρ → A)
    (z : ρ ⊕ (ρ ⊕ OutsideIndex control pivot)) :
    coordinateAssignment control pivot hc hp hdisjoint base c y
      (coordinateIndex control pivot z) = Sum.elim c (Sum.elim y base) z := by
  exact congrArg (Sum.elim c (Sum.elim y base))
    ((coordinateEquiv control pivot hc hp hdisjoint).symm_apply_apply z)

/-- Full product-law factorization, with the outside coordinates averaged
last in the proof and moved to the outermost expectation in the result. -/
theorem independent_average_three [Fintype A]
    (control pivot : ρ → α) (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (μ : FiniteLaw A) (f : (α → A) → ℝ) :
    (FiniteLaw.independent (fun _ : α => μ)).average f =
      (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
        (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
          (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
            f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) := by
  classical
  rw [FiniteLaw.independent_average_equiv (coordinateEquiv control pivot hc hp hdisjoint)]
  rw [FiniteLaw.independent_average_sum]
  simp_rw [FiniteLaw.independent_average_sum]
  change (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
    (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
      (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
        f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) = _
  calc
    _ = (FiniteLaw.independent (fun _ : ρ => μ)).average (fun c =>
        (FiniteLaw.independent (fun _ : OutsideIndex control pivot => μ)).average (fun base =>
          (FiniteLaw.independent (fun _ : ρ => μ)).average (fun y =>
            f (coordinateAssignment control pivot hc hp hdisjoint base c y)))) := by
      apply congrArg (FiniteLaw.independent (fun _ : ρ => μ)).average
      funext c
      exact FiniteLaw.average_comm _ _ _
    _ = _ := FiniteLaw.average_comm _ _ _

omit [DecidableEq ρ] in
/-- Evaluation of the joined samples is the exact integer assignment used
in the row-splitting theorem. -/
lemma coordinateAssignment_integer (control pivot : ρ → α)
    (hc : Function.Injective control) (hp : Function.Injective pivot)
    (hdisjoint : ∀ i j, pivot i ≠ control j) (value : A → ℤ)
    (base : OutsideIndex control pivot → A) (c y : ρ → A) :
    (fun z => value (coordinateAssignment control pivot hc hp hdisjoint base c y z)) =
      splitAssignment control pivot
        (fun z => if hz : z ∈ outsideCoordinates control pivot then value (base ⟨z, hz⟩) else 0)
        (fun i => value (c i)) (fun i => value (y i)) := by
  classical
  funext z
  obtain ⟨j, rfl⟩ := (coordinateEquiv control pivot hc hp hdisjoint).surjective z
  change value (coordinateAssignment control pivot hc hp hdisjoint base c y
    (coordinateIndex control pivot j)) = _
  rw [coordinateAssignment_index]
  change _ = splitAssignment control pivot _ _ _ (coordinateIndex control pivot j)
  rcases j with i | (i | z)
  · change value (c i) = splitAssignment control pivot _ _ _ (control i)
    rw [splitAssignment_control control pivot _ hc]
  · change value (y i) = splitAssignment control pivot _ _ _ (pivot i)
    rw [splitAssignment_pivot control pivot _ hp hdisjoint]
  · change value (base z) = splitAssignment control pivot _ _ _ (z : α)
    rw [splitAssignment_outside control pivot _ _ _ z.property]
    simp only [dite_true, z.property]

end TwoPointCorrelations

end OAI
