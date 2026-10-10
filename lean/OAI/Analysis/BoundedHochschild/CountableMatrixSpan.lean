import OAI.Analysis.BoundedHochschild.CountableDiagonalOperators

namespace OAI

/-! The algebraic countable matrix algebra consists of finite linear
combinations of its matrix units and the ambient identity. -/

noncomputable section

open scoped Pointwise

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def countableMatrixUnit (c : ℕ → PartialIso M) (i j : ℕ) : M :=
  (c i : M) * star (c j : M)

@[simp] lemma countableMatrixUnit_star (c : ℕ → PartialIso M) (i j : ℕ) :
    star (countableMatrixUnit c i j) = countableMatrixUnit c j i := by
  simp [countableMatrixUnit]

lemma countableMatrixUnit_mul (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) (i j k l : ℕ) :
    countableMatrixUnit c i j * countableMatrixUnit c k l =
      if j = k then countableMatrixUnit c i l else 0 := by
  calc
    _ = (c i : M) * (star (c j : M) * (c k : M)) * star (c l : M) := by
      simp only [countableMatrixUnit, mul_assoc]
    _ = _ := by rw [countableColumn_star_mul c hi ho]; split_ifs <;> simp [countableMatrixUnit]

def countableMatrixWordMonoid (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) : Submonoid M where
  carrier := {a | a = 0 ∨ a = 1 ∨ ∃ i j, a = countableMatrixUnit c i j}
  one_mem' := Or.inr (Or.inl rfl)
  mul_mem' := by
    rintro a b (rfl | rfl | ⟨i, j, rfl⟩) hb
    · exact Or.inl (zero_mul b)
    · simpa only [one_mul] using hb
    · rcases hb with rfl | rfl | ⟨k, l, rfl⟩
      · exact Or.inl (mul_zero _)
      · exact Or.inr (Or.inr ⟨i, j, mul_one _⟩)
      · rw [countableMatrixUnit_mul c hi ho]
        split_ifs
        · exact Or.inr (Or.inr ⟨i, l, rfl⟩)
        · exact Or.inl rfl

lemma countableMatrixWordMonoid_star (c : ℕ → PartialIso M) (hi ho)
    {a : M} (ha : a ∈ countableMatrixWordMonoid c hi ho) :
    star a ∈ countableMatrixWordMonoid c hi ho := by
  rcases ha with rfl | rfl | ⟨i, j, rfl⟩
  · exact Or.inl (star_zero M)
  · exact Or.inr (Or.inl (star_one M))
  · exact Or.inr (Or.inr ⟨j, i, countableMatrixUnit_star c i j⟩)

theorem countableMatrixAlgebra_eq_span (c : ℕ → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) :
    (countableMatrixAlgebra c).toSubalgebra.toSubmodule =
      Submodule.span ℂ ({1} ∪ Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)) := by
  let S := Set.range (fun p : ℕ × ℕ => countableMatrixUnit c p.1 p.2)
  let P := Submodule.span ℂ ({1} ∪ S)
  have hS : S ⊆ countableMatrixWordMonoid c hi ho := by
    rintro a ⟨⟨i, j⟩, rfl⟩
    exact Or.inr (Or.inr ⟨i, j, rfl⟩)
  have hgen : S ∪ star S ⊆ countableMatrixWordMonoid c hi ho := by
    intro a ha
    rcases ha with ha | ha
    · exact hS ha
    · have ha' : star a ∈ S := by simpa only [Set.mem_star] using ha
      have hstar := countableMatrixWordMonoid_star c hi ho (hS ha')
      change star (star a) = 0 ∨ star (star a) = 1 ∨
        ∃ i j, star (star a) = countableMatrixUnit c i j at hstar
      change a = 0 ∨ a = 1 ∨ ∃ i j, a = countableMatrixUnit c i j
      simpa only [star_star] using hstar
  have hwords : Submonoid.closure (S ∪ star S) ≤ countableMatrixWordMonoid c hi ho :=
    Submonoid.closure_le.mpr hgen
  apply le_antisymm
  · change (StarAlgebra.adjoin ℂ S).toSubalgebra.toSubmodule ≤ P
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_le.mpr
    intro a ha
    rcases hwords ha with rfl | rfl | ⟨i, j, rfl⟩
    · exact P.zero_mem
    · exact Submodule.subset_span (Or.inl (Set.mem_singleton 1))
    · exact Submodule.subset_span (Or.inr ⟨(i, j), rfl⟩)
  · apply Submodule.span_le.mpr
    intro a ha
    rcases ha with ha | ha
    · have ha1 : a = 1 := Set.mem_singleton_iff.mp ha
      subst a
      exact (countableMatrixAlgebra c).one_mem
    · exact StarAlgebra.subset_adjoin ℂ S ha

end BoundedHochschild.KadisonRingrose

end

end OAI
