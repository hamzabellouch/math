import OAI.Analysis.IrrationalRotation.Analysis.TowerMatrixUnits

namespace OAI

noncomputable section
namespace Invariant233.TowerMatrixUnits

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {β : Type*} {ι : β → Type*} [∀ b, DecidableEq (ι b)]

structure IsBlockMatrixUnitFamily (e : (b : β) → ι b → ι b → A) : Prop where
  block : ∀ b, IsMatrixUnitFamily (e b)
  cross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0

def blockMatrixGenerators (e : (b : β) → ι b → ι b → A) : Set A :=
  insert 1 (Set.range fun t : Σ b, ι b × ι b => e t.1 t.2.1 t.2.2)

omit [StarRing A] [StarModule ℂ A] [∀ block, DecidableEq (ι block)] in
theorem blockMatrixUnit_mem_span (e : (b : β) → ι b → ι b → A)
    (b : β) (i j : ι b) : e b i j ∈ Submodule.span ℂ (blockMatrixGenerators e) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨b, i, j⟩, rfl⟩)

omit [StarModule ℂ A] in
theorem blockMatrixGenerators_mul (e : (b : β) → ι b → ι b → A)
    (he : IsBlockMatrixUnitFamily e) :
    ∀ x ∈ blockMatrixGenerators e, ∀ y ∈ blockMatrixGenerators e,
      x * y ∈ Submodule.span ℂ (blockMatrixGenerators e) := by
  classical
  rintro x (rfl | ⟨⟨b, i, j⟩, rfl⟩) y hy
  · simpa using Submodule.subset_span hy
  · rcases hy with rfl | ⟨⟨c, k, l⟩, rfl⟩
    · simpa using blockMatrixUnit_mem_span e b i j
    · by_cases hbc : b = c
      · subst c
        rw [(he.block b).mul]
        split_ifs
        · exact blockMatrixUnit_mem_span e b i l
        · exact Submodule.zero_mem _
      · rw [he.cross b c hbc]
        exact Submodule.zero_mem _

omit [StarModule ℂ A] in
theorem blockMatrixGenerators_star (e : (b : β) → ι b → ι b → A)
    (he : IsBlockMatrixUnitFamily e) :
    ∀ x ∈ blockMatrixGenerators e, star x ∈ Submodule.span ℂ (blockMatrixGenerators e) := by
  rintro x (rfl | ⟨⟨b, i, j⟩, rfl⟩)
  · simpa using (Submodule.subset_span (Set.mem_insert 1 _) :
      (1 : A) ∈ Submodule.span ℂ (blockMatrixGenerators e))
  · rw [(he.block b).star]
    exact blockMatrixUnit_mem_span e b j i

def blockMatrixAlgebra (e : (b : β) → ι b → ι b → A)
    (he : IsBlockMatrixUnitFamily e) : StarSubalgebra ℂ A :=
  spanStarAlgebra (blockMatrixGenerators e) (Submodule.subset_span (Set.mem_insert 1 _))
    (blockMatrixGenerators_mul e he) (blockMatrixGenerators_star e he)

theorem blockMatrixAlgebra_finiteDimensional [Finite β] [∀ b, Finite (ι b)]
    (e : (b : β) → ι b → ι b → A) (he : IsBlockMatrixUnitFamily e) :
    FiniteDimensional ℂ (blockMatrixAlgebra e he) :=
  spanStarAlgebra_finiteDimensional _ ((Set.finite_range _).insert 1) _ _ _

@[simp] theorem blockMatrixUnit_mem_blockMatrixAlgebra
    (e : (b : β) → ι b → ι b → A) (he : IsBlockMatrixUnitFamily e)
    (b : β) (i j : ι b) : e b i j ∈ blockMatrixAlgebra e he :=
  blockMatrixUnit_mem_span e b i j

theorem blockMatrixAlgebra_le (e : (b : β) → ι b → ι b → A)
    (he : IsBlockMatrixUnitFamily e) (B : StarSubalgebra ℂ A)
    (heB : ∀ b i j, e b i j ∈ B) : blockMatrixAlgebra e he ≤ B := by
  apply spanStarAlgebra_le
  rintro x (rfl | ⟨⟨b, i, j⟩, rfl⟩)
  · exact B.one_mem
  · exact heB b i j

theorem blockMatrixAlgebra_eq_adjoin (e : (b : β) → ι b → ι b → A)
    (he : IsBlockMatrixUnitFamily e) :
    blockMatrixAlgebra e he = StarAlgebra.adjoin ℂ
      (Set.range fun t : Σ b, ι b × ι b => e t.1 t.2.1 t.2.2) := by
  apply le_antisymm
  · apply blockMatrixAlgebra_le
    intro b i j
    exact StarAlgebra.subset_adjoin ℂ _ ⟨⟨b, i, j⟩, rfl⟩
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨b, i, j⟩, rfl⟩
    exact blockMatrixUnit_mem_blockMatrixAlgebra e he b i j

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem compressed_cross_eq_zero {u v p q : A}
    (hu : u ∈ unitary A) (hv : v ∈ unitary A)
    (h : (u * p * star u) * (v * q * star v) = 0) :
    p * star u * v * q = 0 := by
  have h' := congrArg (fun x : A => star u * x * v) h
  have hu' := Unitary.star_mul_self_of_mem hu
  have hv' := Unitary.star_mul_self_of_mem hv
  simp only [← mul_assoc, hu', one_mul, mul_zero, zero_mul] at h'
  simpa only [mul_assoc, hv', mul_one] using h'

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem towerEntry_cross_eq_zero {γ δ : Type*} (u : γ → A) (v : δ → A)
    (hu : ∀ i, u i ∈ unitary A) (hv : ∀ j, v j ∈ unitary A) (p q : A)
    (horth : ∀ i j, towerEntry u p i i * towerEntry v q j j = 0)
    (i j : γ) (k l : δ) : towerEntry u p i j * towerEntry v q k l = 0 := by
  have hzero := compressed_cross_eq_zero (hu j) (hv k) (horth j k)
  calc
    towerEntry u p i j * towerEntry v q k l =
        u i * (p * star (u j) * v k * q) * star (v l) := by
      simp only [towerEntry, mul_assoc]
    _ = 0 := by rw [hzero, mul_zero, zero_mul]

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem towerEntry_isBlockMatrixUnitFamily (u : (b : β) → ι b → A) (p : β → A)
    (hu : ∀ b i, u b i ∈ unitary A) (hp : ∀ b, IsStarProjection (p b))
    (hself : ∀ b i j, i ≠ j →
      towerEntry (u b) (p b) i i * towerEntry (u b) (p b) j j = 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j,
      towerEntry (u b) (p b) i i * towerEntry (u c) (p c) j j = 0) :
    IsBlockMatrixUnitFamily (fun b => towerEntry (u b) (p b)) := by
  refine ⟨fun b => towerEntry_isMatrixUnitFamily (u b) (hu b) (hp b) (hself b), ?_⟩
  intro b c hbc i j k l
  exact towerEntry_cross_eq_zero (u b) (u c) (hu b) (hu c) (p b) (p c)
    (hcross b c hbc) i j k l

theorem exists_finiteDimensional_blockTowerAlgebra [Finite β] [∀ b, Finite (ι b)]
    (u : (b : β) → ι b → A) (p : β → A)
    (hu : ∀ b i, u b i ∈ unitary A) (hp : ∀ b, IsStarProjection (p b))
    (hself : ∀ b i j, i ≠ j →
      towerEntry (u b) (p b) i i * towerEntry (u b) (p b) j j = 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j,
      towerEntry (u b) (p b) i i * towerEntry (u c) (p c) j j = 0)
    (B : StarSubalgebra ℂ A) (hpB : ∀ b, p b ∈ B) (huB : ∀ b i, u b i ∈ B) :
    ∃ C : StarSubalgebra ℂ A, C ≤ B ∧ FiniteDimensional ℂ C ∧
      (∀ b i j, towerEntry (u b) (p b) i j ∈ C) := by
  let e := fun b => towerEntry (u b) (p b)
  let he := towerEntry_isBlockMatrixUnitFamily u p hu hp hself hcross
  refine ⟨blockMatrixAlgebra e he, ?_, blockMatrixAlgebra_finiteDimensional e he,
    blockMatrixUnit_mem_blockMatrixAlgebra e he⟩
  apply blockMatrixAlgebra_le
  intro b i j
  exact B.mul_mem (B.mul_mem (huB b i) (hpB b)) (B.star_mem' (huB b j))

end Invariant233.TowerMatrixUnits

end

end OAI
