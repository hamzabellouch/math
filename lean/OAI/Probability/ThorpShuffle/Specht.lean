import OAI.Probability.ThorpShuffle.Tableaux

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

omit [Fintype α] in
@[simp] lemma perm_apply_inv (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x := g.apply_symm_apply x

omit [Fintype α] in
@[simp] lemma perm_inv_apply (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x := g.symm_apply_apply x

def Tabloid (r : α → ℕ) := {f : α → ℕ // ∃ g : Equiv.Perm α, f = r ∘ g}

instance tabloidFinite (r : α → ℕ) : Finite (Tabloid r) := by
  apply Finite.of_surjective (fun g : Equiv.Perm α => (⟨r ∘ g, g, rfl⟩ : Tabloid r))
  rintro ⟨f, g, rfl⟩
  exact ⟨g, rfl⟩

instance tabloidFintype (r : α → ℕ) : Fintype (Tabloid r) := Fintype.ofFinite _

instance tabloidAction (r : α → ℕ) : MulAction (Equiv.Perm α) (Tabloid r) where
  smul g f := ⟨f.val ∘ ⇑(g⁻¹ : Equiv.Perm α), by
    obtain ⟨h, hh⟩ := f.property
    refine ⟨h * g⁻¹, ?_⟩
    funext x
    simp only [Function.comp_apply, hh, Equiv.Perm.mul_apply]⟩
  one_smul f := by apply Subtype.ext; funext x; rfl
  mul_smul g h f := by
    apply Subtype.ext
    funext x
    change f.val ((g * h)⁻¹ x) = f.val (h⁻¹ (g⁻¹ x))
    rw [mul_inv_rev, Equiv.Perm.mul_apply]

omit [Fintype α] in
@[simp] lemma tabloid_smul_apply (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) (x : α) :
    (g • f).val x = f.val (g⁻¹ x) := rfl

def baseTabloid (r : α → ℕ) : Tabloid r := ⟨r, 1, by funext x; rfl⟩

omit [Fintype α] in
@[simp] lemma baseTabloid_apply (r : α → ℕ) (x : α) : (baseTabloid r).val x = r x := rfl

def fiberGroup (c : α → ℕ) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, c (g x) = c x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ x)
    change c (g (g.symm x)) = c (g.symm x) at hh
    rw [g.apply_symm_apply] at hh
    exact hh.symm

omit [Fintype α] in
lemma stabilizes_tabloid_iff (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) :
    g • f = f ↔ ∀ x, f.val (g x) = f.val x := by
  constructor
  · intro h x
    have hh := congrArg (fun t : Tabloid r => t.val (g x)) h
    simpa only [tabloid_smul_apply, perm_inv_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    have hh := h (g⁻¹ x)
    simpa only [tabloid_smul_apply, perm_apply_inv] using hh.symm

omit [Fintype α] in
lemma swap_preserves {c : α → ℕ} {x y : α} (hc : c x = c y) :
    Equiv.swap x y ∈ fiberGroup c := by
  intro z
  by_cases hzx : z = x
  · subst z; simp [hc]
  by_cases hzy : z = y
  · subst z; simp [hc]
  rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

def complexSign : Equiv.Perm α →* ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤˣ) : ℤ)
  map_one' := by simp
  map_mul' := by intro g h; simp

@[simp] lemma complexSign_conj (g : Equiv.Perm α) : conj (complexSign g) = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_inv (g : Equiv.Perm α) : complexSign g⁻¹ = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_swap (x y : α) (h : x ≠ y) : complexSign (Equiv.swap x y) = -1 := by
  simp [complexSign, Equiv.Perm.sign_swap h]

variable (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D)

def tableauRow (x : α) : ℕ := (t x).val.1

def tableauCol (x : α) : ℕ := (t x).val.2

omit [Fintype α] in

lemma row_col_free (g : fiberGroup (tableauCol D t))
    (hg : (g : Equiv.Perm α) • baseTabloid (tableauRow D t) = baseTabloid (tableauRow D t)) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact (stabilizes_tabloid_iff _ _ _).mp hg x
  · exact g.property x

lemma collision_odd (f : Tabloid (tableauRow D t)) (x y : α) (hxy : x ≠ y)
    (hc : tableauCol D t x = tableauCol D t y) (hr : f.val x = f.val y) :
    ∃ g : fiberGroup (tableauCol D t), (g : Equiv.Perm α) • f = f ∧ complexSign (g : Equiv.Perm α) = -1 := by
  refine ⟨⟨Equiv.swap x y, swap_preserves hc⟩, ?_, complexSign_swap x y hxy⟩
  rw [stabilizes_tabloid_iff]
  exact swap_preserves hr

lemma collision_or_column (f : Tabloid (tableauRow D t)) :
    (∃ a : fiberGroup (tableauCol D t), (a : Equiv.Perm α) • f = f ∧
      complexSign (a : Equiv.Perm α) = -1) ∨
    ∃ a : fiberGroup (tableauCol D t), f = (a : Equiv.Perm α) • baseTabloid (tableauRow D t) := by
  classical
  by_cases hc : ∃ x y : α, x ≠ y ∧ tableauCol D t x = tableauCol D t y ∧ f.val x = f.val y
  · obtain ⟨x, y, hxy, hx, hy⟩ := hc
    exact Or.inl (collision_odd D t f x y hxy hx hy)
  right
  let r : Thorp.Young.Cells D → ℕ := fun z => f.val (t.symm z)
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 → r x = r y → x = y := by
    intro x y hcol hr
    by_contra hxy
    apply hc
    refine ⟨t.symm x, t.symm y, ?_, ?_, hr⟩
    · exact fun h => hxy (t.symm.injective h)
    · simpa only [tableauCol, Equiv.apply_symm_apply] using hcol
  have hs : ∑ z : Thorp.Young.Cells D, r z = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    change ∑ z, f.val (t.symm z) = _
    rw [Equiv.sum_comp t.symm]
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    change ∑ x, tableauRow D t (g x) = _
    rw [Equiv.sum_comp g]
    exact Equiv.sum_comp t (fun z : Thorp.Young.Cells D => z.val.1)
  obtain ⟨σ, hσc, hσr⟩ := Thorp.Young.column_sort D r hi hs
  let a : Equiv.Perm α := (t.trans σ).trans t.symm
  have hac : a ∈ fiberGroup (tableauCol D t) := by
    intro x
    change (t (t.symm (σ (t x)))).val.2 = (t x).val.2
    simpa only [Equiv.apply_symm_apply] using hσc (t x)
  have har (x : α) : f.val (a x) = tableauRow D t x := hσr (t x)
  refine ⟨⟨a, hac⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hh := har (a⁻¹ x)
  simpa only [tabloid_smul_apply, baseTabloid_apply, perm_apply_inv] using hh

def tabloidRep : Representation ℂ (Equiv.Perm α) (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.rep

def columnAlternator : Module.End ℂ (EuclideanSpace ℂ (Tabloid (tableauRow D t))) :=
  PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)

def polytabloid : EuclideanSpace ℂ (Tabloid (tableauRow D t)) :=
  columnAlternator D t (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))

lemma polytabloid_support (f : Tabloid (tableauRow D t)) (hf : polytabloid D t f ≠ 0) :
    ∃ h : fiberGroup (tableauCol D t), f = h.val • baseTabloid (tableauRow D t) := by
  by_contra hn
  push Not at hn
  apply hf
  change PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ)) f = 0
  rw [PermutationSpace.alternator_coeff]
  apply Finset.sum_eq_zero
  intro h _
  have hne : h.val⁻¹ • f ≠ baseTabloid (tableauRow D t) := by
    intro he
    exact hn h (inv_smul_eq_iff.mp he)
  rw [PiLp.single_apply]
  change complexSign h.val * (if h.val⁻¹ • f = baseTabloid (tableauRow D t) then 1 else 0) = 0
  rw [ite_eq_right hne, mul_zero]

lemma polytabloid_diag : polytabloid D t (baseTabloid (tableauRow D t)) = 1 := by
  exact PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)

lemma polytabloid_ne_zero : polytabloid D t ≠ 0 := by
  have hh := PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)
  intro hz
  change polytabloid D t (baseTabloid (tableauRow D t)) = 1 at hh
  rw [hz] at hh
  norm_num at hh

lemma columnAlternator_rank_one (v : EuclideanSpace ℂ (Tabloid (tableauRow D t))) :
    columnAlternator D t v = ⟪polytabloid D t, v⟫_ℂ • polytabloid D t := by
  exact PermutationSpace.alternator_rank_one (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (fun h => complexSign_conj h.val)
    (fun h => complexSign_inv h.val) (row_col_free D t) (collision_or_column D t) v

def module : Subrepresentation (tabloidRep D t) := cyclic (tabloidRep D t) (polytabloid D t)

theorem irreducible : Representation.IsIrreducible (module D t).toRepresentation := by
  exact cyclic_irreducible (tabloidRep D t) (polytabloid D t) (polytabloid_ne_zero D t)
    PermutationSpace.rep_unitary (columnAlternator D t) (columnAlternator_rank_one D t)
    (PermutationSpace.alternator_stable (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype))

end Thorp.Specht

end

end OAI
