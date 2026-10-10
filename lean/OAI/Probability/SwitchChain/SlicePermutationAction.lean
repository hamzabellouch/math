import OAI.Probability.SwitchChain.TransitiveAverage

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SlicePermutationAction

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem exists_perm_map_eq (s t : Finset α) (hcard : s.card = t.card) :
    ∃ σ : Equiv.Perm α, s.map σ.toEmbedding = t := by
  classical
  let e : s ≃ t := Fintype.equivOfCardEq (by simpa using hcard)
  let σ : Equiv.Perm α := e.extendSubtype
  refine ⟨σ, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact e.extendSubtype_mem x hx
  · simpa using hcard.ge

abbrev Slice (α : Type*) (q : ℕ) := {s : Finset α // s.card = q}

def boundedSliceEquiv (U : Finset α) (q : ℕ) :
    {s : Finset α // s ⊆ U ∧ s.card = q} ≃ Slice U q where
  toFun s := ⟨s.val.subtype (fun x => x ∈ U), by
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr s.property.1]
    exact s.property.2⟩
  invFun s := ⟨s.val.map (Function.Embedding.subtype (fun x => x ∈ U)),
    ⟨fun _ hx => Finset.property_of_mem_map_subtype _ hx, by simpa using s.property⟩⟩
  left_inv s := Subtype.ext (Finset.subtype_map_of_mem s.property.1)
  right_inv s := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp (Finset.mem_subtype.mp hx)
      have heq : y = x := Subtype.ext hxy
      simpa [← heq] using hy
    · intro hx
      exact Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨x, hx, rfl⟩)

def relabel {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) : Slice α q :=
  ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_one {q : ℕ} (s : Slice α q) : relabel 1 s = s := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  change s.val.map (Function.Embedding.refl α) = s.val
  exact Finset.map_refl

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_mul {q : ℕ} (σ τ : Equiv.Perm α) (s : Slice α q) :
    relabel (σ * τ) s = relabel σ (relabel τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  simp only [relabel, Finset.map_map]
  rfl

def relabelEquiv {q : ℕ} (σ : Equiv.Perm α) : Equiv.Perm (Slice α q) where
  toFun := relabel σ
  invFun := relabel σ⁻¹
  left_inv s := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv s := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

@[simp] theorem relabelEquiv_apply {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) :
    relabelEquiv σ s = relabel σ s := rfl

def relabelHom (q : ℕ) : Equiv.Perm α →* Equiv.Perm (Slice α q) where
  toFun := relabelEquiv
  map_one' := by apply Equiv.ext; intro s; exact relabel_one s
  map_mul' σ τ := by apply Equiv.ext; intro s; exact relabel_mul σ τ s

theorem sum_relabel {q : ℕ} (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s : Slice α q, f (relabel σ s)) = ∑ s : Slice α q, f s :=
  Equiv.sum_comp (relabelEquiv σ) f

theorem relabelEquiv_list_prod {q : ℕ} (l : List (Equiv.Perm α)) :
    relabelEquiv (q := q) l.prod = (l.map relabelEquiv).prod :=
  map_list_prod (relabelHom q) l

@[reducible] def mulAction (q : ℕ) : MulAction (Equiv.Perm α) (Slice α q) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

theorem exists_relabel_eq {q : ℕ} (s t : Slice α q) :
    ∃ σ : Equiv.Perm α, relabel σ s = t := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq s.val t.val (s.property.trans t.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

theorem average_relabel_eq {q : ℕ} (f : Slice α q → ℝ) (s : Slice α q) :
    (∑ σ : Equiv.Perm α, f (relabel σ s)) / (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ t : Slice α q, f t) / (Fintype.card (Slice α q) : ℝ) := by
  let := mulAction (α := α) q
  let : MulAction.IsPretransitive (Equiv.Perm α) (Slice α q) :=
    ⟨exists_relabel_eq⟩
  exact TransitiveAverage.average_smul_eq f s

theorem average_relabel_sq_difference {q : ℕ} (f : Slice α q → ℝ) :
    (∑ σ : Equiv.Perm α, ∑ s : Slice α q, (f s - f (relabel σ s)) ^ 2) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ s : Slice α q, ∑ t : Slice α q, (f s - f t) ^ 2) /
        (Fintype.card (Slice α q) : ℝ) := by
  let := mulAction (α := α) q
  let : MulAction.IsPretransitive (Equiv.Perm α) (Slice α q) :=
    ⟨exists_relabel_eq⟩
  exact TransitiveAverage.average_sum_sq_difference f

end Problem315.SlicePermutationAction

end

end OAI
