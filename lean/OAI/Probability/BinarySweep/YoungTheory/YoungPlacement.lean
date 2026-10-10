import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungDominance

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

variable {X J : Type*} [Fintype X] [DecidableEq X] [Fintype J]

def movePlacement (g : Equiv.Perm X) (x : J ↪ X) : J ↪ X := x.trans g.toEmbedding

omit [Fintype X] [DecidableEq X] [Fintype J] in
lemma movePlacement_mul (g h : Equiv.Perm X) (x : J ↪ X) :
    movePlacement (g*h) x = movePlacement g (movePlacement h x) := rfl

omit [Fintype X] [DecidableEq X] [Fintype J] in
@[simp] lemma movePlacement_one (x : J ↪ X) : movePlacement 1 x = x := by ext; rfl

def placementRep : Representation ℂ (Equiv.Perm X) ((J ↪ X) → ℂ) where
  toFun g := {
    toFun := fun v x => v (movePlacement g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext; simp
  map_mul' g h := by ext v x; rfl

lemma placementRep_basis (g : Equiv.Perm X) (x : J ↪ X) :
    placementRep (X := X) (J := J) g (Pi.single x (1 : ℂ)) =
      (Pi.single (movePlacement g x) (1 : ℂ) : (J ↪ X) → ℂ) := by
  ext y
  change (Pi.single x (1 : ℂ) : (J ↪ X) → ℂ) (movePlacement g⁻¹ y) = _
  simp only [Pi.single_apply]
  have he : movePlacement g⁻¹ y = x ↔ y = movePlacement g x := by
    constructor <;> intro h
    · have hh := congrArg (movePlacement g) h
      simpa only [← movePlacement_mul, mul_inv_cancel, movePlacement_one] using hh
    · subst y
      simp only [← movePlacement_mul, inv_mul_cancel, movePlacement_one]
  simp only [he]

variable (μ : YoungDiagram)

abbrev Tail := {x : Cell μ // row x ≠ 0}

lemma perm_same_tail_tabloid (g h : G μ)
    (he : ∀ x : Tail μ, g x.val = h x.val) : tabloidOfPerm μ g = tabloidOfPerm μ h := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  intro x
  by_cases hx : row x ≠ 0
  · have hh := he ⟨x,hx⟩
    change row (g⁻¹ (h x)) = row x
    rw [← hh]
    exact congrArg row (g.symm_apply_apply x)
  · have hx0 : row x = 0 := not_ne_iff.mp hx
    change row (g⁻¹ (h x)) = row x
    rw [hx0]
    by_contra hr
    have hh := he ⟨g⁻¹ (h x),hr⟩
    change g (g.symm (h x)) = _ at hh
    rw [g.apply_symm_apply] at hh
    have hh' : x = g⁻¹ (h x) := h.injective hh
    exact hr (hh' ▸ hx0)

lemma placement_extends (x : Tail μ ↪ Cell μ) :
    ∃ g : G μ, ∀ a : Tail μ, g a.val = x a :=
  Equiv.Perm.exists_extending_pair Subtype.val x Subtype.val_injective x.injective

def placementTabloid (x : Tail μ ↪ Cell μ) : Tabloid μ :=
  tabloidOfPerm μ (placement_extends μ x).choose

lemma placementTabloid_eq (x : Tail μ ↪ Cell μ) (g : G μ)
    (hg : ∀ a : Tail μ, g a.val = x a) : placementTabloid μ x = tabloidOfPerm μ g := by
  apply perm_same_tail_tabloid
  intro a
  rw [(placement_extends μ x).choose_spec, hg]

lemma placementTabloid_surjective : Function.Surjective (placementTabloid μ) := by
  intro t
  obtain ⟨g,rfl⟩ := tabloidOfPerm_surjective μ t
  exact ⟨⟨fun a => g a.val, g.injective.comp Subtype.val_injective⟩,
    placementTabloid_eq μ _ g (fun _ => rfl)⟩

lemma placementTabloid_move (g : G μ) (x : Tail μ ↪ Cell μ) :
    placementTabloid μ (movePlacement g x) = g • placementTabloid μ x := by
  obtain ⟨h,hh⟩ := placement_extends μ x
  rw [placementTabloid_eq μ x h hh, smul_tabloidOfPerm]
  apply placementTabloid_eq
  intro a
  change g (h a.val) = g (x a)
  rw [hh]

def spechtPlacement : SpechtSpace μ →ₗ[ℂ] ((Tail μ ↪ Cell μ) → ℂ) where
  toFun v x := spechtInclude μ v (placementTabloid μ x)
  map_add' v w := by ext x; simp
  map_smul' z v := by ext x; simp

lemma spechtPlacement_injective : Function.Injective (spechtPlacement μ) := by
  intro v w h
  apply spechtInclude_injective μ
  ext t
  obtain ⟨x,rfl⟩ := placementTabloid_surjective μ t
  exact congrFun h x

lemma spechtPlacement_intertwines (g : G μ) (v : SpechtSpace μ) :
    spechtPlacement μ (spechtRep μ g v) = placementRep g (spechtPlacement μ v) := by
  ext x
  change spechtInclude μ (spechtRep μ g v) (placementTabloid μ x) =
    spechtInclude μ v (placementTabloid μ (movePlacement g⁻¹ x))
  rw [spechtInclude_rep, placementTabloid_move]
  rfl

theorem specht_finrank_le_placements :
    Module.finrank ℂ (SpechtSpace μ) ≤ Fintype.card (Tail μ ↪ Cell μ) := by
  simpa using LinearMap.finrank_le_finrank_of_injective (spechtPlacement_injective μ)

lemma card_tail : Fintype.card (Tail μ) = Fintype.card (Cell μ) - μ.rowLen 0 := by
  rw [Fintype.card_subtype_compl]
  congr 1
  rw [Fintype.card_subtype]
  have h := rowPrefix_succ μ 0
  simpa [rowPrefix] using h

theorem specht_finrank_le_power : Module.finrank ℂ (SpechtSpace μ) ≤
    Fintype.card (Cell μ) ^ (Fintype.card (Cell μ) - μ.rowLen 0) := by
  calc
    _ ≤ Fintype.card (Tail μ ↪ Cell μ) := specht_finrank_le_placements μ
    _ ≤ Fintype.card (Tail μ → Cell μ) := Fintype.card_le_of_injective
      (fun f : Tail μ ↪ Cell μ => (f : Tail μ → Cell μ)) DFunLike.coe_injective
    _ = _ := by rw [Fintype.card_fun, card_tail]

lemma col_lt_firstRow (x : Cell μ) : col x < μ.rowLen 0 := by
  exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp x.property)
    (μ.rowLen_anti 0 (row x) (Nat.zero_le _))

lemma placement_column_collision (x : J ↪ Cell μ)
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0) :
    ∃ a b : Cell μ, a ≠ b ∧ a ∉ Set.range x ∧ b ∉ Set.range x ∧ col a = col b := by
  classical
  by_contra hn
  have hinj : Function.Injective (fun a : {a : Cell μ // a ∉ Set.range x} =>
      (⟨col a.val, col_lt_firstRow μ a.val⟩ : Fin (μ.rowLen 0))) := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    exact hn ⟨a.val,b.val,hne,a.property,b.property,congrArg Fin.val hab⟩
  have hh := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin] at hh
  have hjn : Fintype.card J ≤ Fintype.card (Cell μ) := Fintype.card_le_of_injective x x.injective
  omega

section ColumnSum
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def columnSum (ρ : Representation ℂ (G μ) V) : Module.End ℂ V :=
  ∑ c : C μ, signC μ c.val • ρ c.val

lemma columnSum_apply (ρ : Representation ℂ (G μ) V) (v : V) :
    columnSum μ ρ v = ∑ c : C μ, signC μ c.val • ρ c.val v := by
  simp [columnSum, LinearMap.sum_apply]

lemma columnSum_rep (ρ : Representation ℂ (G μ) V) (c : C μ) (v : V) :
    columnSum μ ρ (ρ c.val v) = signC μ c.val • columnSum μ ρ v := by
  rw [columnSum_apply, columnSum_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • ρ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • ρ d.val (ρ c.val v) =
    signC μ c.val • (signC μ (d * c).val • ρ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

end ColumnSum

lemma columnSum_placement_zero
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0) :
    columnSum μ (placementRep (X := Cell μ) (J := J)) = 0 := by
  have hb (x : J ↪ Cell μ) : columnSum μ placementRep (Pi.single x (1 : ℂ)) = 0 := by
    obtain ⟨a,b,hne,ha,hb,hcol⟩ := placement_column_collision μ x hj
    let c : C μ := ⟨Equiv.swap a b, swap_mem_fiber _ hcol⟩
    have hf : movePlacement c.val x = x := by
      apply Function.Embedding.ext
      intro j
      change Equiv.swap a b (x j) = x j
      apply Equiv.swap_apply_of_ne_of_ne
      · exact fun h => ha ⟨j,h⟩
      · exact fun h => hb ⟨j,h⟩
    have he := columnSum_rep μ placementRep c (Pi.single x (1 : ℂ))
    rw [placementRep_basis, hf, show signC μ c.val = -1 from signC_swap μ hne,
      neg_one_smul] at he
    ext y
    have hy := congrFun he y
    simp only [Pi.neg_apply] at hy
    change columnSum μ placementRep (Pi.single x (1 : ℂ)) y = 0
    linear_combination (1/2 : ℂ) * hy
  apply LinearMap.ext
  intro v
  have hv : v = ∑ x : J ↪ Cell μ, v x • Pi.single x (1 : ℂ) := by
    ext y
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, hb, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

theorem no_short_placement_intertwiner
    (hj : Fintype.card J < Fintype.card (Cell μ) - μ.rowLen 0)
    (f : SpechtSpace μ →ₗ[ℂ] ((J ↪ Cell μ) → ℂ))
    (hf : ∀ g v, f (spechtRep μ g v) = placementRep g (f v)) : f = 0 := by
  have he : columnSum μ placementRep (f (spechtPoly μ)) =
      (Fintype.card (C μ) : ℂ) • f (spechtPoly μ) := by
    rw [columnSum_apply]
    simp_rw [← hf]
    have hh := congrArg f (spechtInclude_column_sum (μ := μ))
    simpa only [map_sum, map_smul] using hh
  rw [columnSum_placement_zero μ hj, LinearMap.zero_apply] at he
  have hp : f (spechtPoly μ) = 0 := (smul_eq_zero.mp he.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  let f' := f.intertwiningMap_of_isIntertwiningMap (spechtRep μ) placementRep hf
  rcases Representation.IsIrreducible.injective_or_eq_zero (k := ℂ) (G := G μ)
      (V := SpechtSpace μ) (W := (J ↪ Cell μ) → ℂ) f' with hinj | hz
  · exact False.elim (spechtPoly_ne_zero μ (hinj (hp.trans f.map_zero.symm)))
  · exact congrArg (fun g => g.toLinearMap) hz

end BinaryCoordinateSweeps.Young

end

end OAI
