import OAI.Algebra.Finitistic.Bar.MultibarIndex

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar.Indexed
universe u

/-- A D/X pattern with length and X-count in its type, avoiding any degree casts. -/
inductive Shape : ℕ → ℕ → Type
  | nil : Shape 0 0
  | base {n r : ℕ} : Shape n r → Shape (n+1) r
  | ideal {n r : ℕ} : Shape n r → Shape (n+1) (r+1)

local instance (n r : ℕ) : DecidableEq (Shape n r) := Classical.decEq _

def toList : {n r : ℕ} → Shape n r → List Bool
  | _, _, .nil => []
  | _, _, .base p => false :: toList p
  | _, _, .ideal p => true :: toList p

@[simp] theorem length_toList {n r : ℕ} (p : Shape n r) : (toList p).length = n := by
  induction p <;> simp_all [toList]

@[simp] theorem count_toList {n r : ℕ} (p : Shape n r) : count (toList p) = r := by
  induction p <;> simp_all [toList, count]

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

@[reducible] def tensor : {n r : ℕ} → Shape n r → ModuleCat k
  | _, _, .nil => ModuleCat.of k N
  | _, _, .base p => ModuleCat.of k (D ⊗[k] tensor p)
  | _, _, .ideal p => ModuleCat.of k (X ⊗[k] tensor p)

def inclusion : {n r : ℕ} → (p : Shape n r) →
    tensor k D X N p →ₗ[k] DerivedBar.term k (TrivSqZeroExt D X) N n
  | _, _, .nil => LinearMap.id
  | _, _, .base p => TensorProduct.map (inlAlgHom k D X).toLinearMap (inclusion p)
  | _, _, .ideal p => TensorProduct.map ((inrHom D X).restrictScalars k) (inclusion p)

def retraction : {n r : ℕ} → (p : Shape n r) →
    DerivedBar.term k (TrivSqZeroExt D X) N n →ₗ[k] tensor k D X N p
  | _, _, .nil => LinearMap.id
  | _, _, .base p => TensorProduct.map (fstHom k D X).toLinearMap (retraction p)
  | _, _, .ideal p => TensorProduct.map ((sndHom D X).restrictScalars k) (retraction p)

theorem retraction_inclusion {n r : ℕ} (p : Shape n r) (v : tensor k D X N p) :
    retraction k D X N p (inclusion k D X N p v) = v := by
  induction p with
  | nil => rfl
  | base p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v =>
      change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
      rw [ih]
    | add v w hv hw => simp only [map_add, hv, hw]
  | ideal p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul x v =>
      change x ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
      rw [ih]
    | add v w hv hw => simp only [map_add, hv, hw]

/-- Distinct patterns are separated by slotwise projections, including non-flat bimodules. -/
theorem retraction_other {n r : ℕ} (p q : Shape n r) (hpq : p ≠ q)
    (v : tensor k D X N q) : retraction k D X N p (inclusion k D X N q v) = 0 := by
  induction p with
  | nil => cases q; exact (hpq rfl).elim
  | base p ih =>
    cases q with
    | base q =>
      have h : p ≠ q := fun h => hpq (congrArg Shape.base h)
      induction v using TensorProduct.inductionOn with
      | tmul d v =>
        change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
        rw [ih q h, TensorProduct.tmul_zero]
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | ideal q =>
      induction v using TensorProduct.inductionOn with
      | tmul x v => exact TensorProduct.zero_tmul _ _
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  | ideal p ih =>
    cases q with
    | base q =>
      induction v using TensorProduct.inductionOn with
      | tmul d v => exact TensorProduct.zero_tmul _ _
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]
    | ideal q =>
      have h : p ≠ q := fun h => hpq (congrArg Shape.ideal h)
      induction v using TensorProduct.inductionOn with
      | tmul x v =>
        change x ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
        rw [ih q h, TensorProduct.tmul_zero]
      | add v w hv hw => simp only [map_add, hv, hw, add_zero]

theorem inclusion_mem {n r : ℕ} (p : Shape n r) (v : tensor k D X N p) :
    inclusion k D X N p v ∈ SquareZero.weight k D X N n r := by
  induction p with
  | nil => exact Submodule.subset_span (SquareZero.Word.nil v)
  | base p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul d v => exact SquareZero.base_tmul_mem d (ih v)
    | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | ideal p ih =>
    induction v using TensorProduct.inductionOn with
    | tmul x v => exact SquareZero.ideal_tmul_mem x (ih v)
    | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

/-- Every homogeneous word is an actual tensor in one of the prescribed blocks. -/
theorem word_inclusion {n r : ℕ} {z : DerivedBar.term k (TrivSqZeroExt D X) N n}
    (hz : SquareZero.Word k D X N n r z) :
    ∃ (p : Shape n r) (v : tensor k D X N p), inclusion k D X N p v = z := by
  induction hz with
  | nil v => exact ⟨.nil, v, rfl⟩
  | base d h ih =>
    obtain ⟨p, v, hv⟩ := ih
    exact ⟨.base p, d ⊗ₜ[k] v, by change (inl d : TrivSqZeroExt D X) ⊗ₜ[k] _ = _; rw [hv]⟩
  | ideal x h ih =>
    obtain ⟨p, v, hv⟩ := ih
    exact ⟨.ideal p, x ⊗ₜ[k] v, by change (inr x : TrivSqZeroExt D X) ⊗ₜ[k] _ = _; rw [hv]⟩

abbrev outerTensor {n r : ℕ} (p : Shape n r) := D ⊗[k] tensor k D X N p

def outerInclusion {n r : ℕ} (p : Shape n r) : outerTensor k D X N p →ₗ[D]
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N n :=
  AlgebraTensorModule.lTensor D D (inclusion k D X N p)

def outerRetraction {n r : ℕ} (p : Shape n r) :
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N n →ₗ[D] outerTensor k D X N p :=
  AlgebraTensorModule.lTensor D D (retraction k D X N p)

theorem outerRetraction_inclusion {n r : ℕ} (p : Shape n r) (v : outerTensor k D X N p) :
    outerRetraction k D X N p (outerInclusion k D X N p v) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N p v) = _
    rw [retraction_inclusion]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem outerRetraction_other {n r : ℕ} (p q : Shape n r) (hpq : p ≠ q)
    (v : outerTensor k D X N q) :
    outerRetraction k D X N p (outerInclusion k D X N q v) = 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] retraction k D X N p (inclusion k D X N q v) = 0
    rw [retraction_other k D X N p q hpq, TensorProduct.tmul_zero]
  | add v w hv hw => simp only [map_add, hv, hw, add_zero]

theorem outerInclusion_mem {n r : ℕ} (p : Shape n r) (v : outerTensor k D X N p) :
    outerInclusion k D X N p v ∈ SquareZero.twoSidedWeight k D X N n r := by
  induction v using TensorProduct.inductionOn with
  | tmul d v => exact SquareZero.tensor_weight_mem d (inclusion_mem k D X N p v)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

/-- The actual sum of all tensor-block inclusions in count r and degree n. -/
def assemble (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) →ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  DirectSum.toModule D (Shape n r) _ (fun p =>
    (outerInclusion k D X N p).codRestrict _ (outerInclusion_mem k D X N p))

/-- Surjectivity is proved from the original homogeneous-word spanning definition. -/
theorem assemble_surjective (n r : ℕ) : Function.Surjective (assemble k D X N n r) := by
  let S := LinearMap.range (assemble k D X N n r)
  have hle : SquareZero.twoSidedWeight k D X N n r ≤
      S.map (SquareZero.twoSidedWeight k D X N n r).subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨d, v, hv, rfl⟩
    obtain ⟨p, w, hw⟩ := word_inclusion k D X N hv
    refine ⟨assemble k D X N n r (DirectSum.lof D _ _ p (d ⊗ₜ[k] w)), ⟨_, rfl⟩, ?_⟩
    simp only [assemble, DirectSum.toModule_lof, LinearMap.codRestrict_apply,
      Submodule.subtype_apply]
    change d ⊗ₜ[k] inclusion k D X N p w = d ⊗ₜ[k] v
    rw [hw]
  intro v
  obtain ⟨w, ⟨z, hz⟩, hw⟩ := hle v.property
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [hz]
  exact hw

/-- Projection onto an actual block after summation recovers the direct-sum component. -/
theorem outerRetraction_assemble (n r : ℕ) (p : Shape n r)
    (z : ⨁ p : Shape n r, outerTensor k D X N p) :
    outerRetraction k D X N p (assemble k D X N n r z) = z p := by
  have h : (outerRetraction k D X N p).comp
      ((SquareZero.twoSidedWeight k D X N n r).subtype.comp (assemble k D X N n r)) =
      DirectSum.component D (Shape n r) (outerTensor k D X N) p := by
    apply DirectSum.linearMap_ext
    intro q
    apply LinearMap.ext
    intro v
    by_cases hpq : p = q
    · subst q
      simpa only [LinearMap.comp_apply, assemble, DirectSum.toModule_lof,
        LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self] using
          outerRetraction_inclusion k D X N p v
    · simpa only [LinearMap.comp_apply, assemble, DirectSum.toModule_lof,
        LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.of, Ne.symm hpq, dite_eq_right, dite_false] using
          outerRetraction_other k D X N p q hpq v
  exact LinearMap.congr_fun h z

/-- The block direct sum is linearly isomorphic to the entire actual count submodule. -/
def decomposition (n r : ℕ) : (⨁ p : Shape n r, outerTensor k D X N p) ≃ₗ[D]
    SquareZero.twoSidedWeight k D X N n r :=
  LinearEquiv.ofBijective (assemble k D X N n r)
    ⟨by
      intro z w h
      apply DFinsupp.ext
      intro p
      rw [← outerRetraction_assemble k D X N n r p z,
        ← outerRetraction_assemble k D X N n r p w, h],
     assemble_surjective k D X N n r⟩
end DerivedBar.Multibar.Indexed

end

end OAI
