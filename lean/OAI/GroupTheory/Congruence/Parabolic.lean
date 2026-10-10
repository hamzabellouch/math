import OAI.GroupTheory.Congruence.OddHomology

namespace OAI

noncomputable section

/-!
Actual parabolic stabilizers, F2 homological stability maps, and matrix duality.
-/

namespace CoboundaryExpanders.ActualParabolic
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory
open scoped BigOperators Matrix


section
open Construction
variable (p a m : ℕ)
abbrev Idx (a : ℕ) := Fin a ⊕ Unit

def rowFixed : Subgroup (Matrix.SpecialLinearGroup (Idx a) (R p)) where
  carrier := {A | ∀ j, A (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j}
  one_mem' := by intro j; rfl
  mul_mem' := by
    intro A B hA hB j
    change ∀ j, A.val (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j at hA
    change ((A.val : Matrix (Idx a) (Idx a) (R p)) * (B.val : Matrix (Idx a) (Idx a) (R p))) _ j = _
    simpa [Matrix.mul_apply,hA,Matrix.one_apply] using hB j
  inv_mem' := by
    intro A hA j
    change ∀ j, A.val (Sum.inr ()) j = (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j at hA
    have he : ((A.val : Matrix (Idx a) (Idx a) (R p)) * ((A⁻¹).val : Matrix (Idx a) (Idx a) (R p))) (Sum.inr ()) j =
        (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inr ()) j := by
      rw [← Matrix.SpecialLinearGroup.coe_mul,mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one]
    simpa [Matrix.mul_apply,hA,Matrix.one_apply] using he

def group : Subgroup (Matrix.SpecialLinearGroup (Idx a) (R p)) :=
  rowFixed p a ⊓ (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker

theorem block_form (A : group p a m) : A.val.val =
    Matrix.fromBlocks (Matrix.toBlocks₁₁ A.val.val)
      (Matrix.toBlocks₁₂ A.val.val) 0 1 := by
  funext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases i
    have h := A.property.1 j
    cases j <;> simpa [Matrix.one_apply] using h

noncomputable def projectValue (A : group p a m) : Matrix.SpecialLinearGroup (Fin a) (R p) :=
  ⟨Matrix.toBlocks₁₁ A.val.val, by
    have h := A.val.property
    rw [block_form p a m A,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one] at h
    exact h⟩

noncomputable def projectSL : group p a m →* Matrix.SpecialLinearGroup (Fin a) (R p) where
  toFun := projectValue p a m
  map_one' := by
    apply Subtype.ext
    funext i j
    change (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin a) (Fin a) (R p)) i j
    simp [Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change Matrix.toBlocks₁₁ (A.val.val * B.val.val) =
      Matrix.toBlocks₁₁ A.val.val * Matrix.toBlocks₁₁ B.val.val
    rw [block_form p a m A,block_form p a m B,Matrix.fromBlocks_multiply]
    simp

noncomputable def project : group p a m →* Gamma p a m :=
  (projectSL p a m).codRestrict _ (by
    intro A
    have h := A.property.2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have he := congrArg (fun B : Matrix.SpecialLinearGroup (Idx a) (R p ⧸ powerIdeal p m) =>
      B (Sum.inl i) (Sum.inl j)) h
    change Ideal.Quotient.mk (powerIdeal p m) (A.val.val (Sum.inl i) (Sum.inl j)) = (1 : Matrix (Fin a) (Fin a) (R p ⧸ powerIdeal p m)) i j
    simpa [Matrix.one_apply] using he)

noncomputable def sectionValue (A : Gamma p a m) : group p a m :=
  ⟨⟨Matrix.fromBlocks A.val.val 0 0 1, by
      rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]; exact A.val.property⟩,
    by
      constructor
      · intro j
        cases j <;> simp
      · apply Matrix.SpecialLinearGroup.ext
        intro i j
        have he := A.property
        change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val = 1 at he
        have hh (i j : Fin a) := congrArg (fun B : Matrix.SpecialLinearGroup (Fin a)
          (R p ⧸ powerIdeal p m) => B i j) he
        change Ideal.Quotient.mk (powerIdeal p m) (Matrix.fromBlocks A.val.val (0 : Matrix (Fin a) Unit (R p)) 0 1 i j) = (1 : Matrix (Idx a) (Idx a) (R p ⧸ powerIdeal p m)) i j
        cases i with
        | inl i => cases j with
          | inl j => simpa [Matrix.one_apply,Matrix.SpecialLinearGroup.map_apply_coe] using hh i j
          | inr j => simp
        | inr i => cases j <;> simp⟩

theorem project_surjective : Function.Surjective (project p a m) := by
  intro A
  exact ⟨sectionValue p a m A,by apply Subtype.ext; apply Subtype.ext; rfl⟩

theorem kernel_form (A : (project p a m).ker) : A.val.val.val =
    Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) (R p))
      (Matrix.toBlocks₁₂ A.val.val.val) 0 1 := by
  have h := A.property
  have he := congrArg (fun x : Gamma p a m => x.val.val) h
  change Matrix.toBlocks₁₁ A.val.val.val = 1 at he
  rw [block_form p a m A.val,he]
  rfl

noncomputable def kernelColumn : (project p a m).ker →* Multiplicative (Fin a → R p) where
  toFun A := Multiplicative.ofAdd (fun i => A.val.val.val (Sum.inl i) (Sum.inr ()))
  map_one' := by
    change (fun i : Fin a => (1 : Matrix (Idx a) (Idx a) (R p)) (Sum.inl i) (Sum.inr ())) = 0
    funext i
    simp
  map_mul' A B := by
    change (fun i => (A.val.val.val * B.val.val.val) (Sum.inl i) (Sum.inr ())) =
      (fun i => A.val.val.val (Sum.inl i) (Sum.inr ()) + B.val.val.val (Sum.inl i) (Sum.inr ()))
    rw [kernel_form p a m A,kernel_form p a m B,Matrix.fromBlocks_multiply]
    funext i
    simp [add_comm]

theorem kernelColumn_injective : Function.Injective (kernelColumn p a m) := by
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [kernel_form p a m A,kernel_form p a m B]
  apply congrArg (fun v : Matrix (Fin a) Unit (R p) => Matrix.fromBlocks 1 v 0 1)
  funext i u
  cases u
  exact congrFun (congrArg Multiplicative.toAdd h) i

theorem project_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    CategoryTheory.IsIso (groupHomology.map (project p a m)
      (QuotientCoinvariants.trivialMap _) j) := by
  apply QuotientCoinvariants.surjection_map_isIso _ (project_surjective p a m)
  exact QuotientCoinvariants.localOdd_of_injective (kernelColumn p a m)
    (kernelColumn_injective p a m)
    (LocallyFiniteOdd.vector_group_local_odd p hp (Fin a → R p))

end

section
open Construction CategoryTheory
variable (p a m : ℕ)

noncomputable def sectionHom : Gamma p a m →* group p a m where
  toFun := sectionValue p a m
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.fromBlocks_one
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    change Matrix.fromBlocks (A.val.val * B.val.val) 0 0 (1 : Matrix Unit Unit (R p)) =
      Matrix.fromBlocks A.val.val 0 0 1 * Matrix.fromBlocks B.val.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

theorem project_comp_section : (project p a m).comp (sectionHom p a m) = MonoidHom.id _ := by
  ext A
  rfl

theorem section_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    IsIso (groupHomology.map (sectionHom p a m)
      (QuotientCoinvariants.trivialMap _) j) := by
  let f := sectionHom p a m
  let g := project p a m
  have hpj := project_homology_isIso p a m hp j
  have hc : groupHomology.map f (QuotientCoinvariants.trivialMap f) j ≫
      groupHomology.map g (QuotientCoinvariants.trivialMap g) j = 𝟙 _ := by
    rw [← groupHomology.map_comp]
    have he : groupHomology.map (g.comp f)
        (QuotientCoinvariants.trivialMap f ≫ (Rep.resFunctor f).map (QuotientCoinvariants.trivialMap g)) j =
        groupHomology.map (MonoidHom.id (Gamma p a m))
          (QuotientCoinvariants.trivialMap (MonoidHom.id (Gamma p a m))) j := by
      apply groupHomology.map_congr
      · exact project_comp_section p a m
      · rfl
    rw [he]
    exact groupHomology.map_id j
  have : IsIso (groupHomology.map f (QuotientCoinvariants.trivialMap f) j ≫
      groupHomology.map g (QuotientCoinvariants.trivialMap g) j) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right (groupHomology.map f (QuotientCoinvariants.trivialMap f) j)
    (groupHomology.map g (QuotientCoinvariants.trivialMap g) j)

end

section
open Construction
variable (p a m : ℕ)

def idxEquiv : Idx a ≃ Fin (a+1) :=
  (Equiv.sumCongr (Equiv.refl (Fin a)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

def inclusion : group p a m →* Gamma p (a+1) m where
  toFun A := ⟨Blocks.reindexSL (idxEquiv a) A.val,by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))
      (Blocks.reindexSL (idxEquiv a) A.val) = 1
    rw [Blocks.reindexSL_map,A.property.2,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

theorem inclusion_comp_section : (inclusion p a m).comp (sectionHom p a m) =
    Blocks.gammaStabilization p a 1 m := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  change Matrix.fromBlocks A.val.val 0 0 (1 : Matrix Unit Unit (R p))
      ((idxEquiv a).symm i) ((idxEquiv a).symm j) =
    Matrix.fromBlocks A.val.val 0 0 (1 : Matrix (Fin 1) (Fin 1) (R p))
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)).surjective i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin 1 ≃ Fin (a+1)).surjective j
  cases i <;> cases j <;> simp [idxEquiv,Matrix.one_apply]
  intro h
  exact (h (Subsingleton.elim _ _)).elim

end

open Construction CategoryTheory
variable (p a m : ℕ)

theorem stabilization_homology_factor (j : ℕ) :
    groupHomology.map (Blocks.gammaStabilization p a 1 m)
      (QuotientCoinvariants.trivialMap _) j =
    groupHomology.map (sectionHom p a m) (QuotientCoinvariants.trivialMap _) j ≫
      groupHomology.map (inclusion p a m) (QuotientCoinvariants.trivialMap _) j := by
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr (inclusion_comp_section p a m).symm rfl j

theorem stabilization_surjective_iff_parabolic [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    Function.Surjective (groupHomology.map (Blocks.gammaStabilization p a 1 m)
      (QuotientCoinvariants.trivialMap _) j) ↔
    Function.Surjective (groupHomology.map (inclusion p a m)
      (QuotientCoinvariants.trivialMap _) j) := by
  let f := groupHomology.map (sectionHom p a m) (QuotientCoinvariants.trivialMap _) j
  let g := groupHomology.map (inclusion p a m) (QuotientCoinvariants.trivialMap _) j
  have : IsIso f := section_homology_isIso p a m hp j
  have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective f).mp inferInstance
  rw [stabilization_homology_factor]
  change Function.Surjective (g ∘ f) ↔ Function.Surjective g
  constructor
  · intro h y
    obtain ⟨x,hx⟩ := h y
    exact ⟨f x,hx⟩
  · intro h
    exact h.comp hf

theorem stabilization_injective_iff_parabolic [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    Function.Injective (groupHomology.map (Blocks.gammaStabilization p a 1 m)
      (QuotientCoinvariants.trivialMap _) j) ↔
    Function.Injective (groupHomology.map (inclusion p a m)
      (QuotientCoinvariants.trivialMap _) j) := by
  let f := groupHomology.map (sectionHom p a m) (QuotientCoinvariants.trivialMap _) j
  let g := groupHomology.map (inclusion p a m) (QuotientCoinvariants.trivialMap _) j
  have : IsIso f := section_homology_isIso p a m hp j
  have hf : Function.Surjective f := (ModuleCat.epi_iff_surjective f).mp inferInstance
  have hi : Function.Injective f := (ModuleCat.mono_iff_injective f).mp inferInstance
  rw [stabilization_homology_factor]
  change Function.Injective (g ∘ f) ↔ Function.Injective g
  constructor
  · intro h x y hxy
    obtain ⟨u,rfl⟩ := hf x
    obtain ⟨v,rfl⟩ := hf y
    exact congrArg f (h hxy)
  · intro h
    exact h.comp hi

end CoboundaryExpanders.ActualParabolic


section
open CategoryTheory
open scoped Matrix

namespace CoboundaryExpanders.F2Stability

variable {G H K : Type} [Group G] [Group H] [Group K]

abbrev hom (f : G →* H) (j : ℕ) :=
  groupHomology.map f (QuotientCoinvariants.trivialMap f) j

lemma hom_comp (f : G →* H) (g : H →* K) (j : ℕ) :
    hom (g.comp f) j = hom f j ≫ hom g j := by
  rw [← groupHomology.map_comp]
  rfl

lemma hom_id (j : ℕ) : hom (MonoidHom.id G) j = 𝟙 _ :=
  groupHomology.map_id j

lemma endomorphism_hom_eq_id (π : G →* H) (α : G →* G)
    (hπ : π.comp α = π) (j : ℕ) [Mono (hom π j)] :
    hom α j = 𝟙 _ := by
  apply (cancel_mono (hom π j)).mp
  rw [Category.id_comp, ← hom_comp, hπ]

def meetConj (S N : Subgroup G) [N.Normal] (g : G) (hg : g ∈ S) :
    ↥(S ⊓ N) →* ↥(S ⊓ N) :=
  ((MulAut.conj g).toMonoidHom.comp (S ⊓ N).subtype).codRestrict _ (by
    intro x
    exact ⟨S.mul_mem (S.mul_mem hg x.property.1) (S.inv_mem hg),
      Subgroup.Normal.conj_mem (inferInstance : N.Normal) x.val x.property.2 g⟩)

end CoboundaryExpanders.F2Stability

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)

def shear (v : Matrix (Fin a) Unit (R p)) :
    Matrix.SpecialLinearGroup (Idx a) (R p) :=
  ⟨Matrix.fromBlocks 1 v 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]⟩

lemma shear_mem (v : Matrix (Fin a) Unit (R p)) : shear p a v ∈ rowFixed p a := by
  intro j
  cases j <;> simp [shear]

lemma shear_inv (v : Matrix (Fin a) Unit (R p)) :
    (shear p a v)⁻¹ = shear p a (-v) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.fromBlocks 1 v 0 1 * Matrix.fromBlocks 1 (-v) 0 1 = 1
  rw [Matrix.fromBlocks_multiply]
  simp

def shearConj (v : Matrix (Fin a) Unit (R p)) : group p a m →* group p a m :=
  meetConj (rowFixed p a)
    (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker
    (shear p a v) (shear_mem p a v)

lemma project_comp_shearConj (v : Matrix (Fin a) Unit (R p)) :
    (project p a m).comp (shearConj p a m v) = project p a m := by
  apply MonoidHom.ext
  intro A
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.toBlocks₁₁
    ((shear p a v).val * A.val.val * ((shear p a v)⁻¹).val) =
    Matrix.toBlocks₁₁ A.val.val
  rw [shear_inv, block_form p a m A]
  simp [shear, Matrix.fromBlocks_multiply]

theorem shearConj_homology_eq_id [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (shearConj p a m v) j = 𝟙 _ := by
  have := project_homology_isIso p a m hp j
  exact endomorphism_hom_eq_id (project p a m) (shearConj p a m v)
    (project_comp_shearConj p a m v) j

local instance gammaNormal : (Gamma p a m).Normal := by
  unfold Gamma
  infer_instance

def shearFin (v : Matrix (Fin a) Unit (R p)) :
    Matrix.SpecialLinearGroup (Fin (a+1)) (R p) :=
  Blocks.reindexSL (idxEquiv a) (shear p a v)

lemma inclusion_comp_shearConj (v : Matrix (Fin a) Unit (R p)) :
    (inclusion p a m).comp (shearConj p a m v) =
      (MulAut.conjNormal (shearFin p a v) : MulAut (Gamma p (a+1) m)).toMonoidHom.comp
        (inclusion p a m) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change Blocks.reindexSL (idxEquiv a) ((shear p a v) * x.val * (shear p a v)⁻¹) =
    (Blocks.reindexSL (idxEquiv a) (shear p a v)) *
      (Blocks.reindexSL (idxEquiv a) x.val) *
      (Blocks.reindexSL (idxEquiv a) (shear p a v))⁻¹
  simp

theorem shearFin_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (shearFin p a v) : MulAut (Gamma p (a+1) m)).toMonoidHom j =
    hom (Blocks.gammaStabilization p a 1 m) j := by
  rw [← inclusion_comp_section, F2Stability.hom_comp, Category.assoc, ← F2Stability.hom_comp,
    ← inclusion_comp_shearConj, F2Stability.hom_comp, shearConj_homology_eq_id p a m hp,
    Category.id_comp]

end CoboundaryExpanders.ActualParabolic

namespace CoboundaryExpanders.MatrixDual
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "SL" => Matrix.SpecialLinearGroup

@[simp] lemma transpose_mul (x y : SL ι A) :
    (x * y).transpose = y.transpose * x.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

@[simp] lemma transpose_one : (1 : SL ι A).transpose = 1 := by
  apply Subtype.ext
  exact Matrix.transpose_one

@[simp] lemma transpose_transpose (x : SL ι A) : x.transpose.transpose = x := by
  rfl

@[simp] lemma transpose_inv (x : SL ι A) : (x⁻¹).transpose = x.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← transpose_mul, inv_mul_cancel, transpose_one]

def dual : MulAut (SL ι A) where
  toFun x := (x⁻¹).transpose
  invFun x := (x⁻¹).transpose
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp

@[simp] lemma dual_apply (x : SL ι A) : dual x = (x⁻¹).transpose := rfl

@[simp] lemma dual_dual (x : SL ι A) : dual (dual x) = x := by simp

lemma map_transpose (f : A →+* B) (x : SL ι A) :
    Matrix.SpecialLinearGroup.map f x.transpose = (Matrix.SpecialLinearGroup.map f x).transpose := rfl

lemma map_dual (f : A →+* B) (x : SL ι A) :
    Matrix.SpecialLinearGroup.map f (dual x) = dual (Matrix.SpecialLinearGroup.map f x) := by
  simp only [dual_apply, map_transpose, map_inv]

lemma reindex_dual (e : ι ≃ κ) (x : SL ι A) :
    Blocks.reindexSL e (dual x) = dual (Blocks.reindexSL e x) := by
  simp only [dual_apply, ← map_inv]
  rfl

lemma block_dual (a b : ℕ) (x : SL (Fin a) A) :
    dual (Blocks.blockSL a b x) = Blocks.blockSL a b (dual x) := by
  change ((Blocks.blockSL a b x)⁻¹).transpose =
    Blocks.blockSL a b ((x⁻¹).transpose)
  rw [← map_inv]
  apply Subtype.ext
  change (Matrix.fromBlocks (x⁻¹).val 0 0 (1 : Matrix (Fin b) (Fin b) A)).transpose =
    Matrix.fromBlocks (x⁻¹).val.transpose 0 0 1
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one]

lemma stabilize_dual (a b : ℕ) (x : SL (Fin a) A) :
    dual (Blocks.stabilizeSL a b x) = Blocks.stabilizeSL a b (dual x) := by
  change dual (Blocks.reindexSL finSumFinEquiv (Blocks.blockSL a b x)) = _
  rw [← reindex_dual, block_dual]
  rfl

open Construction
variable (p a m : ℕ)

lemma dual_mem_gamma (x : Gamma p a m) : dual x.val ∈ Gamma p a m := by
  change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (dual x.val) = 1
  rw [map_dual, x.property, map_one]

def gammaDual : MulAut (Gamma p a m) where
  toFun x := ⟨dual x.val, dual_mem_gamma p a m x⟩
  invFun x := ⟨dual x.val, dual_mem_gamma p a m x⟩
  left_inv x := Subtype.ext (dual_dual x.val)
  right_inv x := Subtype.ext (dual_dual x.val)
  map_mul' _ _ := Subtype.ext (map_mul dual _ _)

lemma gammaDual_stabilization (b : ℕ) :
    (gammaDual p (a+b) m).toMonoidHom.comp (Blocks.gammaStabilization p a b m) =
      (Blocks.gammaStabilization p a b m).comp (gammaDual p a m).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  exact Subtype.ext (stabilize_dual a b x.val)

end CoboundaryExpanders.MatrixDual

namespace CoboundaryExpanders.F2Stability
variable {G H : Type} [Group G] [Group H]

lemma hom_equiv_isIso (e : G ≃* H) (j : ℕ) : IsIso (hom e.toMonoidHom j) := by
  let i : groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j ≅
      groupHomology (Rep.trivial (ZMod 2) H (ZMod 2)) j :=
    { hom := hom e.toMonoidHom j
      inv := hom e.symm.toMonoidHom j
      hom_inv_id := by
        rw [← hom_comp]
        have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
        rw [he, hom_id]
      inv_hom_id := by
        rw [← hom_comp]
        have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by ext x; simp
        rw [he, hom_id] }
  exact i.isIso_hom

end CoboundaryExpanders.F2Stability

namespace CoboundaryExpanders.MatrixDual
open Construction F2Stability
variable (p a m : ℕ)
local instance gammaNormal : (Gamma p a m).Normal := by unfold Gamma; infer_instance

lemma gammaDual_conj (g : Matrix.SpecialLinearGroup (Fin a) (R p)) :
    (gammaDual p a m).toMonoidHom.comp (MulAut.conjNormal g).toMonoidHom =
      (MulAut.conjNormal (dual g)).toMonoidHom.comp (gammaDual p a m).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change dual (g * x.val * g⁻¹) = dual g * dual x.val * (dual g)⁻¹
  simp

theorem dual_fixes_stable_image (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) (j : ℕ)
    (hg : hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (dual g) : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j := by
  have := hom_equiv_isIso (gammaDual p a m) j
  apply (cancel_epi (hom (gammaDual p a m).toMonoidHom j)).mp
  have hd : hom (gammaDual p a m).toMonoidHom j ≫
      hom (Blocks.gammaStabilization p a 1 m) j =
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (gammaDual p (a+1) m).toMonoidHom j := by
    rw [← F2Stability.hom_comp, ← F2Stability.hom_comp, gammaDual_stabilization]
  rw [← Category.assoc, hd, Category.assoc, ← F2Stability.hom_comp,
    ← gammaDual_conj, F2Stability.hom_comp, ← Category.assoc, hg]

end CoboundaryExpanders.MatrixDual

namespace CoboundaryExpanders.ActualParabolic
open Construction F2Stability
variable (p a m : ℕ)
local instance gammaNormalLast : (Gamma p a m).Normal := by unfold Gamma; infer_instance

theorem lowerShear_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (v : Matrix (Fin a) Unit (R p)) (j : ℕ) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal (MatrixDual.dual (shearFin p a v)) :
        MulAut (Gamma p (a+1) m)).toMonoidHom j =
    hom (Blocks.gammaStabilization p a 1 m) j :=
  MatrixDual.dual_fixes_stable_image p a m _ j
    (shearFin_fixes_stable_image p a m hp v j)

end CoboundaryExpanders.ActualParabolic

end

open CategoryTheory

namespace CoboundaryExpanders.Actions
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) [S.Normal] {X : ModuleCat.{u} k}

def fixingImage (j : ℕ) (f : X ⟶ groupHomology (Rep.trivial k S k) j) : Subgroup G where
  carrier := {g | f ≫ conjugation S g j = f}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change f ≫ conjugation S (g*h) j = f
    rw [conjugation_mul, ← Category.assoc, hh, hg]
  inv_mem' := by
    intro g hg
    change f ≫ conjugation S g⁻¹ j = f
    have he := conjugation_mul (k := k) S g⁻¹ g j
    rw [inv_mul_cancel, conjugation_one] at he
    calc
      f ≫ conjugation S g⁻¹ j = (f ≫ conjugation S g j) ≫ conjugation S g⁻¹ j := by rw [hg]
      _ = f := by rw [Category.assoc, ← he, Category.comp_id]

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.ActualParabolic
open Construction Elementary F2Stability Actions
variable (p a m : ℕ)
local instance gammaNorm : (Gamma p a m).Normal := by unfold Gamma; infer_instance

@[simp] lemma idxEquiv_inl (i : Fin a) : idxEquiv a (Sum.inl i) = i.castSucc := rfl
@[simp] lemma idxEquiv_inr : idxEquiv a (Sum.inr ()) = Fin.last a := rfl

lemma upperRoot_shear (i : Fin a) (c : R p) :
    E (show i.castSucc ≠ Fin.last a by exact Fin.castSucc_ne_last i) c =
      shearFin p a (fun j _ => if j = i then c else 0) := by
  apply Matrix.SpecialLinearGroup.ext
  intro x y
  obtain ⟨x,rfl⟩ := (idxEquiv a).surjective x
  obtain ⟨y,rfl⟩ := (idxEquiv a).surjective y
  change (Matrix.transvection i.castSucc (Fin.last a) c) _ _ =
    (Blocks.reindexSL (idxEquiv a) (shear p a (fun j _ => if j=i then c else 0))) _ _
  rw [Blocks.reindexSL_apply]
  cases x with
  | inl x => cases y with
    | inl y => simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, Matrix.one_apply, (Fin.castSucc_ne_last _).symm]
    | inr y => cases y; simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, eq_comm]
  | inr x => cases x; cases y with
    | inl y => simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks, (Fin.castSucc_ne_last _).symm]
    | inr y => cases y; simp [Matrix.transvection, Matrix.single, shear, Matrix.fromBlocks]

lemma dual_root {i j : Fin a} (hij : i ≠ j) (c : R p) :
    MatrixDual.dual (E hij c) = E hij.symm (-c) := by
  rw [MatrixDual.dual_apply, Matrix.SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (Matrix.transvection i j (-c)).transpose = Matrix.transvection j i (-c)
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]

abbrev stableFixed (j : ℕ) :=
  fixingImage (Gamma p (a+1) m) j (hom (Blocks.gammaStabilization p a 1 m) j)

lemma upper_root_mem [Fact p.Prime] (hp : Odd p) (i : Fin a) (c : R p) (j : ℕ) :
    E (Fin.castSucc_ne_last i) c ∈ stableFixed p a m j := by
  change hom (Blocks.gammaStabilization p a 1 m) j ≫
    hom (MulAut.conjNormal (E (Fin.castSucc_ne_last i) c)).toMonoidHom j = _
  rw [upperRoot_shear]
  exact shearFin_fixes_stable_image p a m hp _ j

lemma lower_root_mem [Fact p.Prime] (hp : Odd p) (i : Fin a) (c : R p) (j : ℕ) :
    E (Fin.castSucc_ne_last i).symm c ∈ stableFixed p a m j := by
  have ht := lowerShear_fixes_stable_image p a m hp (fun x _ => if x=i then -c else 0) j
  rw [← upperRoot_shear, dual_root, neg_neg] at ht
  exact ht

theorem polynomial_fixes_stable_image [Fact p.Prime] (hp : Odd p)
    (j : ℕ) (g : Matrix.SpecialLinearGroup (Fin (a+1)) (R p)) :
    hom (Blocks.gammaStabilization p a 1 m) j ≫
      hom (MulAut.conjNormal g : MulAut (Gamma p (a+1) m)).toMonoidHom j =
        hom (Blocks.gammaStabilization p a 1 m) j := by
  change g ∈ stableFixed p a m j
  apply polynomial_SL_mem_of_roots
  intro x y hxy c
  by_cases hx : x = Fin.last a
  · subst x
    obtain ⟨y,rfl⟩ := Fin.eq_castSucc_of_ne_last (Ne.symm hxy)
    exact lower_root_mem p a m hp y c j
  · by_cases hy : y = Fin.last a
    · subst y
      obtain ⟨x,rfl⟩ := Fin.eq_castSucc_of_ne_last hx
      exact upper_root_mem p a m hp x c j
    · obtain ⟨x,rfl⟩ := Fin.eq_castSucc_of_ne_last hx
      obtain ⟨y,rfl⟩ := Fin.eq_castSucc_of_ne_last hy
      simpa only [mul_one] using E_path_mem (stableFixed p a m j)
        (Fin.castSucc_ne_last x) (Fin.castSucc_ne_last y).symm hxy
        (upper_root_mem p a m hp x c j) (lower_root_mem p a m hp y 1 j)

end CoboundaryExpanders.ActualParabolic

end

end OAI
