import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.CutCircleIndex
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! Split flags and their matrix equations, following *Integral points on character varieties of curves*. -/

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties
open scoped Classical Matrix

/-- The coordinate prefix attached to a split finite filtration. -/
def coordinatePrefix (R : Type*) [CommRing R] {α : Type*}
    (a : α → ℕ) (k : ℕ) : Submodule R (α → R) where
  carrier := {u | ∀ t, k ≤ a t → u t = 0}
  add_mem' hu hv t ht := by simp [hu t ht,hv t ht]
  zero_mem' t ht := rfl
  smul_mem' r u hu t ht := by simp [hu t ht]

def coordinateGrade (R : Type*) [CommRing R] {α : Type*}
    (a : α → ℕ) (k : ℕ) : (α → R) →ₗ[R] ({t // a t = k} → R) where
  toFun u t := u t.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def filteredMatrixStabilizer {R : Type*} [CommRing R] {α β : Type*}
    (a : α → ℕ) (b : β → ℕ) : Submodule R (Matrix α β R) where
  carrier := {M | ∀ i j, b j ≤ a i → M i j=0}
  zero_mem' _ _ _ := rfl
  add_mem' hM hN i j h := by simp [hM i j h,hN i j h]
  smul_mem' r M hM i j h := by simp [hM i j h]

/-- Free blocks in the identified-quotient lift itself. -/
def retainedLiftEntries {α β : Type*} (a : α → ℕ) (b : β → ℕ) :=
  {p : α × β // b p.2 ≤ a p.1}

/-- Additional stabilizer blocks after refining a coarse block. -/
def refinementFiberEntries {α β : Type*} (a : α → ℕ) (b : β → ℕ) (f : ℕ → ℕ) :=
  {p : α × β // a p.1 < b p.2 ∧ f (a p.1)=f (b p.2)}

lemma filteredMatrixStabilizer_iff {R : Type*} [CommRing R] {α β : Type*}
    [Fintype β] (a : α → ℕ) (b : β → ℕ) (M : Matrix α β R) :
    M ∈ filteredMatrixStabilizer a b ↔
      ∀ k q, q ∈ coordinatePrefix R b (k+1) →
        M *ᵥ q ∈ coordinatePrefix R a k := by
  constructor
  · intro hM k q hq i hi
    apply Finset.sum_eq_zero
    intro j _
    change M i j * q j = 0
    by_cases h : b j ≤ a i
    · rw [hM i j h,zero_mul]
    · rw [hq j (by omega),mul_zero]
  · intro hM i j hij
    have hq : Pi.single j (1:R) ∈ coordinatePrefix R b (b j+1) := by
      intro t ht
      have hne : t ≠ j := by intro H; subst t; omega
      exact Pi.single_eq_of_ne hne _
    have H := hM (b j) (Pi.single j 1) hq i hij
    simpa [Matrix.mulVec_single,Matrix.col] using H


end IntegralCharacterVarieties
namespace IntegralCharacterVarieties
open scoped Classical
variable {R : Type*} [CommRing R] {α : Type*} (a : α → ℕ)

lemma prefix_zero_eq_bot : coordinatePrefix R a 0=⊥ := by
  ext v
  constructor
  · intro hv
    change v=0
    ext i
    exact hv i (Nat.zero_le _)
  · intro hv
    have hv0 : v=0 := hv
    subst v
    exact (coordinatePrefix R a 0).zero_mem

lemma prefix_mono {k l : ℕ} (hkl : k ≤ l) :
    coordinatePrefix R a k ≤ coordinatePrefix R a l := by
  intro v hv i hi
  exact hv i (hkl.trans hi)

/-- Equality of parallel identified flags in a fixed split basis: not only preservation of dimensions, but equality of each submodule and each induced coordinate projection on the named grade. -/
def SameCoordinateFlag (e : (α → R) ≃ₗ[R] (α → R)) : Prop :=
  (∀ k, (coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R a k) ∧
  ∀ k v, v ∈ coordinatePrefix R a (k+1) →
    coordinateGrade R a k (e v)=coordinateGrade R a k v

/-- The strict-upper criterion is valid over every full coefficient ring. -/
theorem sameCoordinateFlag_iff_lowering (e : (α → R) ≃ₗ[R] (α → R)) :
    SameCoordinateFlag a e ↔ ∀ k v, v ∈ coordinatePrefix R a (k+1) →
      e v-v ∈ coordinatePrefix R a k := by
  constructor
  · rintro ⟨hF,hG⟩ k v hv i hi
    have hev : e v ∈ coordinatePrefix R a (k+1) := by
      rw [← hF (k+1)]
      exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
    change e v i-v i=0
    by_cases he : a i=k
    · have hg := congrFun (hG k v hv) ⟨i,he⟩
      exact sub_eq_zero.mpr hg
    · have hki : k+1 ≤ a i := by omega
      rw [hev i hki,hv i hki,sub_self]
  · intro h
    have hforward : ∀ k v, v ∈ coordinatePrefix R a k → e v ∈ coordinatePrefix R a k := by
      intro k v hv
      cases k with
      | zero =>
        rw [prefix_zero_eq_bot] at hv ⊢
        have hv0 : v=0 := hv
        simp only [hv0,map_zero,Submodule.mem_bot]
      | succ k =>
        have hh := h k v hv
        have hh' := prefix_mono a (Nat.le_succ k) hh
        simpa only [sub_add_cancel] using (coordinatePrefix R a (k+1)).add_mem hh' hv
    constructor
    · intro k
      induction k with
      | zero => simp [prefix_zero_eq_bot]
      | succ k ih =>
        apply le_antisymm
        · rintro _ ⟨v,hv,rfl⟩
          exact hforward (k+1) v hv
        · intro v hv
          have hd := h k v hv
          rw [← ih] at hd
          rcases Submodule.mem_map.mp hd with ⟨u,hu,heu⟩
          apply Submodule.mem_map.mpr
          refine ⟨v-u,(coordinatePrefix R a (k+1)).sub_mem hv (prefix_mono a (Nat.le_succ k) hu),?_⟩
          simp only [map_sub]
          change e v-e u=v
          change e u=e v-v at heu
          rw [heu]
          abel
    · intro k v hv
      ext i
      have hh := h k v hv i.val (le_of_eq i.property.symm)
      exact sub_eq_zero.mp hh

variable {V : Type*} [AddCommGroup V] [Module R V]

/-- A freely split flag with its named quotient identifications. -/
def framedPrefix (e : (α → R) ≃ₗ[R] V) (k : ℕ) : Submodule R V :=
  (coordinatePrefix R a k).map e.toLinearMap

def framedGrade (e : (α → R) ≃ₗ[R] V) (k : ℕ) : V →ₗ[R] ({i // a i=k} → R) :=
  (coordinateGrade R a k).comp e.symm.toLinearMap

/-- Equality includes the quotient maps, not just the underlying flag. -/
def SameFramedFlag (e f : (α → R) ≃ₗ[R] V) : Prop :=
  (∀ k, framedPrefix a e k=framedPrefix a f k) ∧
  ∀ k v, v ∈ framedPrefix a e (k+1) → framedGrade a e k v=framedGrade a f k v

lemma sameFramedFlag_iff (e f : (α → R) ≃ₗ[R] V) :
    SameFramedFlag a e f ↔ SameCoordinateFlag a (e.trans f.symm) := by
  constructor
  · rintro ⟨hF,hG⟩
    constructor
    · intro k
      apply le_antisymm
      · rintro _ ⟨v,hv,rfl⟩
        have he : e v ∈ framedPrefix a e k := Submodule.mem_map.mpr ⟨v,hv,rfl⟩
        rw [hF k] at he
        rcases Submodule.mem_map.mp he with ⟨w,hw,hew⟩
        change f.symm (e v) ∈ coordinatePrefix R a k
        change f w=e v at hew
        rw [← hew,LinearEquiv.symm_apply_apply]
        exact hw
      · intro v hv
        have hf : f v ∈ framedPrefix a f k := Submodule.mem_map.mpr ⟨v,hv,rfl⟩
        rw [← hF k] at hf
        rcases Submodule.mem_map.mp hf with ⟨w,hw,hew⟩
        apply Submodule.mem_map.mpr
        refine ⟨w,hw,?_⟩
        change f.symm (e w)=v
        change e w=f v at hew
        rw [hew,LinearEquiv.symm_apply_apply]
    · intro k v hv
      have hg := hG k (e v) (Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
      simpa only [framedGrade,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply,LinearEquiv.trans_apply] using hg.symm
  · rintro ⟨hF,hG⟩
    constructor
    · intro k
      apply le_antisymm
      · rintro _ ⟨v,hv,rfl⟩
        have hh : (e.trans f.symm) v ∈ coordinatePrefix R a k := by
          rw [← hF k]
          exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
        exact Submodule.mem_map.mpr ⟨(e.trans f.symm) v,hh,by simp⟩
      · rintro _ ⟨v,hv,rfl⟩
        rw [← hF k] at hv
        rcases Submodule.mem_map.mp hv with ⟨w,hw,hew⟩
        exact Submodule.mem_map.mpr ⟨w,hw,by simpa only [LinearEquiv.coe_coe,
          LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using congrArg f hew⟩
    · rintro k _ ⟨v,hv,rfl⟩
      simpa only [framedGrade,LinearMap.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply,LinearEquiv.trans_apply] using (hG k v hv).symm

end IntegralCharacterVarieties
namespace IntegralCharacterVarieties.HomTransport
open scoped Classical Matrix
variable {R : Type*} [CommRing R] {α β : Type*}
variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The coefficient matrix for h ↦ U h Q (column indices on Hom). -/
def coefficients (U : Matrix α α R) (Q : Matrix β β R) :
    Matrix (α × β) (α × β) R := Matrix.kronecker U Q.transpose

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] lemma coefficients_apply (U : Matrix α α R) (Q : Matrix β β R)
    (i k : α) (j l : β) : coefficients U Q (i,j) (k,l)=U i k*Q l j := rfl

omit [DecidableEq α] [DecidableEq β] in
lemma coefficients_mul (U V : Matrix α α R) (Q T : Matrix β β R) :
    coefficients U Q * coefficients V T=coefficients (U*V) (T*Q) := by
  unfold coefficients Matrix.kronecker
  rw [Matrix.transpose_mul]
  exact (Matrix.mul_kronecker_mul U V Q.transpose T.transpose).symm

omit [Fintype α] [Fintype β] in
@[simp] lemma coefficients_one : coefficients (1 : Matrix α α R) (1 : Matrix β β R)=1 := by
  simp only [coefficients,Matrix.transpose_one]
  exact Matrix.one_kronecker_one

/-- Every change of the named U,Q bases induces this invertible matrix on the free module of extension entries. Inverses are polynomial in the inverse base-change entries retained in the GL presentation. -/
def unit (U : (Matrix α α R)ˣ) (Q : (Matrix β β R)ˣ) :
    (Matrix (α × β) (α × β) R)ˣ where
  val := coefficients (U : Matrix α α R) (↑Q⁻¹ : Matrix β β R)
  inv := coefficients (↑U⁻¹ : Matrix α α R) (Q : Matrix β β R)
  val_inv := by
    rw [coefficients_mul,Units.mul_inv,Units.mul_inv,coefficients_one]
  inv_val := by
    rw [coefficients_mul,Units.inv_mul,Units.inv_mul,coefficients_one]

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
/-- Coefficient-ring functoriality, including at non-field points. -/
lemma coefficients_map {S : Type*} [CommRing S] (φ : R →+* S)
    (U : Matrix α α R) (Q : Matrix β β R) :
    (coefficients U Q).map φ=coefficients (U.map φ) (Q.map φ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  exact map_mul φ _ _

omit [DecidableEq α] [DecidableEq β] in
lemma coefficients_mulVec (U : Matrix α α R) (Q : Matrix β β R)
    (h : α × β → R) (i : α) (j : β) :
    (coefficients U Q *ᵥ h) (i,j)=(U * (Matrix.of fun k l => h (k,l)) * Q) i j := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,coefficients_apply,
    Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.of_apply]
  ring

/-- Linear equivalence defined by a transport and its inverse. -/
def matrixUnitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι R)ˣ) : (ι → R) ≃ₗ[R] (ι → R) where
  toLinearMap := Matrix.toLin' (U : Matrix ι ι R)
  invFun := fun v => (↑U⁻¹ : Matrix ι ι R) *ᵥ v
  left_inv v := by
    change (↑U⁻¹ : Matrix ι ι R) *ᵥ ((U : Matrix ι ι R) *ᵥ v)=v
    rw [Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec]
  right_inv v := by
    change (U : Matrix ι ι R) *ᵥ ((↑U⁻¹ : Matrix ι ι R) *ᵥ v)=v
    rw [Matrix.mulVec_mulVec,Units.mul_inv,Matrix.one_mulVec]

@[simp] lemma matrixUnitEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι R)ˣ) (v : ι → R) : matrixUnitEquiv U v=(U : Matrix ι ι R) *ᵥ v := rfl

@[simp] lemma matrixUnitEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (Matrix ι ι R)ˣ) (v : ι → R) :
    (matrixUnitEquiv U).symm v=(↑U⁻¹ : Matrix ι ι R) *ᵥ v := rfl

lemma hom_coordinate_transform (U : (Matrix α α R)ˣ) (Q : (Matrix β β R)ˣ)
    (h : α × β → R) (v : β → R) :
    matrixUnitEquiv U ((Matrix.of fun i j => h (i,j)) *ᵥ (matrixUnitEquiv Q).symm v)=
      (Matrix.of fun i j => (matrixUnitEquiv (unit U Q) h) (i,j)) *ᵥ v := by
  change (U : Matrix α α R) *ᵥ ((Matrix.of fun i j => h (i,j)) *ᵥ ((↑Q⁻¹ : Matrix β β R) *ᵥ v))=_
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  congr 1
  ext i j
  exact (coefficients_mulVec (U : Matrix α α R) (↑Q⁻¹ : Matrix β β R) h i j).symm

end IntegralCharacterVarieties.HomTransport
namespace IntegralCharacterVarieties
open scoped Matrix Classical
open HomTransport
variable {R : Type*} [CommRing R] {α : Type*} [Fintype α] [DecidableEq α]
variable (a : α → ℕ)

/-- Exact split-frame polynomial equations for equality of flags and identified quotients. Both inverse matrices are variables in the ambient GL scheme; no inversion is added to the integers. -/
theorem sameFramedFlag_matrix_iff (P Q : (Matrix α α R)ˣ) :
    SameFramedFlag a (matrixUnitEquiv P) (matrixUnitEquiv Q) ↔
    ∀ i j, a j ≤ a i → ((↑Q⁻¹ : Matrix α α R)*(P : Matrix α α R)) i j=
      (1 : Matrix α α R) i j := by
  rw [sameFramedFlag_iff,sameCoordinateFlag_iff_lowering]
  have hM := filteredMatrixStabilizer_iff a a
    ((↑Q⁻¹ : Matrix α α R)*(P : Matrix α α R)-1)
  have hact : ∀ v : α → R,
      ((↑Q⁻¹ : Matrix α α R)*(P : Matrix α α R)-1) *ᵥ v=
      ((matrixUnitEquiv P).trans (matrixUnitEquiv Q).symm) v-v := by
    intro v
    rw [Matrix.sub_mulVec,Matrix.one_mulVec]
    congr 1
    change ((↑Q⁻¹ : Matrix α α R)*(P : Matrix α α R)) *ᵥ v=
      (↑Q⁻¹ : Matrix α α R) *ᵥ ((P : Matrix α α R) *ᵥ v)
    exact (Matrix.mulVec_mulVec _ _ _).symm
  simp only [hact] at hM
  rw [← hM]
  change (∀ i j, a j ≤ a i → ((↑Q⁻¹ : Matrix α α R)*(P : Matrix α α R)) i j-
    (1 : Matrix α α R) i j=0) ↔ _
  simp only [sub_eq_zero]

end IntegralCharacterVarieties
open scoped Classical Matrix

end

end OAI
