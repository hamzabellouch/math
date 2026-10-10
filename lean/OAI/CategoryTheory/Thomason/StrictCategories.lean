import Mathlib
import OAI.CategoryTheory.Thomason.NormalizedChains

namespace OAI

/-! Strict Categories. -/

noncomputable section
universe u v w z


namespace Thomason


namespace OmegaCategory

variable (C : OmegaCategory.{u})

@[simp] lemma source_source_self (k : ℕ) (x : C.Cell) :
    C.source k (C.source k x) = C.source k x := by
  simp [C.source_source]

@[simp] lemma target_target_self (k : ℕ) (x : C.Cell) :
    C.target k (C.target k x) = C.target k x := by
  simp [C.target_target]

@[simp] lemma source_target_self (k : ℕ) (x : C.Cell) :
    C.source k (C.target k x) = C.target k x := by
  simp [C.source_target]

@[simp] lemma target_source_self (k : ℕ) (x : C.Cell) :
    C.target k (C.source k x) = C.source k x := by
  simp [C.target_source]

lemma target_eq_self_of_source_eq_self {k : ℕ} {x : C.Cell}
    (h : C.source k x = x) : C.target k x = x := by
  rw [← h, C.target_source_self]

lemma source_eq_self_of_target_eq_self {k : ℕ} {x : C.Cell}
    (h : C.target k x = x) : C.source k x = x := by
  rw [← h, C.source_target_self]

lemma source_fixed_upwards {i j : ℕ} (hij : i ≤ j) {x : C.Cell}
    (h : C.source i x = x) : C.source j x = x := by
  rw [← h, C.source_source, min_eq_right hij]

def Cells (k : ℕ) := {x : C.Cell // C.source k x = x}


lemma source_composable {k i : ℕ} (hki : k < i) {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    C.target k (C.source i x) = C.source k (C.source i y) := by
  rw [C.target_source, ite_eq_left hki, C.source_source, min_eq_left (le_of_lt hki)]
  exact h

lemma target_composable {k i : ℕ} (hki : k < i) {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    C.target k (C.target i x) = C.source k (C.target i y) := by
  rw [C.target_target, min_eq_left (le_of_lt hki), C.source_target, ite_eq_left hki]
  exact h

lemma assoc_composable_left {k : ℕ} {x y z : C.Cell}
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.target k (C.comp k x y hxy) = C.source k z := by
  rw [C.target_comp_le k k le_rfl]
  exact hyz

lemma assoc_composable_right {k : ℕ} {x y z : C.Cell}
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.target k x = C.source k (C.comp k y z hyz) := by
  rw [C.source_comp_le k k le_rfl]
  exact hxy


namespace Functor

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {B : OmegaCategory.{w}}

lemma map_composable (F : Functor C D) {k : ℕ} {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    D.target k (F.map x) = D.source k (F.map y) := by
  rw [← F.map_target, ← F.map_source, h]


end Functor


end OmegaCategory
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason


attribute [instance] DirectedComplex.group

namespace DirectedComplex


namespace Table

variable {K : DirectedComplex.{u}}


@[simp] lemma truncate_row (k : ℕ) (e : Bool) (x : Table K) (p : ℕ) (b : Bool) :
    (truncate k e x).row p b =
      if p < k then x.row p b else if p = k then x.row p e else 0 := rfl

lemma truncate_truncate (i j : ℕ) (e f : Bool) (x : Table K) :
    truncate i e (truncate j f x) =
      if i < j then truncate i e x else truncate j f x := by
  ext p b
  by_cases hij : i < j
  · simp only [hij, ite_eq_left, truncate_row]
    by_cases hpi : p < i
    · have hpj : p < j := lt_trans hpi hij
      simp [hpi, hpj]
    · by_cases hpe : p = i
      · subst p
        simp [hij]
      · simp [hpi, hpe]
  · simp only [hij, ite_false, truncate_row]
    by_cases hpj : p < j
    · have hpi : p < i := by omega
      simp [hpj, hpi]
    · by_cases hpje : p = j
      · subst p
        by_cases hji : j < i
        · simp [hji]
        · have hi : i = j := by omega
          subst i
          simp
      · by_cases hpi : p < i
        · simp [hpi, hpj, hpje]
        · by_cases hpie : p = i
          · subst p
            simp [hij]
          · simp [hpi, hpie, hpj, hpje]

lemma truncate_truncate_same (i j : ℕ) (e : Bool) (x : Table K) :
    truncate i e (truncate j e x) = truncate (min i j) e x := by
  rw [truncate_truncate]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]

lemma lower_rows_eq {k : ℕ} {x y : Table K}
    (h : truncate k true x = truncate k false y) {p : ℕ} (hp : p < k) (b : Bool) :
    x.row p b = y.row p b := by
  have hr := congrArg (fun z : Table K => z.row p b) h
  simpa only [truncate_row, hp, ite_eq_left] using hr

lemma matching_row_eq {k : ℕ} {x y : Table K}
    (h : truncate k true x = truncate k false y) : x.row k true = y.row k false := by
  have hr := congrArg (fun z : Table K => z.row k false) h
  simpa using hr


@[simp] lemma comp_row (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y) (p : ℕ) (b : Bool) :
    (comp k x y h).row p b = if p < k then x.row p b else if p = k then
      (if b then y.row p true else x.row p false) else x.row p b + y.row p b := rfl

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    truncate i false (comp k x y h) = truncate i false x := by
  ext p b
  by_cases hpi : p < i
  · have hpk : p < k := lt_of_lt_of_le hpi hik
    simp [hpi, hpk]
  · by_cases hpe : p = i
    · subst p
      by_cases hik' : i < k
      · simp [hik']
      · have he : i = k := by omega
        subst i
        simp
    · simp [hpi, hpe]

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    truncate i true (comp k x y h) = truncate i true y := by
  ext p b
  by_cases hpi : p < i
  · have hpk : p < k := lt_of_lt_of_le hpi hik
    simp only [truncate_row, ite_eq_left hpi, comp_row, ite_eq_left hpk]
    exact lower_rows_eq h hpk b
  · by_cases hpe : p = i
    · subst p
      by_cases hik' : i < k
      · simpa [hik'] using lower_rows_eq h hik' true
      · have he : i = k := by omega
        subst i
        simp
    · simp [hpi, hpe]

lemma truncate_comp_gt (i k : ℕ) (hki : k < i) (e : Bool) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (h' : truncate k true (truncate i e x) = truncate k false (truncate i e y)) :
    truncate i e (comp k x y h) = comp k (truncate i e x) (truncate i e y) h' := by
  ext p b
  by_cases hpk : p < k
  · have hpi : p < i := lt_trans hpk hki
    simp [hpk, hpi]
  · by_cases hpe : p = k
    · subst p
      simp [hki]
    · by_cases hpi : p < i
      · simp [hpk, hpe, hpi]
      · by_cases hpie : p = i
        · subst p
          have hik : ¬i < k := by omega
          have hie : ¬i = k := by omega
          simp [hik, hie]
        · simp [hpk, hpe, hpi, hpie]

lemma unit_left (k : ℕ) (x : Table K)
    (h : truncate k true (truncate k false x) = truncate k false x) :
    comp k (truncate k false x) x h = x := by
  ext p b
  by_cases hp : p < k
  · simp [hp]
  · by_cases he : p = k
    · subst p
      cases b <;> simp
    · simp [hp, he]

lemma unit_right (k : ℕ) (x : Table K)
    (h : truncate k true x = truncate k false (truncate k true x)) :
    comp k x (truncate k true x) h = x := by
  ext p b
  by_cases hp : p < k
  · simp [hp]
  · by_cases he : p = k
    · subst p
      cases b <;> simp
    · simp [hp, he]

lemma assoc (k : ℕ) (x y z : Table K)
    (hxy : truncate k true x = truncate k false y)
    (hyz : truncate k true y = truncate k false z)
    (hxy_z : truncate k true (comp k x y hxy) = truncate k false z)
    (hx_yz : truncate k true x = truncate k false (comp k y z hyz)) :
    comp k (comp k x y hxy) z hxy_z = comp k x (comp k y z hyz) hx_yz := by
  ext p b
  by_cases hp : p < k
  · simp [hp]
  · by_cases he : p = k
    · subst p
      cases b <;> simp
    · simp [hp, he, add_assoc]

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : Table K)
    (hab : truncate l true a = truncate l false b)
    (hcd : truncate l true c = truncate l false d)
    (hac : truncate k true a = truncate k false c)
    (hbd : truncate k true b = truncate k false d)
    (hab_cd : truncate k true (comp l a b hab) = truncate k false (comp l c d hcd))
    (hac_bd : truncate l true (comp k a c hac) = truncate l false (comp k b d hbd)) :
    comp k (comp l a b hab) (comp l c d hcd) hab_cd =
      comp l (comp k a c hac) (comp k b d hbd) hac_bd := by
  ext p e
  by_cases hpk : p < k
  · have hpl : p < l := lt_trans hpk hkl
    simp [hpk, hpl]
  · by_cases hpe : p = k
    · subst p
      cases e <;> simp [hkl]
    · by_cases hpl : p < l
      · simp [hpk, hpe, hpl]
      · by_cases hple : p = l
        · subst p
          have hlk : ¬l < k := by omega
          have hlke : ¬l = k := by omega
          cases e <;> simp [hlk, hlke]
        · simp only [comp_row, ite_eq_right hpk, ite_eq_right hpe, ite_eq_right hpl, ite_eq_right hple]
          abel

lemma finite_dimension (x : Table K) : ∃ k, truncate k false x = x := by
  obtain ⟨k, hk⟩ := x.bounded
  have ht : x.row k true = x.row k false := by
    have hb := x.boundary k false
    rw [hk (k+1) (by omega) false, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  refine ⟨k, ?_⟩
  ext p b
  by_cases hp : p < k
  · simp [hp]
  · by_cases he : p = k
    · subst p
      cases b <;> simp [ht]
    · have hkp : k < p := by omega
      simp [hp, he, hk p hkp b]

end Table
end DirectedComplex
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex


namespace Hom

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}


@[simp] lemma table_row (f : Hom K L) (x : Table K) (p : ℕ) (b : Bool) :
    (f.table x).row p b = f.map p (x.row p b) := rfl

lemma table_truncate (f : Hom K L) (k : ℕ) (b : Bool) (x : Table K) :
    f.table (Table.truncate k b x) = Table.truncate k b (f.table x) := by
  ext p e
  simp only [table_row, Table.truncate_row]
  split_ifs <;> simp only [map_zero]

lemma table_comp (f : Hom K L) (k : ℕ) (x y : Table K)
    (h : Table.truncate k true x = Table.truncate k false y)
    (h' : Table.truncate k true (f.table x) = Table.truncate k false (f.table y)) :
    f.table (Table.comp k x y h) = Table.comp k (f.table x) (f.table y) h' := by
  ext p e
  simp only [table_row, Table.comp_row]
  split_ifs <;> simp only [map_add]


end Hom


end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]


@[simp] lemma emptyCoefficient_bracket (l : List E) :
    emptyCoefficient (bracket l) = if l = [] then 1 else 0 := by
  classical
  by_cases hl : l = []
  · subst l
    simp [emptyCoefficient, bracket_of_pairwise List.Pairwise.nil, emptyWord]
  · by_cases hs : l.Pairwise (· < ·)
    · have hw : (⟨l, hs⟩ : Word E) ≠ emptyWord := by
        intro he
        exact hl (congrArg Subtype.val he)
      simp [emptyCoefficient, bracket_of_pairwise hs, hw, hl]
    · simp [bracket_of_not_pairwise hs, hl]

lemma emptyCoefficient_map {D : Type v} [PartialOrder D] (f : E →o D) (c : Chains E) :
    emptyCoefficient (map f c) = emptyCoefficient c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul, map_bracket _ (l.property.imp fun h => le_of_lt h),
      emptyCoefficient_bracket, List.map_eq_nil_iff]


end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

@[simp] lemma complexMap_id : complexMap (OrderHom.id : E →o E) =
    DirectedComplex.Hom.id (complex E) := by
  ext p x
  apply Subtype.ext
  exact map_id x.val

lemma complexMap_comp {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]
    (f : E →o D) (g : D →o B) : complexMap (g.comp f) =
      DirectedComplex.Hom.comp (complexMap f) (complexMap g) := by
  ext p x
  apply Subtype.ext
  exact map_comp f g x.val

open CategoryTheory


end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


abbrev Oriental (m : ℕ) : OmegaCategory.{0} := orientals.obj (.mk m)


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable (K : DirectedComplex.{u})

abbrev CylinderChain : ℕ → Type u
  | 0 => K.Chain 0 × K.Chain 0
  | p+1 => K.Chain (p+1) × K.Chain (p+1) × K.Chain p

abbrev cylinderChainGroup (p : ℕ) : AddCommGroup (CylinderChain K p) :=
  match p with
  | 0 => inferInstanceAs (AddCommGroup (K.Chain 0 × K.Chain 0))
  | q+1 => inferInstanceAs (AddCommGroup (K.Chain (q+1) × K.Chain (q+1) × K.Chain q))

attribute [instance] cylinderChainGroup

def cylinderDifferential : (p : ℕ) → CylinderChain K (p+1) →+ CylinderChain K p
  | 0 =>
    { toFun := fun x => (K.d 0 x.1 - x.2.2, K.d 0 x.2.1 + x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp <;> abel }
  | p+1 =>
    { toFun := fun x => (K.d (p+1) x.1 - ((-1 : ℤ)^(p+1)) • x.2.2,
        K.d (p+1) x.2.1 + ((-1 : ℤ)^(p+1)) • x.2.2, K.d p x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp [smul_add] <;> abel }

lemma cylinderDifferential_sq (p : ℕ) (x : CylinderChain K (p+2)) :
    cylinderDifferential K p (cylinderDifferential K (p+1) x) = 0 := by
  cases p with
  | zero =>
    apply Prod.ext <;> simp [cylinderDifferential, K.d_d]
  | succ p =>
    apply Prod.ext
    · simp [cylinderDifferential, K.d_d, pow_succ]
    · apply Prod.ext <;> simp [cylinderDifferential, K.d_d, pow_succ]

def cylinderPositive : (p : ℕ) → AddSubmonoid (CylinderChain K p)
  | 0 => (K.positive 0).prod (K.positive 0)
  | p+1 => (K.positive (p+1)).prod ((K.positive (p+1)).prod (K.positive p))

abbrev cylinder : DirectedComplex.{u} where
  Chain := CylinderChain K
  group := cylinderChainGroup K
  d := cylinderDifferential K
  d_d := cylinderDifferential_sq K
  augmentation :=
    { toFun := fun x => K.augmentation x.1 + K.augmentation x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  augmentation_d x := by
    change K.augmentation (K.d 0 x.1 - x.2.2) +
      K.augmentation (K.d 0 x.2.1 + x.2.2) = 0
    simp [K.augmentation_d]
  positive := cylinderPositive K

def cylinderEndpointMap (b : Bool) : (p : ℕ) → K.Chain p →+ CylinderChain K p
  | 0 =>
    { toFun := fun x => if b then (0, x) else (x, 0)
      map_zero' := by cases b <;> rfl
      map_add' := by cases b <;> intros <;> simp }
  | p+1 =>
    { toFun := fun x => if b then (0, x, 0) else (x, 0, 0)
      map_zero' := by cases b <;> rfl
      map_add' := by cases b <;> intros <;> simp }

def cylinderEndpoint (b : Bool) : Hom K K.cylinder where
  map := cylinderEndpointMap K b
  map_d p x := by
    cases p <;> cases b <;>
      dsimp [cylinder, cylinderEndpointMap, cylinderDifferential] <;> simp
  map_augmentation x := by
    cases b <;> dsimp [cylinder, cylinderEndpointMap] <;> simp
  map_positive p x hx := by
    cases p <;> cases b <;>
      simp only [cylinder, cylinderPositive, cylinderEndpointMap, Bool.false_eq_true,
        ↓reduceIte, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        AddSubmonoid.mem_prod] <;> simp only [hx, AddSubmonoid.zero_mem, and_self]

def cylinderProjectionMap : (p : ℕ) → CylinderChain K p →+ K.Chain p
  | 0 =>
    { toFun := fun x => x.1 + x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  | p+1 =>
    { toFun := fun x => x.1 + x.2.1
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }

def cylinderProjection : Hom K.cylinder K where
  map := cylinderProjectionMap K
  map_d p x := by
    cases p <;> dsimp [cylinder, cylinderProjectionMap, cylinderDifferential] <;>
      simp only [map_add] <;> abel
  map_augmentation x := by
    dsimp [cylinder, cylinderProjectionMap]
    exact map_add _ _ _
  map_positive p x hx := by
    cases p with
    | zero => exact (K.positive 0).add_mem hx.1 hx.2
    | succ p => exact (K.positive (p+1)).add_mem hx.1 hx.2.1

@[simp] lemma cylinderProjection_endpoint (b : Bool) :
    Hom.comp (cylinderEndpoint K b) (cylinderProjection K) = Hom.id K := by
  ext p x
  cases p <;> cases b <;>
    dsimp [Hom.comp, Hom.id, cylinderEndpoint, cylinderProjection,
      cylinderEndpointMap, cylinderProjectionMap] <;> simp

end Thomason.DirectedComplex

end

end OAI
