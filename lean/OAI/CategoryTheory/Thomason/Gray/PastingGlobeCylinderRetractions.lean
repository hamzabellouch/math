import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeChains
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderAtoms
import OAI.CategoryTheory.Thomason.Gray.PastingGlobeCylinderPath

namespace OAI

section

/-! # Right cylinders preserve the actual pasted-globe chain pushouts

The explicit path-complex hom-set correspondence constructs the descended
positive chain map. The subsequent realization gluing is a separate claim;
no preservation of pushouts by realization is assumed here.
-/

namespace Thomason.Construction.DirectedComplex.RightPath

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {K L : DirectedComplex.{0}}

abbrev rawApp (f : Hom K (complex L)) : (n : ℕ) → K.group n →+ rawGroup L n
  | 0 => (zeroGroup L).subtype.comp (f.app 0)
  | n+1 => f.app (n+1)

theorem rawApp_differential (f : Hom K (complex L)) (n : ℕ) (x : K.group (n+1)) :
    rawApp f n (K.differential n x) = rawDifferential L n (rawApp f (n+1) x) := by
  cases n with
  | zero => exact congrArg Subtype.val (f.differential 0 x)
  | succ n => exact f.differential (n+1) x

def firstApp (f : Hom K (complex L)) (n : ℕ) : K.group n →+ L.group n where
  toFun x := (rawApp f n x).1
  map_zero' := congrArg Prod.fst (map_zero (rawApp f n))
  map_add' x y := congrArg Prod.fst (map_add (rawApp f n) x y)

def secondApp (f : Hom K (complex L)) (n : ℕ) : K.group n →+ L.group n where
  toFun x := (rawApp f n x).2.1
  map_zero' := congrArg (Prod.fst ∘ Prod.snd) (map_zero (rawApp f n))
  map_add' x y := congrArg (Prod.fst ∘ Prod.snd) (map_add (rawApp f n) x y)

def shiftedFrom (f : Hom K (complex L)) (n : ℕ) : K.group n →+ L.group (n+1) where
  toFun x := (rawApp f n x).2.2
  map_zero' := congrArg (Prod.snd ∘ Prod.snd) (map_zero (rawApp f n))
  map_add' x y := congrArg (Prod.snd ∘ Prod.snd) (map_add (rawApp f n) x y)

def first (f : Hom K (complex L)) : Hom K L where
  app := firstApp f
  differential n x := congrArg Prod.fst (rawApp_differential f n x)
  augmentation x := f.augmentation x
  positive n x hx := by
    have h := f.positive n hx
    cases n <;> exact h.1

def second (f : Hom K (complex L)) : Hom K L where
  app := secondApp f
  differential n x := congrArg (Prod.fst ∘ Prod.snd) (rawApp_differential f n x)
  augmentation x := by
    have h := congrArg L.augmentation (f.app 0 x).property
    change L.augmentation (L.differential 0 (shiftedFrom f 0 x)) =
      L.augmentation (secondApp f 0 x - firstApp f 0 x) at h
    rw [L.augmentation_differential, map_sub] at h
    exact (sub_eq_zero.mp h.symm).trans (f.augmentation x)
  positive n x hx := by
    have h := f.positive n hx
    cases n <;> exact h.2.1

theorem shiftedFrom_positive (f : Hom K (complex L)) (n : ℕ) {x : K.group n}
    (hx : x ∈ K.positive n) : shiftedFrom f n x ∈ L.positive (n+1) := by
  have h := f.positive n hx
  cases n <;> exact h.2.2

theorem shiftedFrom_differential_zero (f : Hom K (complex L)) (x : K.group 0) :
    L.differential 0 (shiftedFrom f 0 x) = (second f).app 0 x - (first f).app 0 x :=
  (f.app 0 x).property

theorem shiftedFrom_differential_succ (f : Hom K (complex L)) (n : ℕ)
    (x : K.group (n+1)) :
    L.differential (n+1) (shiftedFrom f (n+1) x) =
      ((-1 : ℤ)^(n+1)) • ((second f).app (n+1) x - (first f).app (n+1) x) +
        shiftedFrom f n (K.differential n x) := by
  have h := congrArg (Prod.snd ∘ Prod.snd) (rawApp_differential f n x)
  change shiftedFrom f n (K.differential n x) =
    L.differential (n+1) (shiftedFrom f (n+1) x) -
      ((-1 : ℤ)^(n+1)) • ((second f).app (n+1) x - (first f).app (n+1) x) at h
  exact (eq_sub_iff_add_eq.mp h).symm.trans (add_comm _ _)

def uncurryApp (f : Hom K (complex L)) :
    (n : ℕ) → (rightCylinder K).group n →+ L.group n
  | 0 =>
    { toFun := fun x => (first f).app 0 x.1 + (second f).app 0 x.2
      map_zero' := by simp
      map_add' := by intros; simp; abel }
  | n+1 =>
    { toFun := fun x => (first f).app (n+1) x.1 + (second f).app (n+1) x.2.1 +
        shiftedFrom f n x.2.2
      map_zero' := by simp
      map_add' := by intros; simp; abel }

/-- Uncurrying preserves positivity, augmentation, and the signed differential. -/
def uncurry (f : Hom K (complex L)) : Hom (rightCylinder K) L where
  app := uncurryApp f
  differential n x := by
    cases n with
    | zero =>
      change (first f).app 0 (K.differential 0 x.1 - x.2.2) +
        (second f).app 0 (K.differential 0 x.2.1 + x.2.2) =
        L.differential 0 ((first f).app 1 x.1 + (second f).app 1 x.2.1 + shiftedFrom f 0 x.2.2)
      rw [map_sub, map_add, map_add, map_add, (first f).differential,
        (second f).differential, shiftedFrom_differential_zero]
      abel
    | succ n =>
      change (first f).app (n+1) (K.differential (n+1) x.1 - ((-1 : ℤ)^(n+1)) • x.2.2) +
        (second f).app (n+1) (K.differential (n+1) x.2.1 + ((-1 : ℤ)^(n+1)) • x.2.2) +
        shiftedFrom f n (K.differential n x.2.2) =
        L.differential (n+1) ((first f).app (n+2) x.1 + (second f).app (n+2) x.2.1 +
          shiftedFrom f (n+1) x.2.2)
      rw [map_sub, map_add, map_zsmul, map_zsmul, map_add, map_add,
        (first f).differential, (second f).differential, shiftedFrom_differential_succ]
      rw [smul_sub]
      abel
  augmentation x := by
    change L.augmentation ((first f).app 0 x.1 + (second f).app 0 x.2) =
      K.augmentation x.1 + K.augmentation x.2
    rw [map_add, (first f).augmentation, (second f).augmentation]
  positive n x hx := by
    cases n with
    | zero => exact (L.positive 0).add_mem ((first f).positive 0 hx.1) ((second f).positive 0 hx.2)
    | succ n =>
      exact (L.positive (n+1)).add_mem
        ((L.positive (n+1)).add_mem ((first f).positive (n+1) hx.1)
          ((second f).positive (n+1) hx.2.1)) (shiftedFrom_positive f n hx.2.2)

theorem uncurry_curry (f : Hom (rightCylinder K) L) : uncurry (curry f) = f := by
  apply Hom.ext_app
  intro n x
  cases n with
  | zero => exact (apply_zero f x).symm
  | succ n =>
    cases n with
    | zero => exact (apply_succ f 0 x).symm
    | succ n => exact (apply_succ f (n+1) x).symm

theorem curry_uncurry (f : Hom K (complex L)) : curry (uncurry f) = f := by
  apply Hom.ext_app
  intro n x
  cases n with
  | zero =>
    apply Subtype.ext
    apply Prod.ext
    · change (first f).app 0 x + (second f).app 0 0 = _
      simp only [map_zero, add_zero]
      rfl
    · apply Prod.ext
      · change (first f).app 0 0 + (second f).app 0 x = _
        simp only [map_zero, zero_add]
        rfl
      · change (first f).app 1 0 + (second f).app 1 0 + shiftedFrom f 0 x = _
        simp only [map_zero, zero_add]
        rfl
  | succ n =>
    apply Prod.ext
    · change (first f).app (n+1) x + (second f).app (n+1) 0 + shiftedFrom f n 0 = _
      simp only [map_zero, add_zero]
      rfl
    · apply Prod.ext
      · change (first f).app (n+1) 0 + (second f).app (n+1) x + shiftedFrom f n 0 = _
        simp only [map_zero, zero_add, add_zero]
        rfl
      · change (first f).app (n+2) 0 + (second f).app (n+2) 0 + shiftedFrom f (n+1) x = _
        simp only [map_zero, zero_add]
        rfl

/-- The actual hom-set correspondence for the right interval chain tensor. -/
def homEquiv : Hom (rightCylinder K) L ≃ Hom K (complex L) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

theorem curry_naturality {A : DirectedComplex.{0}} (g : Hom A K)
    (f : Hom (rightCylinder K) L) :
    curry (Hom.comp (RightCylinder.map g) f) = Hom.comp g (curry f) := by
  apply Hom.ext_app
  intro n x
  cases n with
  | zero =>
    apply Subtype.ext
    apply Prod.ext
    · change f.app 0 (g.app 0 x, g.app 0 0) = f.app 0 (g.app 0 x, 0)
      rw [map_zero]
    · apply Prod.ext
      · change f.app 0 (g.app 0 0, g.app 0 x) = f.app 0 (0, g.app 0 x)
        rw [map_zero]
      · change f.app 1 (g.app 1 0, g.app 1 0, g.app 0 x) = _
        simp only [map_zero]
        rfl
  | succ n =>
    apply Prod.ext
    · change f.app (n+1) (g.app (n+1) x, g.app (n+1) 0, g.app n 0) = _
      simp only [map_zero]
      rfl
    · apply Prod.ext
      · change f.app (n+1) (g.app (n+1) 0, g.app (n+1) x, g.app n 0) = _
        simp only [map_zero]
        rfl
      · change f.app (n+2) (g.app (n+2) 0, g.app (n+2) 0, g.app (n+1) x) = _
        simp only [map_zero]
        rfl


theorem uncurry_naturality {A : DirectedComplex.{0}} (g : Hom A K)
    (f : Hom K (complex L)) :
    uncurry (Hom.comp g f) = Hom.comp (RightCylinder.map g) (uncurry f) := by
  apply (homEquiv (K := A) (L := L)).injective
  change curry (uncurry (Hom.comp g f)) = curry (Hom.comp (RightCylinder.map g) (uncurry f))
  rw [curry_uncurry, curry_naturality, curry_uncurry]

/-- The positive path-complex correspondence gives an actual chain pushout
of right cylinders, with the prescribed four maps. -/
theorem rightCylinder_isPushout {A B C P : DirectedComplex.{0}}
    {i : A ⟶ B} {j : A ⟶ C} {l : B ⟶ P} {r : C ⟶ P}
    (hP : IsPushout i j l r) :
    IsPushout (C := DirectedComplex.{0}) (RightCylinder.map i) (RightCylinder.map j)
      (RightCylinder.map l) (RightCylinder.map r) := by
  have hw : rightCylinderFunctor.map i ≫ rightCylinderFunctor.map l =
      rightCylinderFunctor.map j ≫ rightCylinderFunctor.map r := by
    simpa only [rightCylinderFunctor.map_comp] using congrArg rightCylinderFunctor.map hP.w
  let d (s : PushoutCocone (C := DirectedComplex.{0}) (RightCylinder.map i) (RightCylinder.map j)) :=
    uncurry (hP.desc (curry s.inl) (curry s.inr) (by
      change Hom.comp i (curry s.inl) = Hom.comp j (curry s.inr)
      rw [← curry_naturality, ← curry_naturality]
      exact congrArg curry s.condition))
  apply IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw d ?_ ?_ ?_)
  · intro s
    dsimp only [d]
    change Hom.comp (RightCylinder.map l) (uncurry _) = s.inl
    rw [← uncurry_naturality]
    change uncurry (l ≫ hP.desc _ _ _) = s.inl
    rw [hP.inl_desc, uncurry_curry]
  · intro s
    dsimp only [d]
    change Hom.comp (RightCylinder.map r) (uncurry _) = s.inr
    rw [← uncurry_naturality]
    change uncurry (r ≫ hP.desc _ _ _) = s.inr
    rw [hP.inr_desc, uncurry_curry]
  · intro s m hl hr
    apply (homEquiv (K := P) (L := s.pt)).injective
    change curry m = curry (d s)
    dsimp only [d]
    rw [curry_uncurry]
    apply hP.hom_ext
    · have he : Hom.comp l (curry m) = curry s.inl :=
        (curry_naturality l m).symm.trans (congrArg curry hl)
      exact he.trans (hP.inl_desc _ _ _).symm
    · have he : Hom.comp r (curry m) = curry s.inr :=
        (curry_naturality r m).symm.trans (congrArg curry hr)
      exact he.trans (hP.inr_desc _ _ _).symm

end

end Thomason.Construction.DirectedComplex.RightPath


namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe

open CategoryTheory CategoryTheory.Limits _root_.OAI.Thomason.Construction.DirectedComplex

/-- The actual positive chain presentation of the pasted-globe cylinder
is a pushout of the two globe-cylinder chain presentations. -/
theorem rightCylinder_abelianization_isPushout (n m k : ℕ) :
    IsPushout (C := DirectedComplex.{0})
      (RightCylinder.map (Abelianization.map (Globe.faceMap true k n)))
      (RightCylinder.map (Abelianization.map (Globe.faceMap false k m)))
      (RightCylinder.map (Abelianization.map (left n m k)))
      (RightCylinder.map (Abelianization.map (right n m k))) :=
  RightPath.rightCylinder_isPushout (abelianization_isPushout n m k)

end Thomason.Construction.StrictOmegaCategory.PastingGlobe

end

section

/-! # Free coordinates for the actual finite cylinder complex

The two endpoint factors and the mixed factor give a literal additive
equivalence to finitely supported functions on the formal tensor basis.
This supplies the coordinates needed by finite atom decomposition.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

private def zeroEquiv (n k : ℕ) :
    Basis n k 0 ≃ Bool × PastingGlobeBasis.Basis n k 0 where
  toFun
    | .endpoint a b => (a, b)
  invFun b := .endpoint b.1 b.2
  left_inv b := by cases b; rfl
  right_inv b := by cases b; rfl

private def succEquiv (n k p : ℕ) : Basis n k (p+1) ≃
    (Bool × PastingGlobeBasis.Basis n k (p+1)) ⊕ PastingGlobeBasis.Basis n k p where
  toFun
    | .endpoint a b => Sum.inl (a, b)
    | .mixed b => Sum.inr b
  invFun
    | Sum.inl b => .endpoint b.1 b.2
    | Sum.inr b => .mixed b
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b with
    | inl b => cases b; rfl
    | inr b => rfl

instance finiteBasis (n k p : ℕ) : Finite (Basis n k p) := by
  cases p with
  | zero => exact Finite.of_equiv _ (zeroEquiv n k).symm
  | succ p => exact Finite.of_equiv _ (succEquiv n k p).symm

instance fintypeBasis (n k p : ℕ) : Fintype (Basis n k p) := Fintype.ofFinite _

/-- Every literal coefficient is an additive map. -/
def coefficientHom {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    (Cylinder hkn).group p →+ ℤ where
  toFun := coefficient hkn b
  map_zero' := by
    cases p with
    | zero => cases b with | endpoint a b => cases a <;> rfl
    | succ p =>
      cases b with
      | endpoint a b => cases a <;> rfl
      | mixed b => rfl
  map_add' x y := by
    cases p with
    | zero => cases b with | endpoint a b => cases a <;> rfl
    | succ p =>
      cases b with
      | endpoint a b => cases a <;> rfl
      | mixed b => rfl

/-- The finitely supported coordinate function of an actual cylinder chain. -/
def toFinsupp {n k p : ℕ} (hkn : k < n) (x : (Cylinder hkn).group p) :
    Basis n k p →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun b => coefficient hkn b x)

@[simp] theorem toFinsupp_apply {n k p : ℕ} (hkn : k < n)
    (x : (Cylinder hkn).group p) (b : Basis n k p) :
    toFinsupp hkn x b = coefficient hkn b x := by simp [toFinsupp]

/-- Reassemble a chain from its finite basis coefficients. -/
def fromFinsupp {n k p : ℕ} (hkn : k < n) :
    (Basis n k p →₀ ℤ) →ₗ[ℤ] (Cylinder hkn).group p :=
  Finsupp.linearCombination ℤ (vector hkn)

@[simp] theorem fromFinsupp_single {n k p : ℕ} (hkn : k < n)
    (b : Basis n k p) (z : ℤ) :
    fromFinsupp hkn (Finsupp.single b z) = z • vector hkn b := by simp [fromFinsupp]

/-- Reassembly recovers each coefficient exactly. -/
theorem coefficient_fromFinsupp {n k p : ℕ} (hkn : k < n)
    (b : Basis n k p) (u : Basis n k p →₀ ℤ) :
    coefficient hkn b (fromFinsupp hkn u) = u b := by
  classical
  change coefficientHom hkn b (fromFinsupp hkn u) = u b
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single c z =>
    rw [fromFinsupp_single, map_zsmul]
    change z • coefficient hkn b (vector hkn c) = _
    rw [coefficient_vector]
    by_cases hbc : b = c
    · subst c
      simp
    · simp [hbc]

/-- Literal free coordinates on every degree of the actual right cylinder. -/
def coordinateEquiv {n k p : ℕ} (hkn : k < n) :
    (Cylinder hkn).group p ≃+ (Basis n k p →₀ ℤ) where
  toFun := toFinsupp hkn
  invFun := fromFinsupp hkn
  left_inv x := by
    apply coefficient_ext hkn
    intro b
    rw [coefficient_fromFinsupp, toFinsupp_apply]
  right_inv u := by
    ext b
    rw [toFinsupp_apply, coefficient_fromFinsupp]
  map_add' x y := by
    ext b
    exact (coefficientHom hkn b).map_add x y

/-- The coordinate equivalence identifies the actual positive cone. -/
theorem coordinateEquiv_positive_iff {n k p : ℕ} (hkn : k < n)
    (x : (Cylinder hkn).group p) :
    x ∈ (Cylinder hkn).positive p ↔ ∀ b, 0 ≤ coordinateEquiv hkn x b :=
  positive_iff hkn x

/-- Every degree-zero basis vector has augmentation one. -/
theorem augmentation_vector {n k : ℕ} (hkn : k < n) (b : Basis n k 0) :
    (Cylinder hkn).augmentation (vector hkn b) = 1 := by
  cases b with
  | endpoint a b =>
    change (Cylinder hkn).augmentation
      ((RightCylinder.endpoint (PastingGlobeBasis.complex n k hkn) a).app 0
        (Finsupp.single b 1)) = 1
    exact ((RightCylinder.endpoint (PastingGlobeBasis.complex n k hkn) a).augmentation
      (show (PastingGlobeBasis.complex n k hkn).group 0 from Finsupp.single b 1)).trans
        (PastingGlobeBasis.weight_single b 1)

/-- Augmentation is the sum of all degree-zero coordinates. -/
theorem augmentation_fromFinsupp {n k : ℕ} (hkn : k < n) (u : Basis n k 0 →₀ ℤ) :
    (Cylinder hkn).augmentation (fromFinsupp hkn u) =
      Finsupp.linearCombination ℤ (fun _ : Basis n k 0 => (1 : ℤ)) u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    rw [fromFinsupp_single, map_zsmul, augmentation_vector]
    simp

/-- The exact augmentation formula in free coordinates. -/
theorem augmentation_coordinate {n k : ℕ} (hkn : k < n) (x : (Cylinder hkn).group 0) :
    (Cylinder hkn).augmentation x =
      (coordinateEquiv hkn x).sum (fun _ z => z) := by
  have he := (coordinateEquiv hkn).left_inv x
  calc
    _ = (Cylinder hkn).augmentation (fromFinsupp hkn (coordinateEquiv hkn x)) :=
      congrArg (Cylinder hkn).augmentation he.symm
    _ = _ := by
      rw [augmentation_fromFinsupp, Finsupp.linearCombination_apply]
      simp


end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Ordered disjointness of the literal cylinder atoms

The signed differential height propagates down every atom table. Thus
increasingly ordered atoms have disjoint negative and positive lower rows,
which is the exact input needed for finite strict decomposition.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex
open scoped BigOperators

noncomputable section

private theorem coefficient_differential_fromFinsupp {n k p : ℕ} (hkn : k < n)
    (c : Basis n k p) (u : Basis n k (p+1) →₀ ℤ) :
    coefficient hkn c ((Cylinder hkn).differential p (fromFinsupp hkn u)) =
      Finsupp.linearCombination ℤ
        (fun b => coefficient hkn c ((Cylinder hkn).differential p (vector hkn b))) u := by
  change coefficientHom hkn c ((Cylinder hkn).differential p (fromFinsupp hkn u)) = _
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single b z =>
    rw [fromFinsupp_single, map_zsmul, map_zsmul]
    simp only [Finsupp.linearCombination_single]
    rfl

/-- Every boundary coefficient is the finite sum of its basis incidences. -/
theorem differential_coefficient_sum {n k p : ℕ} (hkn : k < n)
    (x : (Cylinder hkn).group (p+1)) (c : Basis n k p) :
    coefficient hkn c ((Cylinder hkn).differential p x) =
      ∑ b ∈ (coordinateEquiv hkn x).support,
        coordinateEquiv hkn x b *
          coefficient hkn c ((Cylinder hkn).differential p (vector hkn b)) := by
  calc
    _ = coefficient hkn c ((Cylinder hkn).differential p
        (fromFinsupp hkn (coordinateEquiv hkn x))) :=
      congrArg (fun z => coefficient hkn c ((Cylinder hkn).differential p z))
        ((coordinateEquiv hkn).left_inv x).symm
    _ = _ := by
      rw [coefficient_differential_fromFinsupp, Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, smul_eq_mul]

/-- A negative coefficient has an actual negative incidence in its support. -/
theorem negative_boundary_witness {n k p : ℕ} (hkn : k < n)
    (x : (Cylinder hkn).group (p+1)) (hx : x ∈ (Cylinder hkn).positive (p+1))
    (c : Basis n k p) (hc : coefficient hkn c ((Cylinder hkn).differential p x) < 0) :
    ∃ b ∈ (coordinateEquiv hkn x).support,
      coefficient hkn c ((Cylinder hkn).differential p (vector hkn b)) < 0 := by
  classical
  by_contra hn
  have hs : 0 ≤ ∑ b ∈ (coordinateEquiv hkn x).support,
      coordinateEquiv hkn x b *
        coefficient hkn c ((Cylinder hkn).differential p (vector hkn b)) := by
    apply Finset.sum_nonneg
    intro b hb
    apply mul_nonneg ((coordinateEquiv_positive_iff hkn x).mp hx b)
    exact le_of_not_gt (fun h => hn ⟨b, hb, h⟩)
  rw [← differential_coefficient_sum] at hs
  omega

/-- A positive coefficient has an actual positive incidence in its support. -/
theorem positive_boundary_witness {n k p : ℕ} (hkn : k < n)
    (x : (Cylinder hkn).group (p+1)) (hx : x ∈ (Cylinder hkn).positive (p+1))
    (c : Basis n k p) (hc : 0 < coefficient hkn c ((Cylinder hkn).differential p x)) :
    ∃ b ∈ (coordinateEquiv hkn x).support,
      0 < coefficient hkn c ((Cylinder hkn).differential p (vector hkn b)) := by
  classical
  by_contra hn
  have hs : (∑ b ∈ (coordinateEquiv hkn x).support,
      coordinateEquiv hkn x b *
        coefficient hkn c ((Cylinder hkn).differential p (vector hkn b))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro b hb
    apply mul_nonpos_of_nonneg_of_nonpos ((coordinateEquiv_positive_iff hkn x).mp hx b)
    exact le_of_not_gt (fun h => hn ⟨b, hb, h⟩)
  rw [← differential_coefficient_sum] at hs
  omega

/-- Weak side-height bounds, including the top degree. -/
theorem atom_side_bounds {n k p : ℕ} (hkn : k < n) (b : Basis n k p)
    (a : Bool) (q : ℕ) (hqp : q ≤ p) (c : Basis n k q)
    (hc : coefficient hkn c ((atom hkn b).table a q) ≠ 0) :
    if a then height b ≤ height c else height c ≤ height b := by
  induction hqp using Nat.decreasingInduction with
  | self =>
    have hcb : c = b := by
      rw [atom_top, coefficient_vector] at hc
      by_contra h
      simp [h] at hc
    subst c
    cases a <;> exact le_rfl
  | of_succ q hq ih =>
    have hs := atom_signed_table hkn b hq a c
    cases a with
    | false =>
      have hd : coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table false (q+1))) < 0 := by
        rw [hs] at hc
        change max 0 (-coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table false (q+1)))) ≠ 0 at hc
        omega
      obtain ⟨d, hmem, hd⟩ := negative_boundary_witness hkn _
        ((atom hkn b).positive false (q+1)) c hd
      have hdi : coefficient hkn d ((atom hkn b).table false (q+1)) ≠ 0 :=
        Finsupp.mem_support_iff.mp hmem
      exact (differential_height hkn false d c hd).le.trans (ih d hdi)
    | true =>
      have hd : 0 < coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table true (q+1))) := by
        rw [hs] at hc
        change max 0 (coefficient hkn c
          ((Cylinder hkn).differential q ((atom hkn b).table true (q+1)))) ≠ 0 at hc
        omega
      obtain ⟨d, hmem, hd⟩ := positive_boundary_witness hkn _
        ((atom hkn b).positive true (q+1)) c hd
      have hdi : coefficient hkn d ((atom hkn b).table true (q+1)) ≠ 0 :=
        Finsupp.mem_support_iff.mp hmem
      exact (ih d hdi).trans (differential_height hkn true d c hd).le

/-- Below the top degree the side-height bounds are strict. -/
theorem atom_side_height {n k p q : ℕ} (hkn : k < n) (b : Basis n k p)
    (a : Bool) (hqp : q < p) (c : Basis n k q)
    (hc : coefficient hkn c ((atom hkn b).table a q) ≠ 0) :
    if a then height b < height c else height c < height b := by
  have hs := atom_signed_table hkn b hqp a c
  cases a with
  | false =>
    have hd : coefficient hkn c
        ((Cylinder hkn).differential q ((atom hkn b).table false (q+1))) < 0 := by
      rw [hs] at hc
      change max 0 (-coefficient hkn c
        ((Cylinder hkn).differential q ((atom hkn b).table false (q+1)))) ≠ 0 at hc
      omega
    obtain ⟨d, hmem, hd⟩ := negative_boundary_witness hkn _
      ((atom hkn b).positive false (q+1)) c hd
    exact (differential_height hkn false d c hd).trans_le
      (atom_side_bounds hkn b false (q+1) hqp d (Finsupp.mem_support_iff.mp hmem))
  | true =>
    have hd : 0 < coefficient hkn c
        ((Cylinder hkn).differential q ((atom hkn b).table true (q+1))) := by
      rw [hs] at hc
      change max 0 (coefficient hkn c
        ((Cylinder hkn).differential q ((atom hkn b).table true (q+1)))) ≠ 0 at hc
      omega
    obtain ⟨d, hmem, hd⟩ := positive_boundary_witness hkn _
      ((atom hkn b).positive true (q+1)) c hd
    exact (atom_side_bounds hkn b true (q+1) hqp d (Finsupp.mem_support_iff.mp hmem)).trans_lt
      (differential_height hkn true d c hd)

/-- Increasingly ordered actual atoms have disjoint lower signed supports. -/
theorem ordered_atoms_disjoint {n k p q r : ℕ} (hkn : k < n)
    (b : Basis n k p) (c : Basis n k q) (hrp : r < p) (hrq : r < q)
    (hbc : height b ≤ height c) (e : Basis n k r) :
    coefficient hkn e ((atom hkn b).table false r) = 0 ∨
      coefficient hkn e ((atom hkn c).table true r) = 0 := by
  by_cases hb : coefficient hkn e ((atom hkn b).table false r) = 0
  · exact Or.inl hb
  · right
    by_contra hc
    have hbe := atom_side_height hkn b false hrp e hb
    have hec := atom_side_height hkn c true hrq e hc
    exact (not_lt_of_ge hbc) (hec.trans hbe)

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Generation of the actual pasted-globe right cylinder

The literal endpoint and prism atoms satisfy the ordered coefficient
interface. Thus all positive cells of this finite cylinder are strict
composites of the constructed atoms. No colimit property of realization
is used in this argument.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- The concrete ordered atom data of two equal globes pasted along a face. -/
def orderedAtomBasis {n k : ℕ} (hkn : k < n) : OrderedAtomBasis (Cylinder hkn) where
  Index := Basis n k
  coordinates _ := coordinateEquiv hkn
  positive_iff _ := coordinateEquiv_positive_iff hkn
  augmentation := augmentation_coordinate hkn
  atom _ := atom hkn
  atom_top _ b a := by
    ext c
    change coefficient hkn c ((atom hkn b).table a _) = Finsupp.single b 1 c
    rw [atom_top, coefficient_vector]
    simp [Finsupp.single_apply, eq_comm]
  atom_above _ b _ h a :=
    Cell.table_zero_of_dimensionLE (atom_dimension hkn b) h a
  height _ := height
  disjoint b c hrp hrq hbc e := ordered_atoms_disjoint hkn b c hrp hrq hbc e

/-- Endpoint atoms and mixed prism atoms composition-generate this cylinder. -/
theorem generated {n k : ℕ} (hkn : k < n) (P : Cell (Cylinder hkn) → Prop)
    (hatom : ∀ p (b : Basis n k p), P (atom hkn b))
    (hcomp : ∀ r x y hxy, P x → P y → P (Cell.comp x y r hxy)) :
    ∀ X, P X :=
  (orderedAtomBasis hkn).generated P hatom hcomp

/-- Strict maps out of the cylinder are determined by its explicit atoms. -/
theorem hom_ext {n k : ℕ} (hkn : k < n) {D : StrictOmegaCategory}
    (F G : (Cylinder hkn).realization ⟶ D)
    (he : ∀ p (b : Basis n k p), F.toFun (atom hkn b) = G.toFun (atom hkn b)) :
    F = G :=
  (orderedAtomBasis hkn).hom_ext F G he

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Joint epimorphy of the actual cylinder pieces

Every constructed endpoint or mixed atom lies in one of the two globe
cylinders. Generation therefore proves uniqueness of a strict glued map.
This result does not assert existence of such a glued map.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

/-- Each original globe gives its actual positive-table cylinder inclusion. -/
def sideMap {n k : ℕ} (hkn : k < n) (s : Bool) :
    (rightCylinder (DirectedGlobeComplex.complex n)).realization ⟶
      (Cylinder hkn).realization :=
  (RightCylinder.map (PastingGlobeBasis.inclusion hkn s)).realization

private theorem endpoint_cell_naturality {K L : DirectedComplex.{0}}
    (f : Hom K L) (a : Bool) (x : Cell K) :
    Cell.map (RightCylinder.map f) (Cell.map (RightCylinder.endpoint K a) x) =
      Cell.map (RightCylinder.endpoint L a) (Cell.map f x) := by
  apply Cell.ext
  funext b p
  exact RightCylinder.map_endpoint f a p (x.table b p)

/-- Every literal atom is in the image of a globe-cylinder inclusion. -/
theorem atom_in_side {n k p : ℕ} (hkn : k < n) (b : Basis n k p) :
    ∃ (s : Bool) (x : Cell (rightCylinder (DirectedGlobeComplex.complex n))),
      (sideMap hkn s).toFun x = atom hkn b := by
  cases b with
  | endpoint a b =>
    refine ⟨b.val.1, Cell.map (RightCylinder.endpoint _ a)
      ((DirectedGlobeComplex.topCell n).face b.val.2 p), ?_⟩
    exact endpoint_cell_naturality (PastingGlobeBasis.inclusion hkn b.val.1) a _
  | @mixed r b =>
    refine ⟨b.val.1, RightCylinder.prism
      ((DirectedGlobeComplex.topCell n).face b.val.2 r), ?_⟩
    exact RightCylinder.prism_naturality (PastingGlobeBasis.inclusion hkn b.val.1) _

/-- Agreement on both cylinder pieces forces equality on their target. -/
theorem sideMap_joint_epi {n k : ℕ} (hkn : k < n) {D : StrictOmegaCategory}
    (F G : (Cylinder hkn).realization ⟶ D)
    (he : ∀ s, sideMap hkn s ≫ F = sideMap hkn s ≫ G) : F = G := by
  apply hom_ext hkn
  intro p b
  obtain ⟨s, x, hx⟩ := atom_in_side hkn b
  have hh := congrArg (fun H => H.toFun x) (he s)
  change F.toFun ((sideMap hkn s).toFun x) =
    G.toFun ((sideMap hkn s).toFun x) at hh
  simpa only [hx] using hh

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # The explicit pasted-cylinder basis compares to the actual chain model

The comparison respects the two globe inclusions. In particular the two
pieces jointly detect strict maps out of the actual chain-model cylinder.
No existence assertion for gluing is made here.
-/

namespace Thomason.Construction.PastingGlobeCylinderBasis

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex StrictOmegaCategory

noncomputable section

private abbrev pasted (n k : ℕ) := StrictOmegaCategory.PastingGlobe.category n n k

private def piece {n k : ℕ} (s : Bool) : StrictOmegaCategory.Globe.category n ⟶ pasted n k :=
  if s then StrictOmegaCategory.PastingGlobe.right n n k
  else StrictOmegaCategory.PastingGlobe.left n n k

/-- The chain comparison respects either specified globe inclusion. -/
theorem abelianization_piece {n k : ℕ} (hkn : k < n) (s : Bool) :
    StrictOmegaCategory.Abelianization.functor.map (piece (n := n) (k := k) s) ≫
        (PastingGlobeBasis.abelianizationIso hkn).hom =
      (DirectedGlobeComplex.abelianizationIso n).hom ≫ PastingGlobeBasis.inclusion hkn s := by
  let f' : Globe.category n ⟶ PastingGlobe.category n n k := piece s
  let a : Abelianization.functor.obj (Globe.category n) ⟶
      PastingGlobeBasis.complex n k hkn :=
    (DirectedGlobeComplex.abelianizationIso n).hom ≫ PastingGlobeBasis.inclusion hkn s
  let b : Abelianization.functor.obj (PastingGlobe.category n n k) ⟶
      PastingGlobeBasis.complex n k hkn := (PastingGlobeBasis.abelianizationIso hkn).hom
  change Abelianization.functor.map f' ≫ b = a
  apply (StrictOmegaCategory.Abelianization.adjunction.homEquiv _ _).injective
  rw [StrictOmegaCategory.Abelianization.adjunction.homEquiv_naturality_left]
  change piece s ≫ (StrictOmegaCategory.Abelianization.unit _ ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting hkn)).realization) =
    (StrictOmegaCategory.Abelianization.unit _ ≫
      (Abelianization.evaluateHom (DirectedGlobeComplex.fromGlobe n)).realization) ≫
        (PastingGlobeBasis.inclusion hkn s).realization
  have hp : Abelianization.unit (pasted n k) ≫
      (Abelianization.evaluateHom (PastingGlobeBasis.fromPasting hkn)).realization =
        PastingGlobeBasis.fromPasting hkn := Abelianization.unit_evaluate _
  have hg : Abelianization.unit (Globe.category n) ≫
      (Abelianization.evaluateHom (DirectedGlobeComplex.fromGlobe n)).realization =
        DirectedGlobeComplex.fromGlobe n := Abelianization.unit_evaluate _
  rw [hp, hg]
  apply StrictOmegaCategory.Globe.hom_ext
  cases s
  · exact StrictOmegaCategory.PastingGlobe.desc_left _ _ _ _ _ _
  · exact StrictOmegaCategory.PastingGlobe.desc_right _ _ _ _ _ _

/-- Literal positive-table comparison for the full pasted-globe cylinder. -/
def modelIso {n k : ℕ} (hkn : k < n) :
    GrayChainExtension.model.obj (pasted n k) ≅ (Cylinder hkn).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso
    (PastingGlobeBasis.abelianizationIso hkn)

private def globeModelIso (n : ℕ) :
    GrayChainExtension.model.obj (StrictOmegaCategory.Globe.category n) ≅
      (rightCylinder (DirectedGlobeComplex.complex n)).realization :=
  (rightCylinderFunctor ⋙ realizationFunctor).mapIso
    (DirectedGlobeComplex.abelianizationIso n)

/-- The full-cylinder isomorphism is compatible with each piece. -/
theorem model_piece {n k : ℕ} (hkn : k < n) (s : Bool) :
    GrayChainExtension.model.map (piece (n := n) (k := k) s) ≫ (modelIso hkn).hom =
      (globeModelIso n).hom ≫ sideMap hkn s := by
  let T := rightCylinderFunctor ⋙ realizationFunctor
  exact (T.map_comp (Abelianization.functor.map (piece s))
    (PastingGlobeBasis.abelianizationIso hkn).hom).symm.trans
      ((congrArg T.map (abelianization_piece hkn s)).trans
        (T.map_comp (DirectedGlobeComplex.abelianizationIso n).hom
          (PastingGlobeBasis.inclusion hkn s)))

/-- Actual model-cylinder maps are determined by their restrictions to the
two actual globe cylinders. -/
theorem model_joint_epi {n k : ℕ} (hkn : k < n) {D : StrictOmegaCategory}
    (F G : GrayChainExtension.model.obj (pasted n k) ⟶ D)
    (hl : GrayChainExtension.model.map (StrictOmegaCategory.PastingGlobe.left n n k) ≫ F =
      GrayChainExtension.model.map (StrictOmegaCategory.PastingGlobe.left n n k) ≫ G)
    (hr : GrayChainExtension.model.map (StrictOmegaCategory.PastingGlobe.right n n k) ≫ F =
      GrayChainExtension.model.map (StrictOmegaCategory.PastingGlobe.right n n k) ≫ G) : F = G := by
  suffices he : (modelIso hkn).inv ≫ F = (modelIso hkn).inv ≫ G by
    have hh := congrArg (fun H => (modelIso hkn).hom ≫ H) he
    simpa only [Iso.hom_inv_id_assoc] using hh
  apply sideMap_joint_epi hkn
  intro s
  apply (cancel_epi (globeModelIso n).hom).mp
  have hs := model_piece hkn s
  have ht := congrArg (fun H => H ≫ (modelIso hkn).inv) hs
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at ht
  simp only [← Category.assoc] at ht ⊢
  simp only [← ht]
  cases s
  · exact hl
  · exact hr

end

end Thomason.Construction.PastingGlobeCylinderBasis

end

section

/-! # Concrete retractions of the two pasted globe pieces

Each half retracts from the pasted globes by collapsing the other half to
the shared face. The retractions agree after projection to the shared globe.
Their right-cylinder images provide exact split maps for the table-gluing
construction, without any preservation assertion for realization.
-/

namespace Thomason.Construction.StrictOmegaCategory.PastingGlobe

open CategoryTheory

noncomputable section

/-- Collapse a higher globe to the universal cell of a lower globe. -/
def collapseTo (n k : ℕ) (hkn : k ≤ n) : Globe.category n ⟶ Globe.category k :=
  Globe.lift _ Globe.Cell.top
    ((Globe.category k).dimensionLE_mono hkn (Globe.category_truncated k Globe.Cell.top))

@[simp] theorem collapseTo_top (n k : ℕ) (hkn : k ≤ n) :
    (collapseTo n k hkn).toFun Globe.Cell.top = Globe.Cell.top := rfl

/-- Retract the left half, collapsing the right half to the shared target face. -/
def retractLeft (n m k : ℕ) (hkm : k ≤ m) : category n m k ⟶ Globe.category n :=
  desc _ Globe.Cell.top ((Globe.category n).face true k Globe.Cell.top)
    (Globe.category_truncated n Globe.Cell.top)
    ((Globe.category n).dimensionLE_mono hkm
      ((Globe.category n).face_dimensionLE true k Globe.Cell.top))
    ((Globe.category n).face_face_same false true k Globe.Cell.top).symm

/-- Retract the right half, collapsing the left half to the shared source face. -/
def retractRight (n m k : ℕ) (hkn : k ≤ n) : category n m k ⟶ Globe.category m :=
  desc _ ((Globe.category m).face false k Globe.Cell.top) Globe.Cell.top
    ((Globe.category m).dimensionLE_mono hkn
      ((Globe.category m).face_dimensionLE false k Globe.Cell.top))
    (Globe.category_truncated m Globe.Cell.top)
    ((Globe.category m).face_face_same true false k Globe.Cell.top)

/-- The common projection remembers the entire shared k-globe. -/
def retractCommon (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    category n m k ⟶ Globe.category k :=
  desc _ Globe.Cell.top Globe.Cell.top
    ((Globe.category k).dimensionLE_mono hkn (Globe.category_truncated k Globe.Cell.top))
    ((Globe.category k).dimensionLE_mono hkm (Globe.category_truncated k Globe.Cell.top))
    ((Globe.category_truncated k Globe.Cell.top).2.trans
      (Globe.category_truncated k Globe.Cell.top).1.symm)

@[reassoc (attr := simp)] theorem left_retractLeft (n m k : ℕ) (hkm : k ≤ m) :
    left n m k ≫ retractLeft n m k hkm = 𝟙 _ := by
  apply Globe.hom_ext
  exact desc_left _ _ _ _ _ _

@[reassoc (attr := simp)] theorem right_retractRight (n m k : ℕ) (hkn : k ≤ n) :
    right n m k ≫ retractRight n m k hkn = 𝟙 _ := by
  apply Globe.hom_ext
  exact desc_right _ _ _ _ _ _

@[reassoc (attr := simp)] theorem right_retractLeft (n m k : ℕ) (hkm : k ≤ m) :
    right n m k ≫ retractLeft n m k hkm =
      collapseTo m k hkm ≫ Globe.faceMap true k n := by
  apply Globe.hom_ext
  exact desc_right _ _ _ _ _ _

@[reassoc (attr := simp)] theorem left_retractRight (n m k : ℕ) (hkn : k ≤ n) :
    left n m k ≫ retractRight n m k hkn =
      collapseTo n k hkn ≫ Globe.faceMap false k m := by
  apply Globe.hom_ext
  exact desc_left _ _ _ _ _ _

@[reassoc (attr := simp)] theorem left_retractCommon (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    left n m k ≫ retractCommon n m k hkn hkm = collapseTo n k hkn := by
  apply Globe.hom_ext
  exact desc_left _ _ _ _ _ _

@[reassoc (attr := simp)] theorem right_retractCommon (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    right n m k ≫ retractCommon n m k hkn hkm = collapseTo m k hkm := by
  apply Globe.hom_ext
  exact desc_right _ _ _ _ _ _

theorem collapseTo_face (n k : ℕ) (hkn : k ≤ n) (a : Bool) :
    Globe.faceMap a k n ≫ collapseTo n k hkn = 𝟙 _ := by
  apply Globe.hom_ext
  change (collapseTo n k hkn).toFun ((Globe.category n).face a k Globe.Cell.top) = Globe.Cell.top
  apply ((collapseTo n k hkn).map_face a k Globe.Cell.top).trans
  cases a
  · exact (Globe.category_truncated k Globe.Cell.top).1
  · exact (Globe.category_truncated k Globe.Cell.top).2

/-- The two retractions have exactly the same projection to their common face. -/
theorem retractLeft_common (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    retractLeft n m k hkm ≫ collapseTo n k hkn = retractCommon n m k hkn hkm := by
  apply (IsPushout.of_hasPushout (Globe.faceMap true k n) (Globe.faceMap false k m)).hom_ext
  · rw [← Category.assoc, left_retractLeft, Category.id_comp, left_retractCommon]
  · rw [← Category.assoc, right_retractLeft, Category.assoc, collapseTo_face,
      Category.comp_id, right_retractCommon]

theorem retractRight_common (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    retractRight n m k hkn ≫ collapseTo m k hkm = retractCommon n m k hkn hkm := by
  apply (IsPushout.of_hasPushout (Globe.faceMap true k n) (Globe.faceMap false k m)).hom_ext
  · rw [← Category.assoc, left_retractRight, Category.assoc, collapseTo_face,
      Category.comp_id, left_retractCommon]
  · rw [← Category.assoc, right_retractRight, Category.id_comp, right_retractCommon]

/-- Both piece-cylinder maps are split monos for the actual chain model. -/
theorem model_left_retractLeft (n m k : ℕ) (hkm : k ≤ m) :
    GrayChainExtension.model.map (left n m k) ≫
      GrayChainExtension.model.map (retractLeft n m k hkm) = 𝟙 _ := by
  rw [← Functor.map_comp, left_retractLeft, GrayChainExtension.model.map_id]

theorem model_right_retractRight (n m k : ℕ) (hkn : k ≤ n) :
    GrayChainExtension.model.map (right n m k) ≫
      GrayChainExtension.model.map (retractRight n m k hkn) = 𝟙 _ := by
  rw [← Functor.map_comp, right_retractRight, GrayChainExtension.model.map_id]

/-- The table projections of the two cylinder halves retain precisely the
same common-cylinder value. -/
theorem model_common (n m k : ℕ) (hkn : k ≤ n) (hkm : k ≤ m) :
    GrayChainExtension.model.map (retractLeft n m k hkm) ≫
      GrayChainExtension.model.map (collapseTo n k hkn) =
    GrayChainExtension.model.map (retractRight n m k hkn) ≫
      GrayChainExtension.model.map (collapseTo m k hkm) := by
  rw [← Functor.map_comp, ← Functor.map_comp, retractLeft_common, retractRight_common]

end

end Thomason.Construction.StrictOmegaCategory.PastingGlobe

end

end OAI
