import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.Flags

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
variable {R V α β : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def gradeCoordinates (a : α → ℕ) :
    (α → R) ≃ₗ[R] ((k : ℕ) → {i // a i=k} → R) where
  toFun v k i := v i.val
  invFun w i := w (a i) ⟨i,rfl⟩
  left_inv w := rfl
  right_inv w := by
    funext k i
    rcases i with ⟨i,hi⟩
    subst k
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sumGrades (a : α → ℕ) (b : β → ℕ)
    (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R)) :
    (α → R) ≃ₗ[R] (β → R) :=
  (gradeCoordinates a).trans ((LinearEquiv.piCongrRight q).trans (gradeCoordinates b).symm)

lemma grade_sumGrades (a : α → ℕ) (b : β → ℕ)
    (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R)) (k : ℕ) (v : α → R) :
    coordinateGrade R b k (sumGrades a b q v)=q k (coordinateGrade R a k v) := by
  ext i
  rcases i with ⟨i,hi⟩
  subst k
  rfl

lemma prefix_sumGrades (a : α → ℕ) (b : β → ℕ)
    (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R)) (k : ℕ) :
    (coordinatePrefix R a k).map (sumGrades a b q).toLinearMap=coordinatePrefix R b k := by
  have hh (a : α → ℕ) (b : β → ℕ)
      (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R))
      (v : α → R) (hv : v∈coordinatePrefix R a k) :
      sumGrades a b q v∈coordinatePrefix R b k := by
    intro i hi
    have hz : coordinateGrade R a (b i) v=0 := by
      ext j
      exact hv j.val (j.property.symm ▸ hi)
    have he := congrFun (grade_sumGrades a b q (b i) v) ⟨i,rfl⟩
    rw [hz,map_zero] at he
    exact he
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact hh a b q v hv
  · intro v hv
    let w := sumGrades b a (fun k => (q k).symm) v
    have hw : w∈coordinatePrefix R a k := by
      intro i hi
      have hz : coordinateGrade R b (a i) v=0 := by
        ext j
        exact hv j.val (j.property.symm ▸ hi)
      have he := congrFun (grade_sumGrades b a (fun k => (q k).symm) (a i) v) ⟨i,rfl⟩
      rw [hz,map_zero] at he
      exact he
    refine ⟨w,hw,?_⟩
    ext i
    have he := congrFun (grade_sumGrades a b q (b i) w) ⟨i,rfl⟩
    rw [show coordinateGrade R a (b i) w=(q (b i)).symm (coordinateGrade R b (b i) v) from
      grade_sumGrades b a (fun k => (q k).symm) (b i) v,
      LinearEquiv.apply_symm_apply] at he
    exact he

lemma sumGrades_symm (a : α → ℕ) (b : β → ℕ)
    (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R)) :
    (sumGrades a b q).symm=sumGrades b a (fun k => (q k).symm) := by
  ext v i
  rfl

/-- Convert named grade maps to full seam frames by a block-diagonal correction over the coefficient
ring. -/
theorem namedFrame_holds (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] V) (f : (β → R) ≃ₗ[R] V)
    (q : (k : ℕ) → ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R))
    (hp : ∀ k,framedPrefix a e k=framedPrefix b f k)
    (hg : ∀ k v,v∈framedPrefix a e (k+1) → q k (framedGrade a e k v)=framedGrade b f k v) :
    SameFramedFlag b ((sumGrades a b q).symm.trans e) f := by
  have hp' (k : ℕ) : framedPrefix b ((sumGrades a b q).symm.trans e) k=framedPrefix a e k := by
    change (coordinatePrefix R b k).map (e.toLinearMap.comp (sumGrades a b q).symm.toLinearMap)=_
    rw [Submodule.map_comp,sumGrades_symm,prefix_sumGrades]
    rfl
  refine ⟨fun k => (hp' k).trans (hp k),?_⟩
  intro k v hv
  rw [hp'] at hv
  change coordinateGrade R b k (sumGrades a b q (e.symm v))=framedGrade b f k v
  rw [grade_sumGrades]
  exact hg k v hv
end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
variable {R : Type*} [CommRing R] {α β : Type*}

def sectionGrade (a : α → ℕ) (k : ℕ) :
    ({i // a i=k} → R) →ₗ[R] (α → R) where
  toFun v i := if h : a i=k then v ⟨i,h⟩ else 0
  map_add' v w := by ext i; by_cases h : a i=k <;> simp [h]
  map_smul' c v := by ext i; by_cases h : a i=k <;> simp [h]

/-- The induced map on a named graded quotient in the original coordinates. -/
def gradeMap (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] (β → R)) (k : ℕ) :
    ({i // a i=k} → R) →ₗ[R] ({i // b i=k} → R) :=
  (coordinateGrade R b k).comp (e.toLinearMap.comp (sectionGrade a k))

end IntegralCharacterVarieties.NamedBandGrades
end

noncomputable section
namespace IntegralCharacterVarieties.NamedBandGrades
open scoped Classical
variable {R : Type*} [CommRing R] {α β : Type*}

@[simp] lemma grade_section (a : α → ℕ) (k : ℕ) (v : {i // a i=k} → R) :
    coordinateGrade R a k (sectionGrade a k v)=v := by
  ext i
  simp [coordinateGrade,sectionGrade,i.property]

lemma section_prefix (a : α → ℕ) (k : ℕ) (v : {i // a i=k} → R) :
    sectionGrade a k v ∈ coordinatePrefix R a (k+1) := by
  intro i hi
  have hn : a i≠k := by omega
  simp [sectionGrade,hn]

lemma grade_prefix_zero (a : α → ℕ) (k : ℕ) (v : α → R)
    (hv : v∈coordinatePrefix R a k) : coordinateGrade R a k v=0 := by
  ext i
  exact hv i.val (le_of_eq i.property.symm)

lemma subtract_section_prefix (a : α → ℕ) (k : ℕ) (v : α → R)
    (hv : v∈coordinatePrefix R a (k+1)) :
    v-sectionGrade a k (coordinateGrade R a k v) ∈ coordinatePrefix R a k := by
  intro i hi
  by_cases he : a i=k
  · simp [sectionGrade,coordinateGrade,he]
  · have hg : k+1≤a i := by omega
    simp [sectionGrade,coordinateGrade,he,hv i hg]

lemma filtered_apply (a : α → ℕ) (b : β → ℕ) (e : (α → R) ≃ₗ[R] (β → R))
    (h : ∀ k,(coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R b k)
    (k : ℕ) {v : α → R} (hv : v∈coordinatePrefix R a k) :
    e v∈coordinatePrefix R b k := by
  rw [←h k]
  exact ⟨v,hv,rfl⟩

lemma filtered_symm (a : α → ℕ) (b : β → ℕ) (e : (α → R) ≃ₗ[R] (β → R))
    (h : ∀ k,(coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R b k) :
    ∀ k,(coordinatePrefix R b k).map e.symm.toLinearMap=coordinatePrefix R a k := by
  intro k
  rw [←h k,←Submodule.map_comp]
  simp

lemma gradeMap_naturality (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] (β → R))
    (h : ∀ k,(coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R b k)
    (k : ℕ) (v : α → R) (hv : v∈coordinatePrefix R a (k+1)) :
    gradeMap a b e k (coordinateGrade R a k v)=coordinateGrade R b k (e v) := by
  have hh := grade_prefix_zero b k (e (v-sectionGrade a k (coordinateGrade R a k v)))
    (filtered_apply a b e h k (subtract_section_prefix a k v hv))
  rw [map_sub,map_sub,sub_eq_zero] at hh
  exact hh.symm

lemma gradeMap_left_inv (a : α → ℕ) (b : β → ℕ)
    (e : (α → R) ≃ₗ[R] (β → R))
    (h : ∀ k,(coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R b k)
    (k : ℕ) (v : {i // a i=k} → R) :
    gradeMap b a e.symm k (gradeMap a b e k v)=v := by
  have hn := gradeMap_naturality b a e.symm (filtered_symm a b e h) k
    (e (sectionGrade a k v)) (filtered_apply a b e h _ (section_prefix a k v))
  change gradeMap b a e.symm k (coordinateGrade R b k (e (sectionGrade a k v)))=v
  rw [hn,LinearEquiv.symm_apply_apply,grade_section]

/-- Preservation of split prefixes makes the named row and column refinement maps invertible over
the coefficient ring. -/
def gradeEquiv (a : α → ℕ) (b : β → ℕ) (e : (α → R) ≃ₗ[R] (β → R))
    (h : ∀ k,(coordinatePrefix R a k).map e.toLinearMap=coordinatePrefix R b k)
    (k : ℕ) : ({i // a i=k} → R) ≃ₗ[R] ({i // b i=k} → R) :=
  { gradeMap a b e k with
    invFun := gradeMap b a e.symm k
    left_inv := gradeMap_left_inv a b e h k
    right_inv := gradeMap_left_inv b a e.symm (filtered_symm a b e h) k }

end IntegralCharacterVarieties.NamedBandGrades
end

end OAI
