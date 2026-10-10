import Mathlib

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

open Polynomial
open scoped DirectSum

namespace ReverseLogKodaira.Blowup

variable {R : Type*} [CommRing R]

 
def grade (I : Ideal R) (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | (p : R[X]) = monomial n ((p : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change (p : R[X]) + q = monomial n (((p : R[X]) + q).coeff n)
    rw [coeff_add, map_add, ← hp, ← hq]
  smul_mem' := by
    intro r p hp
    change r • (p : R[X]) = monomial n ((r • (p : R[X])).coeff n)
    rw [coeff_smul, ← smul_monomial, ← hp]

lemma mem_grade_iff (I : Ideal R) (n : ℕ) (p : reesAlgebra I) :
    p ∈ grade I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := Iff.rfl

 
def homogeneous (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) : reesAlgebra I :=
  ⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩

@[simp] lemma homogeneous_val (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    (homogeneous I n r hr : R[X]) = monomial n r := rfl

lemma homogeneous_mem (I : Ideal R) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    homogeneous I n r hr ∈ grade I n := by
  simp [mem_grade_iff]

instance gradedMonoid (I : Ideal R) : SetLike.GradedMonoid (grade I) where
  one_mem := by
    change (1 : R[X]) = monomial 0 ((1 : R[X]).coeff 0)
    simp
  mul_mem := by
    intro i j p q hp hq
    rw [mem_grade_iff] at hp hq ⊢
    change (p : R[X]) * q = monomial (i+j) (((p : R[X]) * q).coeff (i+j))
    rw [hp, hq, monomial_mul_monomial, coeff_monomial]
    simp

 
def component (I : Ideal R) (n : ℕ) (p : reesAlgebra I) : grade I n :=
  ⟨homogeneous I n ((p : R[X]).coeff n) (p.property n), homogeneous_mem ..⟩

@[simp] lemma component_val (I : Ideal R) (n : ℕ) (p : reesAlgebra I) :
    ((component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

 
def decompose (I : Ideal R) (p : reesAlgebra I) : ⨁ n, grade I n :=
  ⟨fun n => component I n p, Trunc.mk ⟨p.val.support.val, fun n => by
    by_cases h : n ∈ p.val.support
    · exact Or.inl h
    · right
      apply Subtype.ext
      apply Subtype.ext
      simp only [component_val, ZeroMemClass.coe_zero]
      rw [notMem_support_iff.mp h, map_zero]⟩⟩

@[simp] lemma decompose_apply (I : Ideal R) (p : reesAlgebra I) (n : ℕ) :
    decompose I p n = component I n p := rfl

lemma grade_coeff_eq_zero (I : Ideal R) {i j : ℕ} (hij : i ≠ j)
    (p : grade I i) : (((p : reesAlgebra I) : R[X]).coeff j) = 0 := by
  have h := p.property
  rw [mem_grade_iff] at h
  rw [h, coeff_monomial, ite_eq_right hij]

lemma coeff_recompose (I : Ideal R) (n : ℕ) (v : ⨁ i, grade I i) :
    ((DirectSum.coeAddMonoidHom (grade I) v : reesAlgebra I) : R[X]).coeff n =
      (((v n : grade I n) : reesAlgebra I) : R[X]).coeff n := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i p =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : i = n
    · subst i; rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      simpa using grade_coeff_eq_zero I h p
  | add x y hx hy =>
    change (↑(DirectSum.coeAddMonoidHom (grade I) (x + y)) : R[X]).coeff n =
      (↑((x n : reesAlgebra I) + (y n : reesAlgebra I)) : R[X]).coeff n
    simpa only [map_add, AddSubmonoid.coe_add, AddSubgroup.coe_add,
      Submodule.coe_add, Subalgebra.coe_add, coeff_add, DFinsupp.add_apply] using congrArg₂ (· + ·) hx hy

instance gradedAlgebra (I : Ideal R) : GradedAlgebra (grade I) where
  __ := gradedMonoid I
  decompose' := decompose I
  left_inv := by
    intro p
    apply Subtype.ext
    ext n
    rw [coeff_recompose, decompose_apply, component_val, coeff_monomial_same]
  right_inv := by
    intro v
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    apply Subtype.ext
    change monomial n _ = (((v n : grade I n) : reesAlgebra I) : R[X])
    rw [coeff_recompose]
    exact (v n).property.symm

 
def constants (I : Ideal R) : R →+* grade I 0 where
  toFun r := ⟨algebraMap R (reesAlgebra I) r, by
    change C r = monomial 0 ((C r).coeff 0)
    simp⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' r s := by apply Subtype.ext; exact map_mul _ _ _
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' r s := by apply Subtype.ext; exact map_add _ _ _

@[simp] lemma constants_val (I : Ideal R) (r : R) :
    ((constants I r : reesAlgebra I) : R[X]) = C r := rfl

 
def linearTerm (I : Ideal R) (t : I) : reesAlgebra I :=
  homogeneous I 1 t (by simp)

lemma linearTerm_mem (I : Ideal R) (t : I) : linearTerm I t ∈ grade I 1 :=
  homogeneous_mem ..

 
abbrev Chart (I : Ideal R) (t : I) :=
  HomogeneousLocalization.Away (grade I) (linearTerm I t)

 
def chartMap (I : Ideal R) (t : I) : R →+* Chart I t :=
  (HomogeneousLocalization.fromZeroRingHom (grade I)
    (Submonoid.powers (linearTerm I t))).comp (constants I)

 
def ratio (I : Ideal R) (t a : I) : Chart I t :=
  HomogeneousLocalization.Away.mk (grade I) (linearTerm_mem I t) 1
    (linearTerm I a) (by simpa using linearTerm_mem I a)

open AlgebraicGeometry CategoryTheory

 
def scheme (I : Ideal R) : Scheme := Proj (grade I)

 
def projection (I : Ideal R) : scheme I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grade I) ≫ Spec.map (CommRingCat.ofHom (constants I))

 
def chartι (I : Ideal R) (t : I) : Spec (CommRingCat.of (Chart I t)) ⟶ scheme I :=
  Proj.awayι (grade I) (linearTerm I t) (linearTerm_mem I t) Nat.zero_lt_one

lemma chartι_projection (I : Ideal R) (t : I) :
    chartι I t ≫ projection I = Spec.map (CommRingCat.ofHom (chartMap I t)) := by
  change Proj.awayι (grade I) (linearTerm I t) (linearTerm_mem I t) Nat.zero_lt_one ≫
    (Proj.toSpecZero (grade I) ≫ Spec.map (CommRingCat.ofHom (constants I))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

open HomogeneousLocalization

lemma chartMap_val (I : Ideal R) (t : I) (r : R) :
    (chartMap I t r).val = algebraMap (reesAlgebra I)
      (Localization.Away (linearTerm I t)) (algebraMap R (reesAlgebra I) r) := by
  rfl

lemma ratio_mul_parameter (I : Ideal R) (t a : I) :
    ratio I t a * chartMap I t t = chartMap I t a := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, chartMap_val, chartMap_val]
  simp only [ratio, Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [linearTerm, homogeneous_val, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
  change C (t : R) * monomial 1 (a : R) = C (a : R) * monomial 1 (t : R)
  rw [C_mul_monomial, C_mul_monomial, mul_comm]

 

theorem ideal_map_chart_eq (I : Ideal R) (t : I) :
    Ideal.map (chartMap I t) I = Ideal.span {chartMap I t t} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨ratio I t ⟨a, ha⟩, ?_⟩
    rw [mul_comm (chartMap I t t) (ratio I t ⟨a, ha⟩)]
    exact (ratio_mul_parameter I t ⟨a, ha⟩).symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ t.property

 

lemma positive_homogeneous_mem_span (I : Ideal R) (n : ℕ) {a : R} (ha : a ∈ I ^ (n+1)) :
    homogeneous I (n+1) a ha ∈ Ideal.span (Set.range (linearTerm I)) := by
  have h : ∀ a ∈ I * I ^ n, ∃ h' : a ∈ I ^ (n+1),
      homogeneous I (n+1) a h' ∈ Ideal.span (Set.range (linearTerm I)) := by
    intro a h
    refine Submodule.smul_induction_on h ?_ ?_
    · intro a ha b hb
      have hab : a * b ∈ I ^ (n+1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul ha hb
      refine ⟨hab, ?_⟩
      change homogeneous I (n+1) (a * b) hab ∈ _
      have heq : homogeneous I (n+1) (a * b) hab =
          linearTerm I ⟨a, ha⟩ * homogeneous I n b hb := by
        apply Subtype.ext
        simp only [homogeneous_val, Subalgebra.coe_mul, linearTerm]
        rw [monomial_mul_monomial, add_comm n 1]
      rw [heq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨⟨a,ha⟩, rfl⟩)
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨add_mem ha hb, ?_⟩
      have heq : homogeneous I (n+1) (a+b) (add_mem ha hb) =
          homogeneous I (n+1) a ha + homogeneous I (n+1) b hb := by
        apply Subtype.ext
        simp [homogeneous_val, map_add]
      rw [heq]
      exact add_mem ha' hb'
  obtain ⟨_, hmem⟩ := h a (by simpa only [pow_succ'] using ha)
  exact hmem

lemma irrelevant_le_span_linear (I : Ideal R) :
    (HomogeneousIdeal.irrelevant (grade I)).toIdeal ≤ Ideal.span (Set.range (linearTerm I)) := by
  change (HomogeneousIdeal.irrelevant (grade I)).toAddSubmonoid ≤
    (Ideal.span (Set.range (linearTerm I))).toAddSubmonoid
  rw [HomogeneousIdeal.irrelevant_eq_iSup]
  refine iSup_le fun n => iSup_le fun hn => ?_
  intro p hp
  cases n with
  | zero => simp at hn
  | succ n =>
    change p ∈ grade I (n+1) at hp
    have heq : p = homogeneous I (n+1) (p.val.coeff (n+1)) (p.property _) :=
      Subtype.ext hp
    rw [heq]
    exact positive_homogeneous_mem_span I n _

 
theorem charts_cover (I : Ideal R) :
    (⨆ t : I, Proj.basicOpen (grade I) (linearTerm I t)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (grade I) (linearTerm I) (irrelevant_le_span_linear I)

 
theorem exists_chart (I : Ideal R) (x : scheme I) :
    ∃ t : I, x ∈ Proj.basicOpen (grade I) (linearTerm I t) := by
  have hx : x ∈ (⨆ t : I, Proj.basicOpen (grade I) (linearTerm I t)) := by
    rw [charts_cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

 
lemma linearTerm_ne_zero (I : Ideal R) (t : I) (ht : (t : R) ≠ 0) :
    linearTerm I t ≠ 0 := by
  intro h
  have := congrArg (fun p : reesAlgebra I => (p : R[X]).coeff 1) h
  exact ht (by simpa [linearTerm, homogeneous] using this)

 

lemma chartMap_injective [IsDomain R] (I : Ideal R) (t : I) (ht : (t : R) ≠ 0) :
    Function.Injective (chartMap I t) := by
  intro a b hab
  have hv := congrArg HomogeneousLocalization.val hab
  rw [chartMap_val, chartMap_val] at hv
  have hinj := IsLocalization.injective (Localization.Away (linearTerm I t))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (linearTerm_ne_zero I t ht))
  have hc := congrArg (fun p : reesAlgebra I => (p : R[X]).coeff 0) (hinj hv)
  simpa using hc

 
lemma chart_isDomain [IsDomain R] (I : Ideal R) (t : I) (ht : (t : R) ≠ 0) :
    IsDomain (Chart I t) := by
  let : IsDomain (Localization.Away (linearTerm I t)) :=
    IsLocalization.Away.isDomain (Localization.Away (linearTerm I t)) (linearTerm_ne_zero I t ht)
  let v : Chart I t →+* Localization.Away (linearTerm I t) :=
    algebraMap (Chart I t) (Localization.Away (linearTerm I t))
  exact Function.Injective.isDomain v
    (HomogeneousLocalization.val_injective (𝒜 := grade I) _)

 

def exceptionalGeneratorMap (I : Ideal R) (t : I) :
    Chart I t →ₗ[Chart I t] Ideal.map (chartMap I t) I where
  toFun a := ⟨chartMap I t t * a,
    Ideal.mul_mem_right a _ (Ideal.mem_map_of_mem _ t.property)⟩
  map_add' a b := by
    apply Subtype.ext
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add,
      Submodule.coe_add]
    exact mul_add _ _ _
  map_smul' r a := by
    apply Subtype.ext
    exact mul_left_comm (chartMap I t t) r a

 

def exceptionalTrivialization [IsDomain R] (I : Ideal R) (t : I) (ht : (t : R) ≠ 0) :
    Chart I t ≃ₗ[Chart I t] Ideal.map (chartMap I t) I := by
  letI : IsDomain (Chart I t) := chart_isDomain I t ht
  have hparam : chartMap I t t ≠ 0 := by
    intro hz
    exact ht (chartMap_injective I t ht (by simpa using hz))
  apply LinearEquiv.ofBijective (exceptionalGeneratorMap I t)
  constructor
  · intro a b hab
    have hc := congrArg Subtype.val hab
    exact (IsRegular.of_ne_zero' (α := Chart I t) hparam).left hc
  · intro a
    have ha := (le_of_eq (ideal_map_chart_eq I t)) a.property
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨c, Subtype.ext hc.symm⟩

 

lemma parameter_ne_zero_of_mem (I : Ideal R) (t : I) (x : scheme I)
    (hx : x ∈ Proj.basicOpen (grade I) (linearTerm I t)) : (t : R) ≠ 0 := by
  intro ht
  have hz : linearTerm I t = 0 := by
    apply Subtype.ext
    simp [linearTerm, homogeneous_val, ht]
  rw [hz, Proj.basicOpen_zero] at hx
  exact hx

 

theorem exists_regular_principal_chart [IsDomain R] (I : Ideal R) (x : scheme I) :
    ∃ t : I, x ∈ Proj.basicOpen (grade I) (linearTerm I t) ∧
      IsRegular (chartMap I t t) ∧
      Ideal.map (chartMap I t) I = Ideal.span {chartMap I t t} := by
  obtain ⟨t, hxt⟩ := exists_chart I x
  have ht := parameter_ne_zero_of_mem I t x hxt
  let : IsDomain (Chart I t) := chart_isDomain I t ht
  have hparam : chartMap I t t ≠ 0 := by
    intro hz
    exact ht (chartMap_injective I t ht (by simpa using hz))
  refine ⟨t, hxt, ?_, ideal_map_chart_eq I t⟩
  exact IsRegular.of_ne_zero' (α := Chart I t) (k := chartMap I t t) hparam

 

theorem ideal_map_baseChange {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal R) (t : I) (f : R →+* A) (g : A →+* B) (h : Chart I t →+* B)
    (square : g.comp f = h.comp (chartMap I t)) :
    Ideal.map g (Ideal.map f I) = Ideal.span {h (chartMap I t t)} := by
  rw [Ideal.map_map, square, ← Ideal.map_map, ideal_map_chart_eq, Ideal.map_span,
    Set.image_singleton]

 

theorem parameter_dvd_image {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal R) (t : I) (f : R →+* A) (g : A →+* B) (h : Chart I t →+* B)
    (square : g.comp f = h.comp (chartMap I t))
    {a : A} (ha : a ∈ Ideal.map f I) : h (chartMap I t t) ∣ g a := by
  apply Ideal.mem_span_singleton.mp
  rw [← ideal_map_baseChange I t f g h square]
  exact Ideal.mem_map_of_mem g ha

end ReverseLogKodaira.Blowup

end
end

end OAI
