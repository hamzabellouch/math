import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PairTail01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
open RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n) {σ : Type*}

def IsPolynomialMap (f : (σ → ℝ) → G) : Prop :=
  ∀ i, RationalPolynomialMap.IsPolynomial (fun x => c.coord (f x) i)

lemma polynomialMap_const {g : G} (hg : IsRational c g) :
    IsPolynomialMap c (fun _ : σ → ℝ => g) := by
  intro i
  obtain ⟨q,hq⟩ := hg i
  simpa only [← hq] using RationalPolynomialMap.const (σ:=σ) q

lemma polynomialMap_one : IsPolynomialMap c (fun _ : σ → ℝ => (1:G)) :=
  polynomialMap_const c (rational_one c)

lemma polynomialMap_mul {f g : (σ → ℝ) → G} (hf : IsPolynomialMap c f)
    (hg : IsPolynomialMap c g) : IsPolynomialMap c (fun x => f x*g x) := by
  intro i
  have hc : IsPolynomial (fun x => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j : Fin i.val => c.coord (f x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val => c.coord (g x) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i)) := by
    apply RationalPolynomialMap.eval
    intro j
    cases j with
    | inl j => exact hf _
    | inr j => exact hg _
  simpa only [c.mul_coord] using RationalPolynomialMap.add (RationalPolynomialMap.add (hf i) (hg i)) hc

lemma polynomialMap_basisFlow (i : Fin n) {f : (σ → ℝ) → ℝ} (hf : IsPolynomial f) :
    IsPolynomialMap c (fun x => basisFlow c i (f x)) := by
  intro j
  obtain ⟨p,hp⟩ := powerPolynomial_rational c (g := basisElement c i) (by
    intro k
    classical
    refine ⟨if k=i then 1 else 0,?_⟩
    simp only [basisElement,Homeomorph.apply_symm_apply,Pi.single_apply]
    split_ifs <;> simp) j
  change IsPolynomial (fun x => c.coord (realPower c (basisElement c i) (f x)) j)
  simpa only [realPower_coord,hp,Polynomial.eval_map] using polynomial_eval p hf

lemma polynomialMap_peel {f : (σ → ℝ) → G} (hf : IsPolynomialMap c f) (k : ℕ) :
    IsPolynomialMap c (fun x => peel c (f x) k) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    simp only [peel]
    split_ifs with hk
    · exact polynomialMap_mul c
        (polynomialMap_basisFlow c ⟨k,hk⟩ (RationalPolynomialMap.neg (ih _))) ih
    · exact ih

lemma polynomial_expCoordinates {f : (σ → ℝ) → G} (hf : IsPolynomialMap c f) (i : Fin n) :
    IsPolynomial (fun x => expCoordinates c (f x) i) := polynomialMap_peel c hf i.val i

lemma polynomialMap_expProduct {f : (σ → ℝ) → (Fin n → ℝ)}
    (hf : ∀ i, IsPolynomial (fun x => f x i)) : IsPolynomialMap c (fun x => expProduct c (f x)) := by
  change IsPolynomialMap c (fun x => (List.ofFn (fun i => basisFlow c i (f x i))).prod)
  simp only [List.ofFn_eq_map]
  generalize List.finRange n = l
  induction l with
  | nil => exact polynomialMap_one c
  | cons i l ih =>
    simp only [List.map_cons,List.prod_cons]
    exact polynomialMap_mul c (polynomialMap_basisFlow c i (hf i)) ih

end RationalLattice
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevCharacters
open RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)

omit [IsTopologicalGroup G] in
@[simp] lemma coord_axis (i : Fin n) (t : ℝ) : c.coord (axis c i t) = Pi.single i t :=
  c.coord.apply_symm_apply _

omit [IsTopologicalGroup G] in
@[simp] lemma axis_zero (i : Fin n) : axis c i 0 = 1 := by
  apply c.coord.injective
  ext j
  simp [c.one_coord]

omit [IsTopologicalGroup G] in
lemma axis_continuous (i : Fin n) : Continuous (axis c i) := by
  apply c.coord.symm.continuous.comp
  exact continuous_pi (fun j => by
    by_cases h : j = i
    · subst j
      change Continuous (fun t : ℝ => (Pi.single i t : Fin n → ℝ) i)
      simp only [Pi.single_eq_same]
      exact continuous_id
    · simpa [Pi.single_apply,h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))))

 

variable (hsk : SecondKind c) (χ : G →* Multiplicative ℝ)
include hsk

def axisCharacter (i : Fin n) : ℝ →+ ℝ where
  toFun t := Multiplicative.toAdd (χ (axis c i t))
  map_zero' := by simp
  map_add' s t := by
    change Multiplicative.toAdd (χ (axis c i (s+t))) = _
    rw [hsk.axis_add, map_mul]
    rfl

omit [IsTopologicalGroup G] in
lemma axisCharacter_continuous (hχ : Continuous χ) (i : Fin n) :
    Continuous (axisCharacter c hsk χ i) := hχ.comp (axis_continuous c i)

omit [IsTopologicalGroup G] in
lemma character_axis (hχ : Continuous χ) (i : Fin n) (t : ℝ) :
    Multiplicative.toAdd (χ (axis c i t)) = t * Multiplicative.toAdd (χ (axis c i 1)) := by
  change axisCharacter c hsk χ i t = t * axisCharacter c hsk χ i 1
  have h := map_real_smul (axisCharacter c hsk χ i) (axisCharacter_continuous c hsk χ hχ i) t 1
  simpa using h

 

omit [IsTopologicalGroup G] in
theorem character_coordinates (hχ : Continuous χ) (g : G) :
    Multiplicative.toAdd (χ g) =
      ∑ i, c.coord g i * Multiplicative.toAdd (χ (axis c i 1)) := by
  conv_lhs => rw [hsk.ordered g]
  rw [map_list_prod, List.map_ofFn]
  change Multiplicative.toAdd ((List.ofFn fun i => χ (axis c i (c.coord g i))).prod) = _
  simp only [toAdd_list_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  exact character_axis c hsk χ hχ i _

variable (Γ : Subgroup G)
variable (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)

omit hsk [IsTopologicalGroup G] in
include hΓ in
lemma axis_one_mem (i : Fin n) : axis c i 1 ∈ Γ := by
  classical
  apply (hΓ _).mpr
  intro j
  by_cases h : j = i
  · subst j
    exact ⟨1,by simp⟩
  · exact ⟨0,by simp [h]⟩

include hΓ in
 
omit [IsTopologicalGroup G] in
theorem integer_character_coordinates (hχ : Continuous χ)
    (hz : ∀ g ∈ Γ, ∃ z : ℤ, Multiplicative.toAdd (χ g) = z) :
    ∃ k : Fin n → ℤ, ∀ g : G, Multiplicative.toAdd (χ g) = ∑ i, c.coord g i * (k i : ℝ) := by
  choose k hk using (fun i => hz _ (axis_one_mem c Γ hΓ i))
  refine ⟨k,fun g => ?_⟩
  rw [character_coordinates c hsk χ hχ g]
  simp_rw [hk]

 
def coordinateForm (a : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i * a i
  map_add' x y := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum,mul_assoc]

omit [IsTopologicalGroup G] in
lemma kernel_eq_image (hχ : Continuous χ) :
    (χ.ker : Set G) = c.coord.symm ''
      ((coordinateForm (fun i => Multiplicative.toAdd (χ (axis c i 1)))).ker : Set (Fin n → ℝ)) := by
  ext g
  constructor
  · intro hg
    refine ⟨c.coord g,?_,c.coord.symm_apply_apply g⟩
    change (∑ i, c.coord g i * Multiplicative.toAdd (χ (axis c i 1))) = 0
    rw [← character_coordinates c hsk χ hχ g]
    change χ g = 1 at hg
    rw [hg]
    rfl
  · rintro ⟨x,hx,rfl⟩
    change χ (c.coord.symm x) = 1
    apply Multiplicative.toAdd.injective
    rw [character_coordinates c hsk χ hχ]
    simpa [coordinateForm] using hx

 

omit [IsTopologicalGroup G] in
theorem kernel_connected (hχ : Continuous χ) : IsConnected (χ.ker : Set G) := by
  rw [kernel_eq_image c hsk χ hχ]
  exact ((coordinateForm (fun i => Multiplicative.toAdd (χ (axis c i 1)))).ker.convex.isConnected
    ⟨0,by simp⟩).image _ c.coord.symm.continuous.continuousOn

end MalcevCharacters
end
end
 

 
section
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
namespace RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}
variable (c : RealCoordinates G n)

def prefixProduct (x : Fin n → ℝ) (k : ℕ) : G :=
  ((List.ofFn (fun i => basisFlow c i (x i))).take k).prod

lemma prefix_mul_tail (x : Fin n → ℝ) (k : ℕ) :
    prefixProduct c x k * tailProduct c x k = expProduct c x :=
  List.prod_take_mul_prod_drop _ _

lemma expProduct_coord (x : Fin n → ℝ) (i : Fin n) :
    c.coord (expProduct c x) i = c.coord (prefixProduct c x i.val) i + x i := by
  rw [← prefix_mul_tail c x i.val]
  rw [coord_mul_of_right_zero c _ _ i (fun j hj =>
    tailProduct_lower c x i.val (Nat.le_of_lt i.isLt) j hj),tailProduct_coord]

lemma prefixProduct_eq (x y : Fin n → ℝ) (k : ℕ)
    (h : ∀ i : Fin n, i.val < k → x i = y i) : prefixProduct c x k = prefixProduct c y k := by
  apply congrArg List.prod
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn]
  · intro i h1 h2
    simp only [List.getElem_take,List.getElem_ofFn]
    congr 1
    apply h
    simp only [List.length_take,List.length_ofFn] at h1
    exact lt_of_lt_of_le h1 (min_le_left _ _)

lemma expProduct_coord_sub (x y : Fin n → ℝ) (i : Fin n)
    (h : ∀ j : Fin n, j < i → x j = y j) :
    c.coord (expProduct c x) i - c.coord (expProduct c y) i = x i-y i := by
  rw [expProduct_coord,expProduct_coord,prefixProduct_eq c x y i.val h]
  ring

lemma expProduct_coord_eq (x y : Fin n → ℝ) (i : Fin n)
    (h : ∀ j : Fin n, j ≤ i → x j = y j) :
    c.coord (expProduct c x) i = c.coord (expProduct c y) i := by
  have he := expProduct_coord_sub c x y i (fun j hj => h j (le_of_lt hj))
  rw [h i le_rfl,sub_self] at he
  linarith

lemma expCoordinates_prefix_eq (g h : G) (i : Fin n)
    (he : ∀ j : Fin n, j ≤ i → c.coord g j = c.coord h j) :
    expCoordinates c g i = expCoordinates c h i := by
  have aux : ∀ k : ℕ, ∀ hk : k<n,
      (∀ j : Fin n, j.val ≤ k → c.coord g j = c.coord h j) →
        expCoordinates c g ⟨k,hk⟩ = expCoordinates c h ⟨k,hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk he
      have hl : ∀ j : Fin n, j < (⟨k,hk⟩:Fin n) → expCoordinates c g j = expCoordinates c h j := by
        intro j hj
        apply ih j.val hj j.isLt
        intro a ha
        exact he a (by change j.val < k at hj; omega)
      have hs := expProduct_coord_sub c (expCoordinates c g) (expCoordinates c h) ⟨k,hk⟩ hl
      rw [expProduct_expCoordinates,expProduct_expCoordinates,he _ le_rfl,sub_self] at hs
      linarith
  exact aux i.val i.isLt he

lemma expCoordinates_coord_sub (g h : G) (i : Fin n)
    (he : ∀ j : Fin n, j < i → c.coord g j = c.coord h j) :
    expCoordinates c g i - expCoordinates c h i = c.coord g i - c.coord h i := by
  have hl : ∀ j : Fin n, j < i → expCoordinates c g j = expCoordinates c h j := by
    intro j hj
    exact expCoordinates_prefix_eq c g h j (fun a ha => he a (lt_of_le_of_lt ha hj))
  have hs := expProduct_coord_sub c (expCoordinates c g) (expCoordinates c h) i hl
  rw [expProduct_expCoordinates,expProduct_expCoordinates] at hs
  exact hs.symm

def lowerExtend (i : Fin n) (x : Fin i.val → ℝ) (j : Fin n) : ℝ :=
  if h : j.val< i.val then x ⟨j.val,h⟩ else 0

lemma expCoordinates_mul_difference (x y : Fin n → ℝ) (i : Fin n) :
    expCoordinates c (expProduct c x * expProduct c y) i = x i + y i +
      expCoordinates c (expProduct c (lowerExtend i (fun j => x ⟨j.val,lt_trans j.isLt i.isLt⟩)) *
        expProduct c (lowerExtend i (fun j => y ⟨j.val,lt_trans j.isLt i.isLt⟩))) i := by
  let x0 := lowerExtend i (fun j => x ⟨j.val,lt_trans j.isLt i.isLt⟩)
  let y0 := lowerExtend i (fun j => y ⟨j.val,lt_trans j.isLt i.isLt⟩)
  have hx : ∀ j : Fin n, j< i → x j = x0 j := by intro j hj; simp [x0,lowerExtend,hj]
  have hy : ∀ j : Fin n, j< i → y j = y0 j := by intro j hj; simp [y0,lowerExtend,hj]
  have cx : ∀ j : Fin n, j< i → c.coord (expProduct c x) j = c.coord (expProduct c x0) j := by
    intro j hj
    exact expProduct_coord_eq c x x0 j (fun a ha => hx a (lt_of_le_of_lt ha hj))
  have cy : ∀ j : Fin n, j< i → c.coord (expProduct c y) j = c.coord (expProduct c y0) j := by
    intro j hj
    exact expProduct_coord_eq c y y0 j (fun a ha => hy a (lt_of_le_of_lt ha hj))
  have cm : ∀ j : Fin n, j< i →
      c.coord (expProduct c x * expProduct c y) j = c.coord (expProduct c x0 * expProduct c y0) j := by
    intro j hj
    rw [c.mul_coord,c.mul_coord,cx j hj,cy j hj]
    congr 2
    funext a
    cases a with
    | inl a => exact cx _ (lt_trans a.isLt hj)
    | inr a => exact cy _ (lt_trans a.isLt hj)
  have hcorr : MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j : Fin i.val => c.coord (expProduct c x) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val => c.coord (expProduct c y) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
      (Sum.elim (fun j : Fin i.val => c.coord (expProduct c x0) ⟨j.val,lt_trans j.isLt i.isLt⟩)
        (fun j : Fin i.val => c.coord (expProduct c y0) ⟨j.val,lt_trans j.isLt i.isLt⟩)) (c.correction i) := by
    congr 1
    funext a
    cases a with
    | inl a => exact cx _ a.isLt
    | inr a => exact cy _ a.isLt
  have hs := expCoordinates_coord_sub c _ _ i cm
  rw [c.mul_coord,c.mul_coord,hcorr] at hs
  have hdx := expProduct_coord_sub c x x0 i hx
  have hdy := expProduct_coord_sub c y y0 i hy
  have hx0 : x0 i = 0 := by simp [x0,lowerExtend]
  have hy0 : y0 i = 0 := by simp [y0,lowerExtend]
  rw [hx0] at hdx
  rw [hy0] at hdy
  change expCoordinates c (expProduct c x * expProduct c y) i = x i+y i+
    expCoordinates c (expProduct c x0 * expProduct c y0) i
  linarith

lemma exists_second_correction (i : Fin n) :
    ∃ P : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ,
      ∀ v : (Fin i.val ⊕ Fin i.val) → ℝ,
        expCoordinates c
          (expProduct c (lowerExtend i (fun j => v (Sum.inl j))) *
            expProduct c (lowerExtend i (fun j => v (Sum.inr j)))) i =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) v P := by
  apply polynomial_expCoordinates c
  apply polynomialMap_mul c <;> apply polynomialMap_expProduct c <;> intro j
  all_goals
    unfold lowerExtend
    split_ifs with hj
    · exact RationalPolynomialMap.coordinate _
    · exact RationalPolynomialMap.zero

lemma expProduct_zero : expProduct c 0 = 1 := by
  change (List.ofFn (fun i => basisFlow c i 0)).prod = 1
  apply List.prod_eq_one
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact basisFlow_zero c i

lemma expCoordinates_one : expCoordinates c 1 = 0 := by
  rw [← expProduct_zero c,expCoordinates_expProduct]

def secondCorrection (i : Fin n) : MvPolynomial (Fin i.val ⊕ Fin i.val) ℚ :=
  (exists_second_correction c i).choose

lemma second_mul_coord (g h : G) (i : Fin n) :
    expCoordinates c (g*h) i = expCoordinates c g i + expCoordinates c h i +
      MvPolynomial.eval₂ (algebraMap ℚ ℝ)
        (Sum.elim (fun j => expCoordinates c g ⟨j.val,lt_trans j.isLt i.isLt⟩)
          (fun j => expCoordinates c h ⟨j.val,lt_trans j.isLt i.isLt⟩)) (secondCorrection c i) := by
  have hm := expCoordinates_mul_difference c (expCoordinates c g) (expCoordinates c h) i
  rw [expProduct_expCoordinates,expProduct_expCoordinates] at hm
  rw [hm]
  congr 1
  exact (exists_second_correction c i).choose_spec
    (Sum.elim (fun j => expCoordinates c g ⟨j.val,lt_trans j.isLt i.isLt⟩)
      (fun j => expCoordinates c h ⟨j.val,lt_trans j.isLt i.isLt⟩))

 
def secondCoordinates [IsTopologicalGroup G] : RealCoordinates G n where
  coord := secondKindHomeomorph c
  one_coord i := congrFun (expCoordinates_one c) i
  correction := secondCorrection c
  mul_coord := second_mul_coord c

lemma expProduct_single (i : Fin n) (t : ℝ) : expProduct c (Pi.single i t) = basisFlow c i t := by
  classical
  change (List.ofFn (fun j => basisFlow c j ((Pi.single i t : Fin n → ℝ) j))).prod = _
  rw [List.ofFn_eq_map,List.prod_map_eq_pow_single i]
  · simp
  · intro j hji hj
    simp [hji]

lemma second_axis [IsTopologicalGroup G] (i : Fin n) (t : ℝ) :
    MalcevCharacters.axis (secondCoordinates c) i t = basisFlow c i t := expProduct_single c i t

 

theorem secondCoordinates_secondKind [IsTopologicalGroup G] :
    MalcevCharacters.SecondKind (secondCoordinates c) where
  axis_add i s t := by simp only [second_axis]; exact basisFlow_add c i s t
  ordered g := by
    simp only [second_axis]
    exact (expProduct_expCoordinates c g).symm

lemma coordinates_prefix_zeros_iff (g : G) (k : ℕ) :
    (∀ i : Fin n, i.val < k → expCoordinates c g i = 0) ↔
      (∀ i : Fin n, i.val < k → c.coord g i = 0) := by
  constructor
  · intro hg i hi
    have he := expProduct_coord_eq c (expCoordinates c g) 0 i (fun j hj => hg j (by
      change j.val ≤ i.val at hj; omega))
    rw [expProduct_expCoordinates,expProduct_zero,c.one_coord] at he
    exact he
  · intro hg i hi
    have he := expCoordinates_prefix_eq c g 1 i (by
      intro j hj
      rw [c.one_coord]
      apply hg
      change j.val ≤ i.val at hj
      omega)
    rw [expCoordinates_one] at he
    exact he

 

theorem secondCoordinates_adapted [IsTopologicalGroup G] (H : Subgroup G) (k : ℕ)
    (hH : ∀ g : G, g ∈ H ↔ ∀ i : Fin n, i.val < k → c.coord g i = 0) (g : G) :
    g ∈ H ↔ ∀ i : Fin n, i.val < k → (secondCoordinates c).coord g i = 0 := by
  exact (hH g).trans (coordinates_prefix_zeros_iff c g k).symm

end RationalLattice

end
end
end
end
end

end OAI
