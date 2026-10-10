import OAI.RepresentationTheory.KazhdanLusztig.Bruhat

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace Hecke

variable {C : Type*} [CommRing C]

/-- The standard free module of the actual Coxeter group. -/
abbrev Space (W C : Type*) [Zero C] := W →₀ C

noncomputable def basis (w : W) : Space W C := Finsupp.single w 1

include klPreservedInstance1 in
theorem end_ext {f g : Module.End C (Space W C)}
    (h : ∀ w, f (basis w) = g (basis w)) : f = g := by
  have _ := klPreservedInstance1
  apply Finsupp.lhom_ext
  intro w c
  have hc : Finsupp.single w c = c • basis w := by
    simp [basis, Finsupp.smul_single]
  rw [hc, map_smul, map_smul, h]

/-- Normalized Hecke multiplication: H_s² = 1 + a H_s. -/
noncomputable def left (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w => basis (cs.simple i * w) +
    if cs.length (cs.simple i * w) < cs.length w then a • basis w else 0)

noncomputable def right (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w => basis (w * cs.simple i) +
    if cs.length (w * cs.simple i) < cs.length w then a • basis w else 0)

@[simp] theorem left_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    left cs a i (basis w) = basis (cs.simple i * w) +
      if cs.length (cs.simple i * w) < cs.length w then a • basis w else 0 := by
  simp [left, basis, Finsupp.linearCombination_single]

@[simp] theorem right_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    right cs a i (basis w) = basis (w * cs.simple i) +
      if cs.length (w * cs.simple i) < cs.length w then a • basis w else 0 := by
  simp [right, basis, Finsupp.linearCombination_single]

theorem left_right_commute (cs : CoxeterSystem M W) (a : C) (i j : B) :
    Commute (left cs a i) (right cs a j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis, map_add]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    rw [heq', heq'']
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [map_smul, right_basis, left_basis,
        heq, ite_eq_left h']
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      simp only [ite_eq_right h', map_zero, add_zero, heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    simp only [hl, hr]
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, ite_false, map_zero, add_zero, map_smul,
        left_basis, right_basis, smul_add, smul_smul, mul_assoc] ;
      abel

theorem left_quadratic (cs : CoxeterSystem M W) (a : C) (i : B) :
    left cs a i * left cs a i = 1 + a • left cs a i := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, map_add,
    cs.simple_mul_simple_cancel_left, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rcases cs.length_simple_mul w i with h | h
  · have hasc : ¬cs.length (cs.simple i * w) < cs.length w := by omega
    have hdesc : cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc]
  · have hdesc : cs.length (cs.simple i * w) < cs.length w := by omega
    have hasc : ¬cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc, smul_add, smul_smul]

/-- Inverse normalized Hecke generator, available without inverting any scalar. -/
noncomputable def leftInv (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) := left cs a i - a • 1

theorem left_mul_leftInv (cs : CoxeterSystem M W) (a : C) (i : B) :
    left cs a i * leftInv cs a i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs a i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  rw [h]
  abel

theorem leftInv_mul_left (cs : CoxeterSystem M W) (a : C) (i : B) :
    leftInv cs a i * left cs a i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs a i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [h]
  abel

noncomputable def leftWord (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (left cs a)).prod

@[simp] theorem leftWord_nil (cs : CoxeterSystem M W) (a : C) :
    leftWord cs a [] = 1 := rfl

@[simp] theorem leftWord_cons (cs : CoxeterSystem M W) (a : C) (i : B) (ω : List B) :
    leftWord cs a (i :: ω) = left cs a i * leftWord cs a ω := rfl

/-- Acting on the identity along a reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs a ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

noncomputable def rightWord (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (right cs a)).prod

@[simp] theorem rightWord_nil (cs : CoxeterSystem M W) (a : C) :
    rightWord cs a [] = 1 := rfl

@[simp] theorem rightWord_cons (cs : CoxeterSystem M W) (a : C) (i : B) (ω : List B) :
    rightWord cs a (i :: ω) = right cs a i * rightWord cs a ω := rfl

theorem rightWord_one (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs a ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) =
        cs.length (cs.simple i * cs.wordProd ω) := by
      rw [← cs.length_inv (cs.simple i * cs.wordProd ω)]
      simp [mul_inv_rev]
    have hasc : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω)⁻¹ := by
      rw [hlen, cs.length_inv]
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hasc' : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω) := by simpa using hasc
    simp [Module.End.mul_apply, ih hω', hasc', cs.wordProd_cons, mul_inv_rev]

theorem commute_rightWord (cs : CoxeterSystem M W) (a : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs a i)) (ω : List B) :
    Commute f (rightWord cs a ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (a : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs a i))
    (hg : ∀ i, Commute g (right cs a i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs a ω (basis 1) = basis w := by
    rw [rightWord_one cs a hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs a hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (a : C) (ω : List B) (i : B) :
    Commute (leftWord cs a ω) (right cs a i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs a j i


theorem leftWord_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs a ω = leftWord cs a η := by
  apply commuting_ext cs a (leftWord_commute_right cs a ω)
    (leftWord_commute_right cs a η)
  rw [leftWord_one cs a hω, leftWord_one cs a hη, heq]

noncomputable def unit (cs : CoxeterSystem M W) (a : C) (i : B) :
    (Module.End C (Space W C))ˣ where
  val := left cs a i
  inv := leftInv cs a i
  val_inv := left_mul_leftInv cs a i
  inv_val := leftInv_mul_left cs a i

noncomputable def wordUnit (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    (Module.End C (Space W C))ˣ := (ω.map (unit cs a)).prod

@[simp] theorem wordUnit_val (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    (wordUnit cs a ω).val = leftWord cs a ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change (unit cs a i).val * (wordUnit cs a ω).val = left cs a i * leftWord cs a ω
    rw [ih]
    rfl

theorem wordUnit_independent (cs : CoxeterSystem M W) (a : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs a ω = wordUnit cs a η := by
  apply Units.ext
  simpa using leftWord_independent cs a hω hη heq

/-- The genuine normalized standard-basis action, a unit in the regular
endomorphism algebra. No presentation relations are assumed. -/
noncomputable def standardUnit (cs : CoxeterSystem M W) (a : C) (w : W) :
    (Module.End C (Space W C))ˣ :=
  wordUnit cs a (Classical.choose (cs.exists_isReduced w))

theorem standardUnit_word (cs : CoxeterSystem M W) (a : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs a (cs.wordProd ω) = wordUnit cs a ω := by
  apply wordUnit_independent cs a (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (a : C) :
    standardUnit cs a 1 = 1 := by
  have h := standardUnit_word cs a (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (a : C) (w : W) :
    (standardUnit cs a w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs a hω, wordUnit_val, leftWord_one cs a hω]

theorem standardUnit_simple_mul (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    standardUnit cs a (cs.simple i * w) = unit cs a i * standardUnit cs a w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (i :: ω) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_simple_mul (cs.wordProd ω) i
    simp only [cs.wordProd_cons, List.length_cons]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_cons, standardUnit_word cs a hred, standardUnit_word cs a hω]
  simp [wordUnit]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs a (w * cs.simple i) = standardUnit cs a w * unit cs a i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs a hred,
    standardUnit_word cs a hω]
  simp [wordUnit, List.map_append, List.prod_append]

/-- The bar image of an actual standard basis vector; inverse units give
expression independence before any polynomial coefficients are extracted. -/
noncomputable def barBasis (cs : CoxeterSystem M W) (a : C) (w : W) : Space W C :=
  ((standardUnit cs a w⁻¹)⁻¹).val (basis 1)

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (a : C) :
    barBasis cs a 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (a : C) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs a (cs.simple i * w) = leftInv cs a i (barBasis cs a w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs a i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl

theorem leftInv_barBasis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    leftInv cs a i (barBasis cs a w) = barBasis cs a (cs.simple i * w) -
      if cs.length (cs.simple i * w) < cs.length w then a • barBasis cs a w else 0 := by
  by_cases h : cs.length (cs.simple i * w) < cs.length w
  · have hasc : cs.length (cs.simple i * w) <
        cs.length (cs.simple i * (cs.simple i * w)) := by simpa using h
    have hb := barBasis_simple_mul_ascent cs a i (cs.simple i * w) hasc
    simp only [cs.simple_mul_simple_cancel_left] at hb
    have hl : left cs a i (barBasis cs a w) = barBasis cs a (cs.simple i * w) := by
      rw [hb, ← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
    simp only [ite_eq_left h, leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hl]
  · have hasc : cs.length w < cs.length (cs.simple i * w) := by
      have := cs.length_simple_mul w i
      omega
    rw [ite_eq_right h, sub_zero, barBasis_simple_mul_ascent cs a i w hasc]

noncomputable def barLinear (cs : CoxeterSystem M W) (a : C) : Module.End C (Space W C) :=
  Finsupp.linearCombination C (barBasis cs a)

@[simp] theorem barLinear_basis (cs : CoxeterSystem M W) (a : C) (w : W) :
    barLinear cs a (basis w) = barBasis cs a w := by
  simp [barLinear, basis, Finsupp.linearCombination_single]

/-- Intertwining with the opposite parameter. In Laurent coefficients this
is the semilinear Hecke bar relation. -/
theorem barLinear_left (cs : CoxeterSystem M W) (a : C) (i : B) :
    barLinear cs a * left cs (-a) i = leftInv cs a i * barLinear cs a := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, map_add, barLinear_basis,
    leftInv_barBasis]
  by_cases h : cs.length (cs.simple i * w) < cs.length w
  · simp [h, sub_eq_add_neg]
  · simp [h]

theorem barLinear_leftInv (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) :
    barLinear cs a (leftInv cs (-a) i v) = left cs a i (barLinear cs a v) := by
  have h := congrArg (fun f : Module.End C (Space W C) => f v) (barLinear_left cs a i)
  simp only [Module.End.mul_apply, leftInv, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h ⊢
  rw [map_sub, map_smul, h]
  simp

/-- The inverse-parameter bar transforms are mutually inverse. -/
theorem barLinear_barBasis (cs : CoxeterSystem M W) (a : C) (w : W) :
    barLinear cs a (barBasis cs (-a) w) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs (-a) i _ hasc,
      barLinear_leftInv, ih hω', left_basis, ite_eq_right (by omega), add_zero]

theorem barLinear_inverse (cs : CoxeterSystem M W) (a : C) :
    barLinear cs a * barLinear cs (-a) = 1 := by
  apply end_ext
  intro w
  simp [Module.End.mul_apply, barLinear_barBasis]


@[simp] theorem leftInv_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    leftInv cs a i (basis w) = basis (cs.simple i * w) -
      if cs.length (cs.simple i * w) < cs.length w then 0 else a • basis w := by
  simp only [leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, left_basis]
  split_ifs <;> abel

theorem left_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (left cs a i v) x = v (cs.simple i * x) +
      if cs.length (cs.simple i * x) < cs.length x then a * v x else 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv', mul_add]
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, left_basis]
    have heq : cs.simple i * w = x ↔ w = cs.simple i * x := by
      constructor <;> intro h
      · rw [← h]; simp
      · rw [h]; simp
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply, basis,
      Finsupp.single_apply, heq]
    by_cases h : w = x
    · subst w
      split_ifs <;> try contradiction
      all_goals simp only [Finsupp.single_eq_same, Finsupp.zero_apply,
        Finsupp.smul_apply, smul_eq_mul, mul_one, mul_zero] ; ring
    · simp only [h, ite_false, mul_zero]
      by_cases hd : cs.length (cs.simple i * w) < cs.length w <;>
        by_cases hd' : cs.length (cs.simple i * x) < cs.length x <;>
        simp [hd, hd', h]

theorem leftInv_coeff (cs : CoxeterSystem M W) (a : C) (i : B) (v : Space W C) (x : W) :
    (leftInv cs a i v) x = v (cs.simple i * x) -
      if cs.length (cs.simple i * x) < cs.length x then 0 else a * v x := by
  simp only [leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, left_coeff]
  split_ifs <;> ring

theorem simple_mul_le_ascent (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) (hy : cs.length y < cs.length (cs.simple i * y)) :
    BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
  have hx := le_upperSimple cs i (cs.simple i * x)
  rw [upperSimple_mul] at hx
  have hm := upperSimple_mono cs i hxy
  simp only [upperSimple, ite_eq_right (show ¬cs.length (cs.simple i * y) < cs.length y by omega)] at hm
  exact hx.trans hm

/-- Triangularity for the genuine reflection-generated order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (a : C) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs a y x = 0 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω generalizing x with
  | nil =>
    have hx : x ≠ 1 := fun h => hxy (h ▸ bruhat_refl cs 1)
    simp [basis, Ne.symm hx]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hle : BruhatLE cs (cs.wordProd ω) (cs.simple i * cs.wordProd ω) :=
      Relation.ReflTransGen.single ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    have hn : ¬BruhatLE cs x (cs.wordProd ω) := fun h => hxy (h.trans hle)
    have hn' : ¬BruhatLE cs (cs.simple i * x) (cs.wordProd ω) := by
      intro h
      have := simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (a : C) (y : W) :
    barBasis cs a y y = 1 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs a i _ hasc, leftInv_coeff]
    simpa [hasc] using ih hω'

/-- Normalized R-polynomials, obtained from the bar action rather than
postulated with an inconsistent choice of descent. -/
noncomputable def rTilde (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  barBasis cs (-X : ℤ[X]) y x

@[simp] theorem rTilde_diagonal (cs : CoxeterSystem M W) (x : W) :
    rTilde cs x x = 1 := barBasis_diagonal cs (-X) x

theorem rTilde_zero (cs : CoxeterSystem M W) (x y : W) (h : ¬BruhatLE cs x y) :
    rTilde cs x y = 0 := barBasis_zero cs (-X) x y h

theorem rTilde_recursion (cs : CoxeterSystem M W) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rTilde cs x y = if cs.length (cs.simple i * x) < cs.length x then
      rTilde cs (cs.simple i * x) (cs.simple i * y)
      else rTilde cs (cs.simple i * x) (cs.simple i * y) + X * rTilde cs x (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs (-X : ℤ[X]) i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  unfold rTilde
  rw [hb, leftInv_coeff]
  split_ifs <;> ring


end Hecke


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

/-- Unnormalized equal-parameter Hecke multiplication, T_s²=q+(q−1)T_s. -/
noncomputable def left (cs : CoxeterSystem M W) (q : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w =>
    if cs.length (cs.simple i * w) < cs.length w then
      q • basis (cs.simple i * w) + (q - 1) • basis w
    else basis (cs.simple i * w))

noncomputable def right (cs : CoxeterSystem M W) (q : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w =>
    if cs.length (w * cs.simple i) < cs.length w then
      q • basis (w * cs.simple i) + (q - 1) • basis w
    else basis (w * cs.simple i))

@[simp] theorem left_basis (cs : CoxeterSystem M W) (q : C) (i : B) (w : W) :
    left cs q i (basis w) = if cs.length (cs.simple i * w) < cs.length w then
      q • basis (cs.simple i * w) + (q - 1) • basis w
    else basis (cs.simple i * w) := by
  simp [left, basis, Finsupp.linearCombination_single]

@[simp] theorem right_basis (cs : CoxeterSystem M W) (q : C) (i : B) (w : W) :
    right cs q i (basis w) = if cs.length (w * cs.simple i) < cs.length w then
      q • basis (w * cs.simple i) + (q - 1) • basis w
    else basis (w * cs.simple i) := by
  simp [right, basis, Finsupp.linearCombination_single]

theorem left_right_commute (cs : CoxeterSystem M W) (q : C) (i j : B) :
    Commute (left cs q i) (right cs q j) := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, right_basis, left_basis]
  by_cases heq : cs.simple i * w = w * cs.simple j
  · have heq' : cs.simple i * (w * cs.simple j) = w := by rw [← heq]; simp
    have heq'' : cs.simple i * w * cs.simple j = w := by simpa [mul_assoc] using heq'
    by_cases h : cs.length (cs.simple i * w) < cs.length w
    · have h' : cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hn : ¬cs.length w < cs.length (cs.simple i * w) := by omega
      have hn' : ¬cs.length w < cs.length (w * cs.simple j) := heq ▸ hn
      simp [h', map_add, map_smul, heq', hn', heq]
    · have h' : ¬cs.length (w * cs.simple j) < cs.length w := heq ▸ h
      have hl : cs.length w < cs.length (cs.simple i * w) := by
        have := cs.length_simple_mul w i; omega
      have hl' : cs.length w < cs.length (w * cs.simple j) := heq ▸ hl
      simp [h', heq', hl', heq]
  · have hl := left_descent_mul_simple_iff cs i j w heq
    have hr := right_descent_simple_mul_iff cs i j w heq
    have hr' : cs.length (cs.simple i * (w * cs.simple j)) <
        cs.length (cs.simple i * w) ↔ cs.length (w * cs.simple j) < cs.length w := by
      simpa only [mul_assoc] using hr
    by_cases hi : cs.length (cs.simple i * w) < cs.length w <;>
      by_cases hj : cs.length (w * cs.simple j) < cs.length w <;>
      simp only [hi, hj, ite_true, ite_false, map_add, map_smul,
        left_basis, right_basis, hl, hr', mul_assoc, smul_add, smul_smul] ;
      module

theorem left_quadratic (cs : CoxeterSystem M W) (q : C) (i : B) :
    left cs q i * left cs q i = q • 1 + (q - 1) • left cs q i := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rcases cs.length_simple_mul w i with h | h
  · have hasc : ¬cs.length (cs.simple i * w) < cs.length w := by omega
    have hdesc : cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc]
  · have hdesc : cs.length (cs.simple i * w) < cs.length w := by omega
    have hasc : ¬cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc, smul_add, smul_smul]

noncomputable def leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    Module.End C (Space W C) := (↑q⁻¹ : C) • (left cs (q : C) i - ((q : C) - 1) • 1)

theorem leftInv_apply (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) :
    leftInv cs q i v = (↑q⁻¹ : C) • (left cs (q : C) i v - ((q : C) - 1) • v) := rfl

theorem left_mul_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    left cs (q : C) i * leftInv cs q i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs (q:C) i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv_apply, Module.End.one_apply,
    map_smul, map_sub]
  rw [h]
  simp [smul_smul]

theorem leftInv_mul_left (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    leftInv cs q i * left cs (q : C) i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs (q:C) i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv_apply, Module.End.one_apply]
  rw [h]
  simp [smul_smul]


noncomputable def leftWord (cs : CoxeterSystem M W) (q : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (left cs q)).prod

@[simp] theorem leftWord_nil (cs : CoxeterSystem M W) (q : C) :
    leftWord cs q [] = 1 := rfl

@[simp] theorem leftWord_cons (cs : CoxeterSystem M W) (q : C) (i : B) (ω : List B) :
    leftWord cs q (i :: ω) = left cs q i * leftWord cs q ω := rfl

/-- Acting on the identity along q reduced word gives exactly its standard
basis element. -/
theorem leftWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    leftWord cs q ω (basis 1) = basis (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : ¬cs.length (cs.simple i * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    simp [Module.End.mul_apply, ih hω', hasc, cs.wordProd_cons]

noncomputable def rightWord (cs : CoxeterSystem M W) (q : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (right cs q)).prod

@[simp] theorem rightWord_nil (cs : CoxeterSystem M W) (q : C) :
    rightWord cs q [] = 1 := rfl

@[simp] theorem rightWord_cons (cs : CoxeterSystem M W) (q : C) (i : B) (ω : List B) :
    rightWord cs q (i :: ω) = right cs q i * rightWord cs q ω := rfl

theorem rightWord_one (cs : CoxeterSystem M W) (q : C) {ω : List B}
    (hω : cs.IsReduced ω) :
    rightWord cs q ω (basis 1) = basis (cs.wordProd ω)⁻¹ := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hlen : cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) =
        cs.length (cs.simple i * cs.wordProd ω) := by
      rw [← cs.length_inv (cs.simple i * cs.wordProd ω)]
      simp [mul_inv_rev]
    have hasc : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω)⁻¹ := by
      rw [hlen, cs.length_inv]
      have := hω.eq
      rw [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hasc' : ¬cs.length ((cs.wordProd ω)⁻¹ * cs.simple i) <
        cs.length (cs.wordProd ω) := by simpa using hasc
    simp [Module.End.mul_apply, ih hω', hasc', cs.wordProd_cons, mul_inv_rev]

theorem commute_rightWord (cs : CoxeterSystem M W) (q : C)
    {f : Module.End C (Space W C)} (h : ∀ i, Commute f (right cs q i)) (ω : List B) :
    Commute f (rightWord cs q ω) := by
  apply Commute.list_prod_right
  intro r hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact h i

/-- The regular right action is cyclic, with cyclic vector the identity. -/
theorem commuting_ext (cs : CoxeterSystem M W) (q : C)
    {f g : Module.End C (Space W C)}
    (hf : ∀ i, Commute f (right cs q i))
    (hg : ∀ i, Commute g (right cs q i))
    (h : f (basis 1) = g (basis 1)) : f = g := by
  apply end_ext
  intro w
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced w⁻¹
  have hw : rightWord cs q ω (basis 1) = basis w := by
    rw [rightWord_one cs q hω, ← heq, inv_inv]
  rw [← hw]
  have hf' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hf ω).eq
  have hg' := congrArg (fun t : Module.End C (Space W C) => t (basis 1))
    (commute_rightWord cs q hg ω).eq
  simp only [Module.End.mul_apply] at hf' hg'
  rw [h] at hf'
  exact hf'.trans hg'.symm

theorem leftWord_commute_right (cs : CoxeterSystem M W) (q : C) (ω : List B) (i : B) :
    Commute (leftWord cs q ω) (right cs q i) := by
  apply Commute.list_prod_left
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  exact left_right_commute cs q j i


theorem leftWord_independent (cs : CoxeterSystem M W) (q : C) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    leftWord cs q ω = leftWord cs q η := by
  apply commuting_ext cs q (leftWord_commute_right cs q ω)
    (leftWord_commute_right cs q η)
  rw [leftWord_one cs q hω, leftWord_one cs q hη, heq]

noncomputable def unit (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    (Module.End C (Space W C))ˣ where
  val := left cs (q : C) i
  inv := leftInv cs q i
  val_inv := left_mul_leftInv cs q i
  inv_val := leftInv_mul_left cs q i

noncomputable def wordUnit (cs : CoxeterSystem M W) (q : Cˣ) (ω : List B) :
    (Module.End C (Space W C))ˣ := (ω.map (unit cs q)).prod

@[simp] theorem wordUnit_val (cs : CoxeterSystem M W) (q : Cˣ) (ω : List B) :
    (wordUnit cs q ω).val = leftWord cs (q : C) ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change (unit cs q i).val * (wordUnit cs q ω).val = left cs (q : C) i * leftWord cs (q : C) ω
    rw [ih]
    rfl

theorem wordUnit_independent (cs : CoxeterSystem M W) (q : Cˣ) {ω η : List B}
    (hω : cs.IsReduced ω) (hη : cs.IsReduced η) (heq : cs.wordProd ω = cs.wordProd η) :
    wordUnit cs q ω = wordUnit cs q η := by
  apply Units.ext
  simpa using leftWord_independent cs (q : C) hω hη heq

/-- The genuine normalized standard-basis action, a unit in the regular
endomorphism algebra. No presentation relations are assumed. -/
noncomputable def standardUnit (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    (Module.End C (Space W C))ˣ :=
  wordUnit cs q (Classical.choose (cs.exists_isReduced w))

theorem standardUnit_word (cs : CoxeterSystem M W) (q : Cˣ) {ω : List B}
    (hω : cs.IsReduced ω) :
    standardUnit cs q (cs.wordProd ω) = wordUnit cs q ω := by
  apply wordUnit_independent cs q (Classical.choose_spec (cs.exists_isReduced _)).1 hω
  exact (Classical.choose_spec (cs.exists_isReduced _)).2.symm

@[simp] theorem standardUnit_one (cs : CoxeterSystem M W) (q : Cˣ) :
    standardUnit cs q 1 = 1 := by
  have h := standardUnit_word cs q (ω := []) (by simp [CoxeterSystem.IsReduced])
  simpa [wordUnit] using h

@[simp] theorem standardUnit_basis_one (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    (standardUnit cs q w).val (basis 1) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [standardUnit_word cs q hω, wordUnit_val, leftWord_one cs (q : C) hω]

theorem standardUnit_simple_mul (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    standardUnit cs q (cs.simple i * w) = unit cs q i * standardUnit cs q w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (i :: ω) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_simple_mul (cs.wordProd ω) i
    simp only [cs.wordProd_cons, List.length_cons]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_cons, standardUnit_word cs q hred, standardUnit_word cs q hω]
  simp [wordUnit]


theorem standardUnit_mul_simple (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (w * cs.simple i)) :
    standardUnit cs q (w * cs.simple i) = standardUnit cs q w * unit cs q i := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hred : cs.IsReduced (ω ++ [i]) := by
    unfold CoxeterSystem.IsReduced
    have := cs.length_mul_simple (cs.wordProd ω) i
    simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
      List.length_singleton]
    rw [← hω.eq]
    omega
  rw [← cs.wordProd_singleton i, ← cs.wordProd_append, standardUnit_word cs q hred,
    standardUnit_word cs q hω]
  simp [wordUnit, List.map_append, List.prod_append]

/-- The bar image of an actual standard basis vector; inverse units give
expression independence before any polynomial coefficients are extracted. -/
noncomputable def barBasis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) : Space W C :=
  ((standardUnit cs q w⁻¹)⁻¹).val (basis 1)

@[simp] theorem barBasis_one (cs : CoxeterSystem M W) (q : Cˣ) :
    barBasis cs q 1 = basis 1 := by simp [barBasis]

theorem barBasis_simple_mul_ascent (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W)
    (hasc : cs.length w < cs.length (cs.simple i * w)) :
    barBasis cs q (cs.simple i * w) = leftInv cs q i (barBasis cs q w) := by
  have hasc' : cs.length w⁻¹ < cs.length (w⁻¹ * cs.simple i) := by
    have hlen : cs.length (w⁻¹ * cs.simple i) = cs.length (cs.simple i * w) := by
      rw [← cs.length_inv (cs.simple i * w)]
      simp [mul_inv_rev]
    simpa [hlen] using hasc
  simp only [barBasis, mul_inv_rev, cs.inv_simple,
    standardUnit_mul_simple cs q i w⁻¹ hasc', Units.val_mul,
    Module.End.mul_apply]
  rfl


theorem leftInv_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W) :
    leftInv cs q i (barBasis cs q w) =
      if cs.length (cs.simple i * w) < cs.length w then
        (↑q⁻¹ : C) • barBasis cs q (cs.simple i * w) +
          ((↑q⁻¹ : C) - 1) • barBasis cs q w
      else barBasis cs q (cs.simple i * w) := by
  by_cases h : cs.length (cs.simple i * w) < cs.length w
  · have hasc : cs.length (cs.simple i * w) <
        cs.length (cs.simple i * (cs.simple i * w)) := by simpa using h
    have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * w) hasc
    simp only [cs.simple_mul_simple_cancel_left] at hb
    have hl : left cs (q : C) i (barBasis cs q w) = barBasis cs q (cs.simple i * w) := by
      rw [hb, ← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
    rw [ite_eq_left h, leftInv_apply, hl, smul_sub, smul_smul]
    have hscalar : (↑q⁻¹ : C) * ((q : C) - 1) = 1 - (↑q⁻¹ : C) := by
      rw [mul_sub, q.inv_mul, mul_one]
    rw [hscalar, sub_smul, one_smul]
    module
  · have hasc : cs.length w < cs.length (cs.simple i * w) := by
      have := cs.length_simple_mul w i
      omega
    rw [ite_eq_right h, barBasis_simple_mul_ascent cs q i w hasc]

noncomputable def barLinear (cs : CoxeterSystem M W) (q : Cˣ) : Module.End C (Space W C) :=
  Finsupp.linearCombination C (barBasis cs q)

@[simp] theorem barLinear_basis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    barLinear cs q (basis w) = barBasis cs q w := by
  simp [barLinear, basis, Finsupp.linearCombination_single]

/-- Linear intertwining, before specializing coefficients to a Laurent ring. -/
theorem barLinear_left (cs : CoxeterSystem M W) (q : Cˣ) (i : B) :
    barLinear cs q * left cs (↑q⁻¹ : C) i = leftInv cs q i * barLinear cs q := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, leftInv_barBasis, barLinear_basis]
  split_ifs <;> simp

theorem barLinear_leftInv (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) :
    barLinear cs q (leftInv cs q⁻¹ i v) = left cs (q : C) i (barLinear cs q v) := by
  have h := congrArg (fun f : Module.End C (Space W C) => f (leftInv cs q⁻¹ i v))
    (barLinear_left cs q i)
  simp only [Module.End.mul_apply] at h
  have hv : left cs (↑q⁻¹ : C) i (leftInv cs q⁻¹ i v) = v := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  rw [hv] at h
  have h' := congrArg (left cs (q : C) i) h
  have hl (t : Space W C) : left cs (q : C) i (leftInv cs q i t) = t := by
    rw [← Module.End.mul_apply, left_mul_leftInv, Module.End.one_apply]
  simpa only [hl] using h'.symm

/-- Applying coefficient inversion and the Hecke bar twice is the identity. -/
theorem barLinear_barBasis (cs : CoxeterSystem M W) (q : Cˣ) (w : W) :
    barLinear cs q (barBasis cs q⁻¹ w) = basis w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q⁻¹ i _ hasc,
      barLinear_leftInv, ih hω', left_basis, ite_eq_right (by omega)]

theorem barLinear_inverse (cs : CoxeterSystem M W) (q : Cˣ) :
    barLinear cs q * barLinear cs q⁻¹ = 1 := by
  apply end_ext
  intro w
  simp [Module.End.mul_apply, barLinear_barBasis]

@[simp] theorem leftInv_basis (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (w : W) :
    leftInv cs q i (basis w) =
      if cs.length (cs.simple i * w) < cs.length w then basis (cs.simple i * w)
      else (↑q⁻¹ : C) • basis (cs.simple i * w) + ((↑q⁻¹ : C) - 1) • basis w := by
  rw [leftInv_apply, left_basis]
  split_ifs
  · simp [smul_smul]
  · rw [smul_sub, smul_smul]
    have hscalar : (↑q⁻¹ : C) * ((q : C) - 1) = 1 - (↑q⁻¹ : C) := by
      rw [mul_sub, q.inv_mul, mul_one]
    rw [hscalar, sub_smul, one_smul]
    module

theorem leftInv_coeff (cs : CoxeterSystem M W) (q : Cˣ) (i : B) (v : Space W C) (x : W) :
    leftInv cs q i v x =
      if cs.length (cs.simple i * x) < cs.length x then (↑q⁻¹ : C) * v (cs.simple i * x)
      else v (cs.simple i * x) + ((↑q⁻¹ : C) - 1) * v x := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v v' hv hv' =>
    simp only [map_add, Finsupp.add_apply, hv, hv']
    split_ifs <;> ring
  | single w c =>
    have hc : Finsupp.single w c = c • (basis w : Space W C) := by
      simp [basis, Finsupp.smul_single]
    rw [hc, map_smul, leftInv_basis]
    by_cases h : w = cs.simple i * x
    · subst w
      have hd : cs.length (cs.simple i * (cs.simple i * x)) < cs.length (cs.simple i * x) ↔
          ¬ cs.length (cs.simple i * x) < cs.length x := by
        simp only [cs.simple_mul_simple_cancel_left]
        have := cs.length_simple_mul x i
        omega
      have hn : cs.simple i * x ≠ x := by
        intro he
        have := cs.length_simple_mul x i
        rw [he] at this
        omega
      simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
        cs.simple_mul_simple_cancel_left, hn, ite_false]
      have hlength := cs.length_simple_mul x i
      split_ifs <;> try omega
      all_goals simp [Ne.symm hn] <;> try ring
    · have hn : cs.simple i * w ≠ x := by
        intro he
        apply h
        rw [← he]
        simp
      by_cases hw : w = x
      · subst w
        simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          Ne.symm hn, ite_false, ]
        split_ifs <;> simp [Ne.symm hn] ; try ring
      · simp only [Finsupp.smul_apply, smul_eq_mul, basis, Finsupp.single_apply,
          h, hw, ite_false]
        split_ifs <;> simp [hn, hw]

/-- Triangularity in the actual Bruhat order. -/
theorem barBasis_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : barBasis cs q y x = 0 := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω generalizing x with
  | nil =>
    have hx : x ≠ 1 := fun h => hxy (h ▸ bruhat_refl cs 1)
    simp [basis, Ne.symm hx]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hle : BruhatLE cs (cs.wordProd ω) (cs.simple i * cs.wordProd ω) :=
      Relation.ReflTransGen.single ⟨hasc, cs.simple i, cs.isReflection_simple i, rfl⟩
    have hn : ¬BruhatLE cs x (cs.wordProd ω) := fun h => hxy (h.trans hle)
    have hn' : ¬BruhatLE cs (cs.simple i * x) (cs.wordProd ω) := by
      intro h
      have := Hecke.simple_mul_le_ascent cs i h hasc
      simp only [cs.simple_mul_simple_cancel_left] at this
      exact hxy this
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff,
      ih x hω' hn, ih (cs.simple i * x) hω' hn']
    split_ifs <;> simp

@[simp] theorem barBasis_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (y : W) :
    barBasis cs q y y = (↑q⁻¹ : C) ^ cs.length y := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced y
  induction ω with
  | nil => simp [basis]
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.wordProd ω) < cs.length (cs.simple i * cs.wordProd ω) := by
      have := hω.eq
      simp only [cs.wordProd_cons, List.length_cons, ← hω'.eq] at this
      omega
    have hlen : cs.length (cs.simple i * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      have := cs.length_simple_mul (cs.wordProd ω) i
      omega
    rw [cs.wordProd_cons, barBasis_simple_mul_ascent cs q i _ hasc, leftInv_coeff]
    rw [cs.simple_mul_simple_cancel_left, ite_eq_left hasc, ih hω', hlen, pow_succ]
    ring

/-- R-value extracted from the genuine Hecke bar, with the classical sign
and leading q-power. No recurrence is imposed in this definition. -/
noncomputable def rValue (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) : C :=
  (-1 : C) ^ cs.length x * (-(q : C)) ^ cs.length y * barBasis cs q y x

@[simp] theorem rValue_diagonal (cs : CoxeterSystem M W) (q : Cˣ) (x : W) :
    rValue cs q x x = 1 := by
  rw [rValue, barBasis_diagonal, ← mul_pow, ← mul_pow]
  simp

theorem rValue_zero (cs : CoxeterSystem M W) (q : Cˣ) (x y : W)
    (hxy : ¬BruhatLE cs x y) : rValue cs q x y = 0 := by
  rw [rValue, barBasis_zero cs q x y hxy, mul_zero]

/-- The classical R recursion holds for *every* left descent, by Hecke
operator independence. This is the consistency obligation for actual R. -/
theorem rValue_recursion (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) (i : B)
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    rValue cs q x y =
      if cs.length (cs.simple i * x) < cs.length x then
        rValue cs q (cs.simple i * x) (cs.simple i * y)
      else ((q : C) - 1) * rValue cs q x (cs.simple i * y) +
        (q : C) * rValue cs q (cs.simple i * x) (cs.simple i * y) := by
  have hasc : cs.length (cs.simple i * y) <
      cs.length (cs.simple i * (cs.simple i * y)) := by simpa using hy
  have hb := barBasis_simple_mul_ascent cs q i (cs.simple i * y) hasc
  simp only [cs.simple_mul_simple_cancel_left] at hb
  have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
    have := cs.length_simple_mul y i
    omega
  have hu : (q : C) * (↑q⁻¹ : C) = 1 := q.val_inv
  by_cases hx : cs.length (cs.simple i * x) < cs.length x
  · have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_left hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_left hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination ((-1 : C) ^ cs.length (cs.simple i * x) *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) (cs.simple i * x)) * hu
  · have hxlen : cs.length (cs.simple i * x) = cs.length x + 1 := by
      have := cs.length_simple_mul x i
      omega
    rw [ite_eq_right hx]
    simp only [rValue, hb, leftInv_coeff, ite_eq_right hx]
    rw [hxlen, hylen]
    simp only [pow_succ]
    linear_combination -((-1 : C) ^ cs.length x *
      (-(q : C)) ^ cs.length (cs.simple i * y) *
      barBasis cs q (cs.simple i * y) x) * hu

end HeckeQ

noncomputable local instance : DecidableEq W := Classical.decEq W

/-- A concrete finite lower ideal of the genuine Bruhat order. -/
noncomputable def lowerFinset (cs : CoxeterSystem M W) (y : W) : Finset W :=
  (finite_bruhat_lower cs y).toFinset

@[simp] theorem mem_lowerFinset (cs : CoxeterSystem M W) (y x : W) :
    x ∈ lowerFinset cs y ↔ BruhatLE cs x y := by
  classical
  exact Set.Finite.mem_toFinset _

namespace HeckeQ

open Hecke (Space basis)
variable {C : Type*} [CommRing C]

theorem bar_coeff_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y, barBasis cs q z x * barBasis cs q⁻¹ y z =
      if x = y then 1 else 0 := by
  classical
  have h := congrArg (fun v : Space W C => v x) (barLinear_barBasis cs q y)
  rw [barLinear, Finsupp.linearCombination_apply, Finsupp.sum_apply] at h
  have hs : (barBasis cs q⁻¹ y).support ⊆ lowerFinset cs y := by
    intro z hz
    apply (mem_lowerFinset cs y z).mpr
    by_contra hn
    exact Finsupp.mem_support_iff.mp hz (barBasis_zero cs _ _ _ hn)
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp), basis, Finsupp.single_apply] at h
  simpa only [Finsupp.smul_apply, smul_eq_mul, mul_comm, eq_comm] using h

theorem rValue_inverse_factor (cs : CoxeterSystem M W) (q : Cˣ) (x z y : W) :
    rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y =
      ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by
  simp only [rValue]
  rw [neg_pow (q : C), neg_pow (↑q⁻¹ : C)]
  calc
    _ = ((-1 : C) ^ cs.length x * (-1 : C) ^ cs.length y) *
        (((-1 : C) * (-1)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length z *
          ((q : C) * (↑q⁻¹ : C)) ^ cs.length y) *
        (barBasis cs q z x * barBasis cs q⁻¹ y z) := by simp only [mul_pow]; ring
    _ = _ := by simp

/-- The exact R-kernel identity, before specialization to polynomials. -/
theorem rValue_inverse (cs : CoxeterSystem M W) (q : Cˣ) (x y : W) :
    ∑ z ∈ lowerFinset cs y,
      rValue cs q x z * (q : C) ^ cs.length y * (↑q⁻¹ : C) ^ cs.length z *
        rValue cs q⁻¹ z y = if x = y then 1 else 0 := by
  classical
  simp_rw [rValue_inverse_factor]
  rw [← Finset.mul_sum, bar_coeff_inverse]
  split_ifs with h
  · subst y
    rw [← mul_pow]
    simp
  · simp

end HeckeQ

/-- Reflection of a bounded-degree polynomial evaluated at an actual unit. -/
theorem eval₂_reflect_unit {C : Type*} [CommRing C] (q : Cˣ)
    (p : ℤ[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    Polynomial.eval₂ (Int.castRingHom C) (q : C) (reflect d p) =
      (q : C) ^ d * Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p := by
  let := q⁻¹.invertible
  have h := Polynomial.eval₂_reflect_mul_pow (Int.castRingHom C) (↑q⁻¹ : C) d p hp
  simp only [invOf_units, inv_inv] at h
  have h' := congrArg (fun a : C => a * (q : C) ^ d) h
  calc
    _ = Polynomial.eval₂ (Int.castRingHom C) (↑q⁻¹ : C) p * (q : C) ^ d := by
      simpa only [mul_assoc, ← mul_pow, q.inv_mul, one_pow, mul_one] using h'
    _ = _ := mul_comm _ _


end KLInvariance
end

end OAI
