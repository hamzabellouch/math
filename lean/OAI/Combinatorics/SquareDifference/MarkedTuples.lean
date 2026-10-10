import OAI.Combinatorics.SquareDifference.ReflectionLaw

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

lemma tuple_marked_uniform {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT + 1)
    (b : Fin tupleBlocks) (hb : b ∈ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * (𝔼 Y : TupleListEntry S → ZMod p,
      𝔼 j : CutHalf b α β → TupleListIndex S,
        tupleValidity S Y * (F (fun v => Y (tupleProjection S v.1, j v)))^2) ≤
      tupleCutForm S b α β F := by
  refine le_trans (mul_le_mul_of_nonneg_right (tupleMarkedConstant_le S hs b hne) ?_)
    (tuple_marked_lower S b hb hne F)
  exact expect_nonneg fun Y _ => expect_nonneg fun j _ =>
    mul_nonneg (tupleValidity_nonneg _ _) (sq_nonneg _)

lemma tuple_marking_domination {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹ *
      tupleUnmarkedMoment S b hb hne F ≤ tupleCutForm (insert b S) b α β F := by
  have hr := tuple_regroup_moment S hs b hb hne F
  rw [card_tupleHalf b hne] at hr
  have hs' : (insert b S).card ≤ tupleT + 1 := by
    rw [card_insert_of_notMem hb]; omega
  have h := mul_le_mul_of_nonneg_left hr tupleMarkedConstant_pos.le
  rw [← mul_assoc] at h
  exact h.trans (tuple_marked_uniform (insert b S) hs' b (mem_insert_self ..) hne F)

lemma truncated_sum_nonneg_of_pairs {B : Type*} [Fintype B] [DecidableEq B]
    (b : B) (t : ℕ) (f : Finset B → ℝ)
    (hpair : ∀ S, b ∉ S → S.card ≤ t → 0 ≤ f S + f (insert b S))
    (hterm : ∀ S, b ∉ S → S.card = t + 1 → 0 ≤ f S) :
    0 ≤ ∑ S ∈ (univ : Finset B).powerset, if S.card ≤ t + 1 then f S else 0 := by
  classical
  rw [← insert_erase (mem_univ b), sum_powerset_insert (notMem_erase b univ), ← sum_add_distrib]
  apply sum_nonneg
  intro S hS
  have hb : b ∉ S := notMem_mono (mem_powerset.mp hS) (notMem_erase b univ)
  rw [card_insert_of_notMem hb]
  by_cases ht : S.card ≤ t
  · simp only [ite_eq_left (by omega : S.card ≤ t + 1),
      ite_eq_left (by omega : S.card + 1 ≤ t + 1)]
    exact hpair S hb ht
  · by_cases he : S.card = t + 1
    · simp only [he, le_refl, ite_true, ite_eq_right (by omega : ¬ t + 1 + 1 ≤ t + 1), add_zero]
      exact hterm S hb he
    · simp [show ¬ S.card ≤ t + 1 by omega, show ¬ S.card + 1 ≤ t + 1 by omega]

lemma balanced_rpow_error {C a p : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hp : 0 < p)
    (hthreshold : (C / a)^16 ≤ p) :
    C * p^(-(1 : ℝ)/8) ≤ a * p^(-(1 : ℝ)/16) := by
  have hroot := Real.rpow_le_rpow (pow_nonneg (div_nonneg hC ha.le) 16) hthreshold
    (by norm_num : 0 ≤ (1 : ℝ)/16)
  have hx : ((C/a)^16)^((1 : ℝ)/16) = C/a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hC ha.le)]
    norm_num
  rw [hx] at hroot
  have hh := mul_le_mul_of_nonneg_right hroot
    (mul_nonneg ha.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/8)))
  have hpow : p^((1 : ℝ)/16) * p^(-(1 : ℝ)/8) = p^(-(1 : ℝ)/16) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    C * p^(-(1 : ℝ)/8) = (C/a) * (a * p^(-(1 : ℝ)/8)) := by field_simp
    _ ≤ p^((1 : ℝ)/16) * (a * p^(-(1 : ℝ)/8)) := hh
    _ = a * p^(-(1 : ℝ)/16) := by rw [mul_left_comm, hpow]

lemma tupleUnmarkedConstant_nonneg : 0 ≤ tupleUnmarkedConstant :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) _)
    (sq_nonneg _)

noncomputable def tupleReflectionThreshold : ℝ :=
  max 3 ((tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount /
    tupleMarkedConstant)^16)

lemma tuple_pair_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (S : Finset (Fin tupleBlocks)) (hs : S.card ≤ tupleT)
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleCutForm S b α β F + (p : ℝ)^(-(1 : ℝ)/16) *
      tupleCutForm (insert b S) b α β F := by
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp3
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  let a := tupleMarkedConstant * ((tupleR : ℝ)^tupleHalfCount)⁻¹
  have hr : 0 < (tupleR : ℝ)^tupleHalfCount := pow_pos (Nat.cast_pos.mpr tupleR_pos) _
  have ha : 0 < a := mul_pos tupleMarkedConstant_pos (inv_pos.mpr hr)
  have hC : tupleUnmarkedConstant / a =
      tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount / tupleMarkedConstant := by
    dsimp [a]
    field_simp
  have hthreshold : (tupleUnmarkedConstant / a)^16 ≤ (p : ℝ) := by
    rw [hC]
    exact (le_max_right _ _).trans hp
  have hc := balanced_rpow_error tupleUnmarkedConstant_nonneg ha hp0 hthreshold
  have hl := tuple_unmarked_error hp2 S (by omega) b hb hne F
  have hd := tuple_marking_domination S hs b hb hne F
  have hd' := mul_le_mul_of_nonneg_left hd
    (Real.rpow_nonneg hp0.le (-(1 : ℝ)/16))
  have hD := tupleUnmarkedMoment_nonneg S b hb hne F
  have hcd := mul_le_mul_of_nonneg_right hc hD
  dsimp [a] at hcd
  nlinarith

noncomputable def tupleMixtureWeight (p : ℕ) (S : Finset (Fin tupleBlocks)) : ℝ :=
  (p : ℝ)^(-(S.card : ℝ)/16)

lemma tupleMixtureWeight_nonneg (p : ℕ) (S : Finset (Fin tupleBlocks)) :
    0 ≤ tupleMixtureWeight p S := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma tupleMixtureWeight_insert {p : ℕ} (hp : 0 < p)
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S) :
    tupleMixtureWeight p (insert b S) = tupleMixtureWeight p S * (p : ℝ)^(-(1 : ℝ)/16) := by
  unfold tupleMixtureWeight
  rw [card_insert_of_notMem hb, Nat.cast_add, Nat.cast_one]
  rw [show -((S.card : ℝ)+1)/16 = -(S.card : ℝ)/16 + -(1 : ℝ)/16 by ring]
  exact Real.rpow_add (Nat.cast_pos.mpr hp) _ _

noncomputable def tupleMixture {p : ℕ} [Fact p.Prime]
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin tupleBlocks)).powerset,
    if S.card ≤ tupleT + 1 then tupleMixtureWeight p S * tupleComponent S G else 0

lemma tupleMixture_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleMixture (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply truncated_sum_nonneg_of_pairs b tupleT
  · intro S hb hs
    have hh := mul_nonneg (tupleMixtureWeight_nonneg p S) (tuple_pair_positive hp S hs b hb hne F)
    rw [tupleMixtureWeight_insert (Fact.out : p.Prime).pos S b hb]
    simpa only [tupleCutForm, mul_add, mul_assoc] using hh
  · intro S hb hs
    exact mul_nonneg (tupleMixtureWeight_nonneg p S)
      (tuple_terminal_positive (by
        have hc : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
        intro h; subst p; norm_num at hc) S hs b hb hne F)

lemma tupleMixture_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleMixture (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply sum_congr rfl
  intro S _
  split_ifs
  · rw [tupleCutForm_symmetric]
  · rfl

noncomputable def tupleComponentMap {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleComponent S
  map_add' F G := by simp [tupleComponent, mul_add, expect_add_distrib]
  map_smul' c F := by
    simp only [tupleComponent, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ a b d : ℝ, a * b * (c * d) = c * (a * b * d) by intros; ring]
    simp_rw [← mul_expect]
    rfl

noncomputable def tupleMixtureMap {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleMixture
  map_add' F G := by
    unfold tupleMixture
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (F+G) = _
      rw [map_add, mul_add]
      rfl
    · simp
  map_smul' c F := by
    change tupleMixture (c • F) = c * tupleMixture F
    unfold tupleMixture
    rw [mul_sum]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (c • F) = _
      rw [map_smul, smul_eq_mul]
      change tupleMixtureWeight p S * (c * tupleComponent S F) =
        c * (tupleMixtureWeight p S * tupleComponent S F)
      ring
    · simp

lemma tupleMixtureMap_apply {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) : tupleMixtureMap F = tupleMixture F := by
  simp only [tupleMixtureMap, LinearMap.coe_mk, AddHom.coe_mk]

lemma tupleMixture_nonneg {p : ℕ} [Fact p.Prime]
    (F : (TupleVertex → ZMod p) → ℝ) (hF : ∀ z, 0 ≤ F z) :
    0 ≤ tupleMixture F := by
  apply sum_nonneg
  intro S _
  split_ifs
  · exact mul_nonneg (tupleMixtureWeight_nonneg p S) (tupleComponent_nonneg S F hF)
  · exact le_rfl

noncomputable def tupleLeadingEdges : ℕ := (tupleListEdges ∅).card

noncomputable def tupleLeadingMassLower : ℝ := (1/2 : ℝ)^(tupleLeadingEdges+1)

noncomputable def tupleMassThreshold : ℝ :=
  max 3 (((2 : ℝ)^(tupleLeadingEdges+1) * tupleLeadingEdges)^2)

lemma tupleLeadingMassLower_pos : 0 < tupleLeadingMassLower := pow_pos (by norm_num) _

lemma error_le_of_square_threshold {E c p : ℝ} (hE : 0 ≤ E) (hc : 0 < c)
    (hp : 0 < p) (h : (E/c)^2 ≤ p) : E * p^(-(1 : ℝ)/2) ≤ c := by
  have hh := Real.rpow_le_rpow (sq_nonneg (E/c)) h (by norm_num : 0 ≤ (1 : ℝ)/2)
  have he : ((E/c)^2)^((1 : ℝ)/2) = E/c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hE hc.le)]
    norm_num
  rw [he] at hh
  have hh' := mul_le_mul_of_nonneg_right hh
    (mul_nonneg hc.le (Real.rpow_nonneg hp.le (-(1 : ℝ)/2)))
  have hp' : p^((1 : ℝ)/2) * p^(-(1 : ℝ)/2) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = (E/c) * (c * p^(-(1 : ℝ)/2)) := by field_simp
    _ ≤ p^((1 : ℝ)/2) * (c * p^(-(1 : ℝ)/2)) := hh'
    _ = c := by rw [mul_left_comm, hp', mul_one]

lemma leading_mass_lower_of_count (e : ℕ) {m p : ℝ}
    (hp : max 3 (((2 : ℝ)^(e+1) * e)^2) ≤ p)
    (hcount : |m-(1/2 : ℝ)^e| ≤ (e : ℝ)*p^(-(1 : ℝ)/2)) :
    (1/2 : ℝ)^(e+1) ≤ m := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<3) ((le_max_left _ _).trans hp)
  have hc0 : 0 < (1/2 : ℝ)^(e+1) := pow_pos (by norm_num) _
  have he : (e : ℝ) / (1/2 : ℝ)^(e+1) = (2 : ℝ)^(e+1)*e := by
    rw [one_div_pow]
    field_simp
  have hc := error_le_of_square_threshold (Nat.cast_nonneg e) hc0 hp0
    (by rw [he]; exact (le_max_right _ _).trans hp)
  have hc2 : (1/2 : ℝ)^e = 2*(1/2 : ℝ)^(e+1) := by rw [pow_succ]; ring
  have he' := hcount.trans hc
  rw [abs_le, hc2] at he'
  linarith [he'.1]

lemma tupleLeading_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleComponent (p := p) ∅ (fun _ => 1) := by
  apply leading_mass_lower_of_count tupleLeadingEdges hp
  have hp3 : (3 : ℝ) ≤ p := (le_max_left _ _).trans hp
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp3
  exact (tuple_leading_mass hp2).trans (mul_le_mul_of_nonneg_left
    (square_delta_le (p := p)) (Nat.cast_nonneg tupleLeadingEdges))

lemma tupleMixture_mass_lower {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) :
    tupleLeadingMassLower ≤ tupleMixture (p := p) (fun _ => 1) := by
  refine (tupleLeading_mass_lower hp).trans ?_
  have hterm : ∀ S : Finset (Fin tupleBlocks), 0 ≤
      if S.card ≤ tupleT+1 then tupleMixtureWeight p S * tupleComponent (p := p) S (fun _ => 1) else 0 := by
    intro S
    split_ifs
    · exact mul_nonneg (tupleMixtureWeight_nonneg p S)
        (tupleComponent_nonneg S _ (fun _ => by norm_num))
    · exact le_rfl
  have hh := single_le_sum (s := (univ : Finset (Fin tupleBlocks)).powerset)
    (fun S _ => hterm S) (a := ∅) (mem_powerset.mpr (empty_subset _))
  simpa only [card_empty, Nat.zero_le, ite_true, tupleMixtureWeight, Nat.cast_zero,
    neg_zero, zero_div, Real.rpow_zero, one_mul, tupleMixture] using hh

lemma tupleMixtureWeight_le_one {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) : tupleMixtureWeight p S ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast (Fact.out : p.Prime).one_lt.le
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by norm_num)

lemma tupleMixture_mass_upper {p : ℕ} [Fact p.Prime] :
    tupleMixture (p := p) (fun _ => 1) ≤ (2 : ℝ)^tupleBlocks * tupleWeightBound := by
  calc
    _ ≤ ∑ _S ∈ (univ : Finset (Fin tupleBlocks)).powerset, tupleWeightBound := by
      apply sum_le_sum
      intro S _
      split_ifs with hs
      · exact (mul_le_mul_of_nonneg_right (tupleMixtureWeight_le_one S)
          (tupleComponent_nonneg S _ (fun _ => by norm_num))).trans
          (by simpa using tupleComponent_mass_le (p := p) S hs)
      · exact tupleWeightBound_pos.le
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_powerset, card_univ,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

noncomputable def tupleLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleMixture (p := p) (fun _ => 1))⁻¹ • tupleMixtureMap

lemma tupleLaw_probability {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) : tupleLaw (p := p) (fun _ => 1) = 1 := by
  have hm := lt_of_lt_of_le tupleLeadingMassLower_pos (tupleMixture_mass_lower hp)
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    inv_mul_cancel₀ hm.ne']

lemma tupleLaw_nonneg {p : ℕ} [Fact p.Prime] (F : (TupleVertex → ZMod p) → ℝ)
    (hF : ∀ z, 0 ≤ F z) : 0 ≤ tupleLaw F :=
  mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
    (by rw [tupleMixtureMap_apply]; exact tupleMixture_nonneg F hF)

lemma tupleLaw_reflection_positive {p : ℕ} [Fact p.Prime]
    (hp : tupleReflectionThreshold ≤ (p : ℝ))
    (b : Fin tupleBlocks) {α β : Fin tupleH} (hne : α ≠ β)
    (F : (CutHalf b α β → ZMod p) → ℝ) :
    0 ≤ tupleLaw (fun z => F (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  apply mul_nonneg (inv_nonneg.mpr (tupleMixture_nonneg _ (fun _ => by norm_num)))
  rw [tupleMixtureMap_apply]
  exact tupleMixture_reflection_positive hp b hne F

lemma tupleLaw_symmetric {p : ℕ} [Fact p.Prime]
    (b : Fin tupleBlocks) (α β : Fin tupleH)
    (F G : (CutHalf b α β → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => z v.1) * G (fun v => z (reflect b α β v.1))) =
    tupleLaw (fun z => G (fun v => z v.1) * F (fun v => z (reflect b α β v.1))) := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply,
    tupleMixture_symmetric b α β F G]

noncomputable def finiteIntegral {X : Type*} [Fintype X] (w : X → ℝ) :
    (X → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ x, w x * f x
  map_add' f g := by simp [mul_add, sum_add_distrib]
  map_smul' c f := by simp [mul_left_comm, mul_sum]

lemma finiteIntegral_nonneg {X : Type*} [Fintype X] (w f : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteIntegral w f :=
  sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

lemma linearFunctional_density {X : Type*} [Fintype X] [DecidableEq X]
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (f : X → ℝ) :
    L f = ∑ x, L (fun y => if y = x then 1 else 0) * f x := by
  classical
  have hf : f = ∑ x, f x • (fun y => if y = x then (1 : ℝ) else 0) := by
    ext y
    simp
  conv_lhs => rw [hf, map_sum]
  apply sum_congr rfl
  intro x _
  simp [mul_comm]

lemma cut_cauchy_schwarz {X I : Type*}
    (L : (X → ℝ) →ₗ[ℝ] ℝ) (left right : X → I)
    (hsym : ∀ F G : I → ℝ,
      L (fun z => F (left z) * G (right z)) =
      L (fun z => G (left z) * F (right z)))
    (hpos : ∀ F : I → ℝ, 0 ≤ L (fun z => F (left z) * F (right z)))
    (F G : I → ℝ) :
    |L (fun z => F (left z) * G (right z))|^2 ≤
      L (fun z => F (left z) * F (right z)) *
      L (fun z => G (left z) * G (right z)) := by
  have hquad (t : ℝ) := hpos (fun x => t * F x + G x)
  have heq (t : ℝ) :
      (fun z => (t * F (left z) + G (left z)) *
        (t * F (right z) + G (right z))) =
      (t*t) • (fun z => F (left z) * F (right z)) +
      t • (fun z => F (left z) * G (right z)) +
      t • (fun z => G (left z) * F (right z)) +
      (fun z => G (left z) * G (right z)) := by
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [heq, map_add, map_smul, smul_eq_mul, ← hsym F G] at hquad
  have hq := discrim_le_zero (fun t => show 0 ≤
    L (fun z => F (left z) * F (right z)) * (t*t) +
      (2*L (fun z => F (left z) * G (right z))) * t +
      L (fun z => G (left z) * G (right z)) by nlinarith [hquad t])
  rw [discrim] at hq
  rw [sq_abs]
  nlinarith

noncomputable def multilinearIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) : ℝ :=
  L (fun z => ∏ v, a v (z v))

noncomputable def diagonalIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  multilinearIntegral L (fun _ => g)

lemma multilinearIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) (c : V → ℝ) :
    multilinearIntegral L (fun v x => a v x / c v) =
      multilinearIntegral L a / ∏ v, c v := by
  unfold multilinearIntegral
  simp_rw [prod_div_distrib]
  have he : (fun z : V → X => (∏ v, a v (z v)) / ∏ v, c v) =
      (∏ v, c v)⁻¹ • (fun z : V → X => ∏ v, a v (z v)) := by
    ext z
    simp [div_eq_mul_inv, mul_comm]
  rw [he, map_smul, smul_eq_mul]
  ring

lemma diagonalIntegral_div {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) (c : ℝ) :
    diagonalIntegral L (fun x => g x / c) =
      diagonalIntegral L g / c^(Fintype.card V) := by
  unfold diagonalIntegral
  simpa only [prod_const, card_univ] using
    multilinearIntegral_div L (fun _ => g) (fun _ => c)

lemma holder_of_finite_maximum {V X : Type*} [Fintype V] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hdiag : ∀ g, 0 ≤ diagonalIntegral L g)
    (hmax : ∀ a : V → X → ℝ, ∃ i : V,
      |multilinearIntegral L a| ≤ diagonalIntegral L (a i))
    (a : V → X → ℝ) :
    |multilinearIntegral L a| ≤
      ∏ v, (diagonalIntegral L (a v))^((1 : ℝ)/(Fintype.card V : ℝ)) := by
  classical
  let d : ℝ := Fintype.card V
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hε (ε : ℝ) (hε : 0 < ε) :
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    let c (v : V) : ℝ := (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)
    have hc (v : V) : 0 < c v := Real.rpow_pos_of_pos (by linarith [hdiag (a v)]) _
    have hcp (v : V) : c v ^ Fintype.card V = diagonalIntegral L (a v)+ε := by
      dsimp [c]
      rw [← Real.rpow_mul_natCast (le_of_lt (by linarith [hdiag (a v)] :
        0 < diagonalIntegral L (a v)+ε))]
      change (diagonalIntegral L (a v)+ε)^((1/d)*d) = _
      rw [one_div_mul_cancel hd.ne', Real.rpow_one]
    obtain ⟨i, hi⟩ := hmax (fun v x => a v x / c v)
    rw [multilinearIntegral_div, diagonalIntegral_div, hcp] at hi
    have hle : diagonalIntegral L (a i) / (diagonalIntegral L (a i)+ε) ≤ 1 := by
      apply (div_le_one (by linarith [hdiag (a i)])).mpr
      linarith
    have hprod : 0 < ∏ v, c v := prod_pos fun v _ => hc v
    rw [abs_div, abs_of_pos hprod] at hi
    exact (div_le_one hprod).mp (hi.trans hle)
  have hc : Continuous (fun ε : ℝ =>
      ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d)) := by
    apply continuous_finsetProd
    intro v _
    exact (Real.continuous_rpow_const (div_nonneg zero_le_one hd.le)).comp
      (continuous_const.add continuous_id)
  have ht := hc.continuousAt.tendsto.mono_left (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 by
    exact inf_le_left)
  have hevent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      |multilinearIntegral L a| ≤ ∏ v, (diagonalIntegral L (a v)+ε)^((1 : ℝ)/d) := by
    filter_upwards [self_mem_nhdsWithin] with ε hεpos
    exact hε ε hεpos
  have hh := ge_of_tendsto ht hevent
  simpa only [add_zero] using hh

lemma prod_word_split {B M : Type*} [Fintype B] [DecidableEq B] [CommMonoid M]
    {h : ℕ} (b : B) {α β : Fin h} (hne : α ≠ β) (f : WordVertex B h → M) :
    ∏ v, f v = (∏ v : CutHalf b α β, f v.1) *
      ∏ v : CutHalf b α β, f (reflect b α β v.1) := by
  classical
  rw [← Fintype.prod_equiv (halfSumEquiv b hne) (fun v => f (halfSumEquiv b hne v)) f
    (fun _ => rfl)]
  exact Fintype.prod_sum_type _

lemma foldWord_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b α β v.1 = v.1 := ite_eq_left v.2

lemma foldWord_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hne : α ≠ β) (v : CutHalf b α β) :
    foldWord b α β (reflect b α β v.1) = v.1 := by
  have hn : ¬ cutPlus b α β (reflect b α β v.1) := by
    rw [cutPlus_reflect_iff_not b hne]
    exact not_not.mpr v.2
  rw [foldWord, ite_eq_right hn, reflect_involutive]

lemma reflect_comm {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : reflect b α β = reflect b β α := by
  funext v
  simp only [reflect, Equiv.swap_comm α β]

lemma foldWord_opposite_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α v.1 = reflect b α β v.1 := by
  have hn : ¬ cutPlus b β α v.1 := not_lt_of_gt v.2
  rw [foldWord, ite_eq_right hn, reflect_comm b β α]

lemma foldWord_opposite_reflect_half {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : CutHalf b α β) :
    foldWord b β α (reflect b α β v.1) = reflect b α β v.1 := by
  apply ite_eq_left
  rw [reflect_comm b α β, reflect_cutPlus]
  exact v.2

noncomputable def halfProduct {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (a : WordVertex B h → X → ℝ)
    (x : CutHalf b α β → X) : ℝ := ∏ v, a v.1 (x v)

end SquareDifference
end

end OAI
