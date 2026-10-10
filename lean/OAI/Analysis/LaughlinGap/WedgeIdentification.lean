import Mathlib
import OAI.Analysis.LaughlinGap.Creation
import OAI.Analysis.LaughlinGap.ThreeGram

namespace OAI

/-! Wedge Identification. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

@[simp] lemma annihilation_vacuum {n : ℕ} (i : Fin n) :
    annihilation i (vacuum n) = 0 := by
  have h := word_eq_zero_of_degree_lt [i] (vacuum_homogeneous n) (by simp)
  simpa only [word_cons, word_nil, one_mul] using h

lemma annihilation_creation_apply {n : ℕ} (i j : Fin n) (x : Hilbert n) :
    annihilation i (creation j x) = (if i=j then x else 0) - creation j (annihilation i x) := by
  have h := congrArg (fun A : Module.End ℂ (Hilbert n) => A x)
    (annihilation_creation_CAR i j)
  simp only [LinearMap.add_apply, LinearMap.comp_apply] at h
  convert eq_sub_of_add_eq h using 2
  split_ifs <;> simp only [LinearMap.id_apply, LinearMap.zero_apply]

lemma annihilation_creation_vacuum {n : ℕ} (i j : Fin n) :
    annihilation i (creation j (vacuum n)) = if i=j then vacuum n else 0 := by
  rw [annihilation_creation_apply, annihilation_vacuum, map_zero, sub_zero]

lemma double_creation_vacuum {n : ℕ} (i x y : Fin n) :
    annihilation i (creation x (creation y (vacuum n))) =
      (if i=x then creation y (vacuum n) else 0) -
      (if i=y then creation x (vacuum n) else 0) := by
  rw [annihilation_creation_apply, annihilation_creation_vacuum]
  congr 1
  split_ifs <;> simp

lemma triple_creation_vacuum {n : ℕ} (i x y z : Fin n) :
    annihilation i (creation x (creation y (creation z (vacuum n)))) =
      (if i=x then creation y (creation z (vacuum n)) else 0) -
      (if i=y then creation x (creation z (vacuum n)) else 0) +
      (if i=z then creation x (creation y (vacuum n)) else 0) := by
  rw [annihilation_creation_apply, double_creation_vacuum, map_sub]
  have h₁ : creation x (if i=y then creation z (vacuum n) else 0) =
      if i=y then creation x (creation z (vacuum n)) else 0 := by
    split_ifs <;> simp
  have h₂ : creation x (if i=z then creation y (vacuum n) else 0) =
      if i=z then creation x (creation y (vacuum n)) else 0 := by
    split_ifs <;> simp
  rw [h₁,h₂]
  abel

def orbitalDelta {n : ℕ} (i j : Fin n) : ℂ := if i=j then 1 else 0

lemma orbitalDelta_smul {n : ℕ} (i j : Fin n) (x : Hilbert n) :
    orbitalDelta i j • x = if i=j then x else 0 := by
  simp [orbitalDelta, ite_smul]

lemma annihilation_creation_vacuum_delta {n : ℕ} (i j : Fin n) :
    annihilation i (creation j (vacuum n)) = orbitalDelta i j • vacuum n := by
  rw [orbitalDelta_smul, annihilation_creation_vacuum]

lemma double_creation_vacuum_delta {n : ℕ} (i x y : Fin n) :
    annihilation i (creation x (creation y (vacuum n))) =
      orbitalDelta i x • creation y (vacuum n) -
      orbitalDelta i y • creation x (vacuum n) := by
  simp only [orbitalDelta_smul, double_creation_vacuum]

lemma triple_creation_vacuum_delta {n : ℕ} (i x y z : Fin n) :
    annihilation i (creation x (creation y (creation z (vacuum n)))) =
      orbitalDelta i x • creation y (creation z (vacuum n)) -
      orbitalDelta i y • creation x (creation z (vacuum n)) +
      orbitalDelta i z • creation x (creation y (vacuum n)) := by
  simp only [orbitalDelta_smul, triple_creation_vacuum]

lemma word_three_creation_vacuum {n : ℕ} (i j k x y z : Fin n) :
    word [i,j,k] (creation x (creation y (creation z (vacuum n)))) ∅ =
      orbitalDelta i x * (orbitalDelta j y * orbitalDelta k z -
        orbitalDelta j z * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k z -
        orbitalDelta j z * orbitalDelta k x) +
      orbitalDelta i z * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x) := by
  simp only [word_cons, word_nil, one_mul, Module.End.mul_apply,
    triple_creation_vacuum_delta, map_add, map_sub, map_smul,
    double_creation_vacuum_delta, annihilation_creation_vacuum_delta,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, vacuum_apply,
    ite_true, mul_one]

lemma sum_increasing_pairs_add {n : ℕ} {M : Type*} [AddCommGroup M]
    (f : Fin n → Fin n → M) (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ a : PairLabel n, f a.val.1 a.val.2) +
      (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]

lemma pairContraction_adjoint_apply {n : ℕ} (v : PairLabel n → ℂ) (x : Hilbert n) :
    (pairContraction v).adjoint x =
      ∑ a : PairLabel n, v a • creation a.val.1 (creation a.val.2 x) := by
  simp only [pairContraction, map_sum, map_smulₛₗ, basicPair,
    adjoint_mul, annihilation_adjoint, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, Complex.star_def, Complex.conj_conj]

lemma pairContraction_ordered_adjoint {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (x : Hilbert n) :
    (pairContraction (fun a : PairLabel n =>
      ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint x =
      ((Real.sqrt 2)⁻¹ : ℂ) •
        ∑ i, ∑ j, (c i j : ℂ) • creation i (creation j x) := by
  have hsum := sum_increasing_pairs_add
    (fun i j : Fin n => (c i j : ℂ) • creation i (creation j x)) (by
      intro i j
      have he := congrArg (fun A : Module.End ℂ (Hilbert n) => A x)
        (creation_anticommute j i)
      simp only [Module.End.mul_apply, LinearMap.neg_apply] at he
      rw [hc i j, Complex.ofReal_neg, he, neg_smul, smul_neg, neg_neg]) (by
      intro i
      have h : c i i = 0 := by have hh := hc i i; linarith
      simp [h])
  rw [← hsum, ← two_smul ℂ (∑ a : PairLabel n,
    (c a.val.1 a.val.2 : ℂ) • creation a.val.1 (creation a.val.2 x)), smul_smul]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * 2 = (Real.sqrt 2 : ℂ) := by
    have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hr : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      field_simp
      nlinarith
    exact_mod_cast hr
  rw [hs, pairContraction_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [smul_smul, Complex.ofReal_mul]

lemma sum_orbitalDelta_mul {n : ℕ} (i : Fin n) (f : Fin n → ℂ) :
    (∑ j, orbitalDelta i j * f j) = f i := by
  simp [orbitalDelta, ite_mul]

lemma sum_mul_orbitalDelta {n : ℕ} (i : Fin n) (f : Fin n → ℂ) :
    (∑ j, f j * orbitalDelta i j) = f i := by
  simp [orbitalDelta, mul_ite]

lemma pair_times_three_determinant {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    (∑ x, ∑ y, (c x y : ℂ) *
      (orbitalDelta i x * (orbitalDelta j y * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k x) +
      orbitalDelta i l * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x))) =
    2 * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  have he (x y : Fin n) : (c x y : ℂ) *
      (orbitalDelta i x * (orbitalDelta j y * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k y) -
      orbitalDelta i y * (orbitalDelta j x * orbitalDelta k l -
        orbitalDelta j l * orbitalDelta k x) +
      orbitalDelta i l * (orbitalDelta j x * orbitalDelta k y -
        orbitalDelta j y * orbitalDelta k x)) =
      orbitalDelta i x * ((c x y : ℂ) * orbitalDelta j y) * orbitalDelta k l -
      orbitalDelta i x * ((c x y : ℂ) * orbitalDelta k y) * orbitalDelta j l -
      orbitalDelta j x * ((c x y : ℂ) * orbitalDelta i y) * orbitalDelta k l +
      orbitalDelta k x * ((c x y : ℂ) * orbitalDelta i y) * orbitalDelta j l +
      orbitalDelta j x * ((c x y : ℂ) * orbitalDelta k y) * orbitalDelta i l -
      orbitalDelta k x * ((c x y : ℂ) * orbitalDelta j y) * orbitalDelta i l := by ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_mul_orbitalDelta,
    sum_orbitalDelta_mul]
  rw [hc i j, hc k i, hc j k]
  push_cast
  ring

lemma rawReadout_three_pair {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    rawReadout n 3
      ((annihilation l * pairContraction (fun a : PairLabel n =>
        ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint (vacuum n)) ![i,j,k] =
    (Real.sqrt 2 : ℂ) * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  rw [rawReadout_apply]
  simp only [List.ofFn_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    List.ofFn_zero, adjoint_mul, annihilation_adjoint, Module.End.mul_apply,
    pairContraction_ordered_adjoint c hc, map_smul, map_sum, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, word_three_creation_vacuum]
  rw [pair_times_three_determinant c hc i j k l]
  have hs : ((Real.sqrt 2)⁻¹ : ℂ) * 2 = (Real.sqrt 2 : ℂ) := by
    have hr : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      field_simp
      nlinarith
    exact_mod_cast hr
  rw [← mul_assoc, hs]

lemma normalizedReadout_three_pair {n : ℕ} (c : Fin n → Fin n → ℝ)
    (hc : ∀ i j, c j i = -c i j) (i j k l : Fin n) :
    normalizedReadout n 3
      ((annihilation l * pairContraction (fun a : PairLabel n =>
        ((Real.sqrt 2 * c a.val.1 a.val.2 : ℝ) : ℂ))).adjoint (vacuum n)) ![i,j,k] =
    ((Real.sqrt 3)⁻¹ : ℂ) * ((c i j : ℂ) * orbitalDelta k l +
      (c j k : ℂ) * orbitalDelta i l + (c k i : ℂ) * orbitalDelta j l) := by
  change ((Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ : ℂ) * rawReadout n 3 _ ![i,j,k] = _
  rw [rawReadout_three_pair c hc i j k l, ← mul_assoc]
  have hs : (Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ * Real.sqrt 2 = (Real.sqrt 3)⁻¹ := by
    norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one]
    rw [show (6:ℝ)=3*2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hz : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  have hs' : ((Real.sqrt ((3:ℕ).factorial : ℝ))⁻¹ : ℂ) * (Real.sqrt 2 : ℂ) =
      ((Real.sqrt 3)⁻¹ : ℂ) := by exact_mod_cast hs
  rw [hs']

lemma normalizedReadout_inner_sector {n N : ℕ} (x y : ExteriorCoordinates n N) :
    inner ℂ (normalizedReadout n N (sectorInclusion n N x))
      (normalizedReadout n N (sectorInclusion n N y)) = inner ℂ x y := by
  let f := (normalizedReadout n N).comp (sectorInclusion n N)
  apply (LinearMap.norm_map_iff_inner_map_map f).mp _ x y
  intro a
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact (normalizedReadout_norm_sq (sectorInclusion_homogeneous a)).trans
    (sectorInclusion_norm_sq a)

end LaughlinGap.Occupation

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation

def tupleThreeEquiv (ι : Type*) : ThreeIndex ι ≃ (Fin 3 → ι) where
  toFun t := ![t.1.1,t.1.2,t.2]
  invFun a := ((a 0,a 1),a 2)
  left_inv _ := rfl
  right_inv a := by ext i; fin_cases i <;> rfl

noncomputable def spinPairForms (Q : ℕ) : Fin (2*Q-2+1) → PairLabel (Q+1) → ℂ := fun p a =>
  (sphericalExteriorPairCoefficient Q p.val a.val.1.val a.val.2.val : ℂ)

lemma normalizedReadout_spin_three_column {Q : ℕ} (hQ : 2 ≤ Q)
    (p : Fin (2*Q-2+1)) (l i j k : Fin (Q+1)) :
    normalizedReadout (Q+1) 3
      (sectorInclusion (Q+1) 3 (tripleWedgeColumn (spinPairForms Q p) l)) ![i,j,k] =
    ((orderedThreeWedge hQ (Pi.single (p,l) 1) ((i,j),k) : ℝ) : ℂ) := by
  have hh : Homogeneous 3
      ((annihilation l * pairContraction (spinPairForms Q p)).adjoint (vacuum (Q+1))) := by
    rw [adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous _ (creation_homogeneous (vacuum_homogeneous _) _)
  rw [tripleWedgeColumn, sectorInclusion_readout hh]
  have hv : spinPairForms Q p = fun a : PairLabel (Q+1) =>
      ((Real.sqrt 2 * pairCoefficient Q p.val a.val.1 a.val.2 : ℝ) : ℂ) := by
    funext a
    exact congrArg Complex.ofReal (sphericalExteriorPairCoefficient_eq_tensor _ _ _ _)
  rw [hv, normalizedReadout_three_pair _ (fun i j => pairCoefficient_swap Q p.val i j)]
  simp only [orderedThreeWedge, LinearMap.smul_apply, LinearMap.comp_apply,
    Pi.smul_apply, smul_eq_mul, cyclicSum_apply, Pi.add_apply, cycleMap_apply,
    pairSpectatorInclusion_apply]
  simp [Pi.single_apply, mul_ite, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_inv, orbitalDelta, ite_and]
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero]

lemma spinTripleGram_entry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : Fin (2*Q-2+1) × Fin (Q+1)) :
    ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)) a b =
    ((orderedThreeGram hQ (Pi.single b 1) a : ℝ) : ℂ) := by
  have he : ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)) a b =
      inner ℂ (tripleWedgeColumn (spinPairForms Q a.1) a.2)
        (tripleWedgeColumn (spinPairForms Q b.1) b.2) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tripleWedgeMatrix,
      PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he, ← normalizedReadout_inner_sector, PiLp.inner_apply]
  rw [← (tupleThreeEquiv (Fin (Q+1))).sum_comp]
  change (∑ t : ThreeIndex (Fin (Q+1)),
    inner ℂ
      (normalizedReadout (Q+1) 3 (sectorInclusion (Q+1) 3
        (tripleWedgeColumn (spinPairForms Q a.1) a.2)) ![t.1.1,t.1.2,t.2])
      (normalizedReadout (Q+1) 3 (sectorInclusion (Q+1) 3
        (tripleWedgeColumn (spinPairForms Q b.1) b.2)) ![t.1.1,t.1.2,t.2])) = _
  simp only [normalizedReadout_spin_three_column hQ, RCLike.inner_apply,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  change dotProduct (orderedThreeWedge hQ (Pi.single b 1))
    (orderedThreeWedge hQ (Pi.single a 1)) = _
  rw [dotProduct_comm, transposeMap_adjoint, dotProduct_comm, dotProduct_single_one]
  rfl

lemma linearMap_apply_coordinates {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (x : ι → ℝ) (k : κ) :
    (∑ i, A (Pi.single i 1) k * x i) = A x k := by
  conv_rhs => rw [A.pi_apply_eq_sum_univ x]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]
  have he : Pi.single i (1:ℝ) = (fun j : ι => if i=j then (1:ℝ) else 0) := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [he]

theorem spinTripleGram_mulVec_real {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)).mulVec (fun i => (a i : ℂ)) =
        fun i => ((orderedThreeGram hQ a i : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, spinTripleGram_entry hQ,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, linearMap_apply_coordinates]

theorem spinTripleGram_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    ((tripleWedgeMatrix (spinPairForms Q)).conjTranspose *
      tripleWedgeMatrix (spinPairForms Q)).mulVec
      (fun i => (coupledTensor (2*Q-2) Q z l i : ℂ)) =
    (1+(threeBodyGramCoefficient Q z : ℂ)) •
      (fun i => (coupledTensor (2*Q-2) Q z l i : ℂ)) := by
  rw [spinTripleGram_mulVec_real hQ, orderedThreeGram_eigenvalue hQ hz hl]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one]

end LaughlinGap.Spin

namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

def physicalPairIndexEquiv {Q : ℕ} (hQ : 2 ≤ Q) :
    Fin (2*Q-1) ≃ Fin (2*Q-2+1) := finCongr (by omega)

def physicalThreeIndexEquiv {Q : ℕ} (hQ : 2 ≤ Q) :
    (Fin (2*Q-1) × Fin (Q+1)) ≃ (Fin (2*Q-2+1) × Fin (Q+1)) :=
  Equiv.prodCongr (physicalPairIndexEquiv hQ) (Equiv.refl _)

@[simp] lemma spinPairForms_physical_index {Q : ℕ} (hQ : 2 ≤ Q) (p : Fin (2*Q-1)) :
    spinPairForms Q (physicalPairIndexEquiv hQ p) = physicalPairForms Q p := rfl

@[simp] lemma spinTripleWedge_physical_index {Q : ℕ} (hQ : 2 ≤ Q)
    (a : BasisLabel (Q+1) 3) (p : Fin (2*Q-1) × Fin (Q+1)) :
    tripleWedgeMatrix (spinPairForms Q) a (physicalThreeIndexEquiv hQ p) =
      tripleWedgeMatrix (physicalPairForms Q) a p := rfl

lemma physicalTripleGram_entry {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : Fin (2*Q-1) × Fin (Q+1)) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)) a b =
    ((orderedThreeGram hQ (Pi.single (physicalThreeIndexEquiv hQ b) 1)
      (physicalThreeIndexEquiv hQ a) : ℝ) : ℂ) := by
  exact spinTripleGram_entry hQ (physicalThreeIndexEquiv hQ a)
    (physicalThreeIndexEquiv hQ b)

theorem physicalTripleGram_mulVec_real {Q : ℕ} (hQ : 2 ≤ Q)
    (a : (Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)).mulVec
        (fun i => (a (physicalThreeIndexEquiv hQ i) : ℂ)) =
      fun i => ((orderedThreeGram hQ a (physicalThreeIndexEquiv hQ i) : ℝ) : ℂ) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, physicalTripleGram_entry hQ,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [(physicalThreeIndexEquiv hQ).sum_comp (fun j =>
    orderedThreeGram hQ (Pi.single j 1) (physicalThreeIndexEquiv hQ i) * a j)]
  rw [linearMap_apply_coordinates]

noncomputable def physicalThreeVector {Q : ℕ} (hQ : 2 ≤ Q) (z l : ℕ) :
    (Fin (2*Q-1) × Fin (Q+1)) → ℂ := fun i =>
  (coupledTensor (2*Q-2) Q z l (physicalThreeIndexEquiv hQ i) : ℂ)

theorem physicalTripleGram_eigenvalue {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) :
    ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
      tripleWedgeMatrix (physicalPairForms Q)).mulVec (physicalThreeVector hQ z l) =
    (1+(threeBodyGramCoefficient Q z : ℂ)) • physicalThreeVector hQ z l := by
  unfold physicalThreeVector
  rw [physicalTripleGram_mulVec_real hQ, orderedThreeGram_eigenvalue hQ hz hl]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one]

theorem physicalTripleWedge_null {Q z l : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hl : l ≤ (2*Q-2)+Q-2*z) (hn : z=0 ∨ z=1 ∨ z=3) :
    (tripleWedgeMatrix (physicalPairForms Q)).mulVec (physicalThreeVector hQ z l) = 0 := by
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _).mp
  have hq : threeBodyGramCoefficient Q z = -1 := by
    rcases hn with rfl | rfl | rfl
    · exact threeBodyGramCoefficient_zero Q
    · exact threeBodyGramCoefficient_one hQ
    · exact threeBodyGramCoefficient_three hz
  rw [physicalTripleGram_eigenvalue hQ hz hl, hq]
  simp

end LaughlinGap.Spin

end

end OAI
