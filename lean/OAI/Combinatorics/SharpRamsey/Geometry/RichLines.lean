/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import Mathlib

namespace OAI

/-! Incidence bounds for rich lines and finite point configurations. -/

section
section

section

namespace SharpLogRamsey.ImplicitBranch
open Polynomial
open scoped Ring

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

The following Hensel lifting theorem is adapted from Mathlib.RingTheory.Henselian.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Henselian.lean

This code has been modified.
-/

 theorem hensel_nonmonic {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : Polynomial R) (a₀ : R)
    (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a, f.IsRoot a ∧ a-a₀ ∈ I := by
  classical
    let f' := derivative f

    let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]

    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => ?_
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
      apply IsUnit.of_map (Ideal.Quotient.mk I)
      convert! h₂ using 1
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
      | succ n ih => ?_
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _

    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih => ?_
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add

    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ I
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁

variable {σ K R S : Type*} [Fintype σ] [DecidableEq σ] [Field K]
  [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

lemma aeval_hom {τ : Type*} (φ : R →ₐ[K] S) (x : τ → R) (F : MvPolynomial τ K) :
    φ (MvPolynomial.aeval x F) = MvPolynomial.aeval (fun i => φ (x i)) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => simp [hf]

noncomputable def liftZ (F : MvPolynomial (Option σ) K) :
    Polynomial (MvPowerSeries σ K) :=
  MvPolynomial.aeval (fun o => o.elim Polynomial.X
    (fun i => Polynomial.C (MvPowerSeries.X i))) F
omit [Fintype σ] [DecidableEq σ] in

lemma eval_liftZ (F : MvPolynomial (Option σ) K) (h : MvPowerSeries σ K) :
    (liftZ F).eval h = MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf => cases i <;> simp_all [liftZ]
omit [Fintype σ] in

lemma derivative_liftZ (F : MvPolynomial (Option σ) K) :
    (liftZ F).derivative = liftZ (MvPolynomial.pderiv none F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [liftZ,Polynomial.algebraMap_apply]
  | add f g hf hg => simp_all [liftZ]
  | mul_X f i hf =>
    cases i <;> simp_all [liftZ,Derivation.leibniz,smul_eq_mul,
      MvPolynomial.pderiv_X] <;> ring
omit [Fintype σ] [DecidableEq σ] in

lemma zeroCoeff_aeval (F : MvPolynomial (Option σ) K) :
    MvPowerSeries.constantCoeff
      (MvPolynomial.aeval (fun o => o.elim 0 MvPowerSeries.X) F) =
      MvPolynomial.constantCoeff F := by
  let φ : MvPowerSeries σ K →ₐ[K] K :=
    { MvPowerSeries.constantCoeff with
      commutes' := by intro c; simp [← MvPowerSeries.c_eq_algebraMap] }
  have H := aeval_hom φ (fun o => o.elim 0 MvPowerSeries.X) F
  have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
    funext o
    cases o with
    | none => exact map_zero φ
    | some i => change MvPowerSeries.constantCoeff (MvPowerSeries.X i) = 0; simp
  rw [hz,MvPolynomial.aeval_zero] at H
  exact H

theorem exists_formal_branch (F : MvPolynomial (Option σ) K)
    (hF : MvPolynomial.constantCoeff F = 0)
    (hD : MvPolynomial.constantCoeff (MvPolynomial.pderiv none F) ≠ 0) :
    ∃ h : MvPowerSeries σ K,
      MvPowerSeries.constantCoeff h = 0 ∧
      MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0 := by
  let I : Ideal (MvPowerSeries σ K) := Ideal.span (Set.range MvPowerSeries.X)
  have hmem : (liftZ F).eval 0 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,eval_liftZ]
    let φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K ⧸ I := Ideal.Quotient.mkₐ K I
    change φ _ = 0
    rw [aeval_hom]
    have hz : (fun o : Option σ => φ (o.elim 0 MvPowerSeries.X)) = 0 := by
      funext o
      cases o with
      | none => exact map_zero φ
      | some i =>
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    rw [hz,MvPolynomial.aeval_zero,hF,map_zero]
  have hu : IsUnit ((liftZ F).derivative.eval 0) := by
    rw [derivative_liftZ,eval_liftZ,MvPowerSeries.isUnit_iff_constantCoeff,
      zeroCoeff_aeval,isUnit_iff_ne_zero]
    exact hD
  let : IsAdicComplete I (MvPowerSeries σ K) :=
    inferInstanceAs (IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X))
      (MvPowerSeries σ K))
  obtain ⟨h,hr,hh⟩ := hensel_nonmonic I (liftZ F) 0 hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨h,?_,?_⟩
  · have hi : I ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := σ) (R := K)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simp
    apply hi
    simpa using hh
  · simpa [Polynomial.IsRoot,eval_liftZ] using hr

end SharpLogRamsey.ImplicitBranch

open Finset Finsupp
namespace SharpLogRamsey.FlatnessCore
variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
variable {p : ℕ} [CharP K p]

lemma cast_ne_zero_of_lt {n : ℕ} (hn : 0 < n) (hp : n < p) : (n : K) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff K p]
  exact fun h => (Nat.le_of_dvd hn h).not_gt hp
omit [Fintype σ] in

lemma coeff_deriv_predecessor (f : MvPowerSeries σ K) (d : σ →₀ ℕ) (i : σ)
    (hi : 0 < d i) :
    MvPowerSeries.coeff (d-single i 1) (MvPowerSeries.pderiv i f) =
      MvPowerSeries.coeff d f * (d i : K) := by
  have h : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  rw [MvPowerSeries.coeff_pderiv,tsub_add_cancel_of_le h,
    coe_tsub,Pi.sub_apply,single_eq_same,Nat.cast_sub (by omega),Nat.cast_one,sub_add_cancel]
omit [DecidableEq σ] in

lemma degree_pos_coordinate {d : σ →₀ ℕ} (hd : 0 < degree d) :
    ∃ i, 0 < d i := by
  by_contra! h
  have hz : d = 0 := by ext i; exact Nat.eq_zero_of_le_zero (h i)
  simp [hz] at hd
omit [Fintype σ] in

lemma coordinate_le_degree (d : σ →₀ ℕ) (i : σ) : d i ≤ degree d := by
  classical
  rw [degree_apply]
  by_cases hi : i ∈ d.support
  · exact single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp at hi
    simp [hi]

theorem coeff_zero_of_hessian_zero (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv i (MvPowerSeries.pderiv j h) = 0)
    (d : σ →₀ ℕ) (hd : 2 ≤ degree d) (hdp : degree d < p) :
    MvPowerSeries.coeff d h = 0 := by
  obtain ⟨i,hi⟩ := degree_pos_coordinate (d := d) (by omega)
  have hs : single i 1 ≤ d := by
    intro j
    by_cases he : i = j
    · subst j; simpa using (Nat.succ_le_iff.mpr hi)
    · simp [single_eq_of_ne (Ne.symm he)]
  let e := d-single i 1
  have hed : e + single i 1 = d := tsub_add_cancel_of_le hs
  have hedeg : degree e + 1 = degree d := by
    have := congrArg degree hed
    simpa using this
  obtain ⟨j,hj⟩ := degree_pos_coordinate (d := e) (by omega)
  have hc := coeff_deriv_predecessor (MvPowerSeries.pderiv i h) e j hj
  rw [hh j i,MvPowerSeries.coeff_zero] at hc
  have hej : (e j : K) ≠ 0 := cast_ne_zero_of_lt (p := p) hj
    (lt_of_le_of_lt (coordinate_le_degree e j) (by omega))
  have he0 : MvPowerSeries.coeff e (MvPowerSeries.pderiv i h) = 0 :=
    (mul_eq_zero.mp hc.symm).resolve_right hej
  have hc' := coeff_deriv_predecessor h d i hi
  change MvPowerSeries.coeff e (MvPowerSeries.pderiv i h) = _ at hc'
  rw [he0] at hc'
  exact (mul_eq_zero.mp hc'.symm).resolve_right
    (cast_ne_zero_of_lt (p := p) hi (lt_of_le_of_lt (coordinate_le_degree d i) hdp))

noncomputable def jetIdeal (n : ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  zero_mem' := by simp
  add_mem' := fun ha hb => (le_min ha hb).trans MvPowerSeries.min_order_le_add
  smul_mem' := by
    intro a f hf
    change (n : ℕ∞) ≤ (a*f).order
    exact hf.trans ((le_add_left le_rfl).trans MvPowerSeries.le_order_mul)
omit [Fintype σ] [DecidableEq σ] in

lemma mem_jetIdeal_iff (n : ℕ) (f : MvPowerSeries σ K) :
    f ∈ jetIdeal n ↔ ∀ d, degree d < n → MvPowerSeries.coeff d f = 0 := by
  constructor
  · intro h d hd
    exact MvPowerSeries.coeff_of_lt_order
      ((show ((degree d : ℕ) : ℕ∞) < n by exact_mod_cast hd).trans_le h)
  · exact MvPowerSeries.nat_le_order

theorem hessian_zero_affine_jet (h : MvPowerSeries σ K)
    (hh : ∀ i j, MvPowerSeries.pderiv i (MvPowerSeries.pderiv j h) = 0) :
    h - (MvPowerSeries.truncTotal 2 h : MvPolynomial σ K).toMvPowerSeries ∈ jetIdeal p := by
  rw [mem_jetIdeal_iff]
  intro d hdp
  rw [map_sub,MvPolynomial.coeff_coe]
  by_cases hd : degree d < 2
  · rw [MvPowerSeries.coeff_truncTotal _ hd,sub_self]
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega),sub_zero]
    exact coeff_zero_of_hessian_zero h hh d (by omega) hdp

variable {τ R : Type*} [CommRing R] [Algebra K R]

lemma aeval_sub_mem (I : Ideal R) (x y : τ → R)
    (hxy : ∀ i, x i-y i ∈ I) (F : MvPolynomial τ K) :
    MvPolynomial.aeval x F-MvPolynomial.aeval y F ∈ I := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simpa only [map_add,add_sub_add_comm] using I.add_mem hf hg
  | mul_X f i hf =>
    simpa only [map_mul,MvPolynomial.aeval_X,
      show MvPolynomial.aeval x f*x i-MvPolynomial.aeval y f*y i =
        x i*(MvPolynomial.aeval x f-MvPolynomial.aeval y f)+
          MvPolynomial.aeval y f*(x i-y i) from by ring] using
      I.add_mem (I.mul_mem_left (x i) hf) (I.mul_mem_left _ (hxy i))

variable [Fintype τ] [DecidableEq τ]

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma totalDegree_aeval_linear (x : τ → MvPolynomial σ K)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).totalDegree ≤ F.totalDegree := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  apply le_trans (MvPolynomial.totalDegree_mul _ _)
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C,zero_add]
  calc
    _ ≤ ∑ i ∈ d.support, (x i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      apply (MvPolynomial.totalDegree_pow _ _).trans
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right (d i) (hx i)
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hd
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in

lemma toSeries_aeval (x : τ → MvPolynomial σ K) (F : MvPolynomial τ K) :
    (MvPolynomial.aeval x F).toMvPowerSeries =
      MvPolynomial.aeval (fun i => (x i).toMvPowerSeries) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [← MvPowerSeries.c_eq_algebraMap]
  | add f g hf hg => simp only [map_add,MvPolynomial.coe_add,hf,hg]
  | mul_X f i hf => simp only [map_mul,MvPolynomial.coe_mul,MvPolynomial.aeval_X,hf]

omit [Fintype σ] in

lemma polynomial_eq_zero_of_jet {F : MvPolynomial σ K} {n : ℕ}
    (hF : F.totalDegree < n) (h : F.toMvPowerSeries ∈ jetIdeal n) : F = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases hd : d ∈ F.support
  · have hle := MvPolynomial.le_totalDegree hd
    have hc := (mem_jetIdeal_iff n F.toMvPowerSeries).mp h d (lt_of_le_of_lt hle hF)
    simpa using hc
  · exact MvPolynomial.notMem_support_iff.mp hd

theorem flat_branch_zero_plane (F : MvPolynomial (Option σ) K)
    (hF : F.totalDegree < p) (h : MvPowerSeries σ K)
    (hroot : MvPolynomial.aeval (fun o => o.elim h MvPowerSeries.X) F = 0)
    (hh : ∀ i j, MvPowerSeries.pderiv i (MvPowerSeries.pderiv j h) = 0) :
    MvPolynomial.aeval (fun o => o.elim (MvPowerSeries.truncTotal 2 h) MvPolynomial.X) F = 0 := by
  let lin := MvPowerSeries.truncTotal 2 h
  let x : Option σ → MvPolynomial σ K := fun o => o.elim lin MvPolynomial.X
  have hx : ∀ i, (x i).totalDegree ≤ 1 := by
    intro i
    cases i with
    | none =>
      have H := MvPowerSeries.totalDegree_truncTotal_lt h (by norm_num : (2:ℕ) ≠ 0)
      change lin.totalDegree ≤ 1
      dsimp [lin]
      omega
    | some i => exact (MvPolynomial.totalDegree_X (R := K) i).le
  apply polynomial_eq_zero_of_jet (n := p)
  · exact (totalDegree_aeval_linear x hx F).trans_lt hF
  · have H := aeval_sub_mem (jetIdeal p)
      (fun o => o.elim h MvPowerSeries.X) (fun i => (x i).toMvPowerSeries) (fun i => ?_) F
    · rw [hroot,zero_sub] at H
      rw [toSeries_aeval]
      exact neg_mem_iff.mp H
    cases i with
    | none => exact hessian_zero_affine_jet h hh
    | some i => simp [x]

lemma deriv_aeval (D : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (MvPolynomial.aeval x F) =
      ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i F) * D (x i) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    simp only [map_mul,MvPolynomial.aeval_X,Derivation.leibniz,smul_eq_mul,
      map_add,MvPolynomial.pderiv_X]
    simp only [
      add_mul,Finset.sum_add_distrib]
    rw [hf,Finset.mul_sum]
    congr 1
    · simp [Pi.single_apply]
    · apply Finset.sum_congr rfl
      intro i hi
      ring

lemma deriv2_aeval (D E : Derivation K R R) (x : τ → R) (F : MvPolynomial τ K) :
    D (E (MvPolynomial.aeval x F)) =
      (∑ j, ∑ i, MvPolynomial.aeval x (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j F)) * D (x i) * E (x j)) +
      ∑ j, MvPolynomial.aeval x (MvPolynomial.pderiv j F) * D (E (x j)) := by
  rw [deriv_aeval E,map_sum]
  simp only [Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [deriv_aeval D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def branchPoint (h : MvPowerSeries σ K) : Option σ → MvPowerSeries σ K :=
  fun o => o.elim h MvPowerSeries.X

noncomputable def branchTangent (h : MvPowerSeries σ K) (a : σ) :
    Option σ → MvPowerSeries σ K := fun o => MvPowerSeries.pderiv a (branchPoint h o)

lemma branch_second_sum (h : MvPowerSeries σ K) (g : Option σ → MvPowerSeries σ K)
    (a b : σ) :
    (∑ j, g j * MvPowerSeries.pderiv a
      (MvPowerSeries.pderiv b (branchPoint h j))) =
    g none * MvPowerSeries.pderiv a (MvPowerSeries.pderiv b h) := by
  rw [Fintype.sum_option]
  simp [branchPoint,MvPowerSeries.pderiv_X,Pi.single_apply,apply_ite]

end SharpLogRamsey.FlatnessCore
end
end
end

end OAI
