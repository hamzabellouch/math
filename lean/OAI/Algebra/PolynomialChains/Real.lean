import Mathlib

namespace OAI

/-! Real weighted chains and pure-power squarefreeness. -/



namespace MultiplicityCounterexample
noncomputable section

abbrev ComplexAffine (N : ℕ) := Fin N → ℂ
abbrev RealPolynomial (N : ℕ) := MvPolynomial (Fin N) ℝ

def complexEval {N : ℕ} (f : RealPolynomial N) (z : ComplexAffine N) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ) z f

def hypersurface {N : ℕ} (f : RealPolynomial N) : Set (ComplexAffine N) :=
  {z | complexEval f z = 0}

def IsReduced {N : ℕ} (f : RealPolynomial N) : Prop :=
  Squarefree (MvPolynomial.map (algebraMap ℝ ℂ) f)

def orderAtOrigin {N : ℕ} (f : RealPolynomial N) : WithTop ℕ :=
  f.support.inf fun m => ((m.sum fun _ e => e : ℕ) : WithTop ℕ)

def IsPositivelyWeightedHomogeneous {N : ℕ} (f : RealPolynomial N) : Prop :=
  ∃ (a : Fin N → ℕ) (d : ℕ),
    0 < d ∧ (∀ i, 0 < a i) ∧
    ∀ (t : ℂ) (z : ComplexAffine N),
      complexEval f (fun i => t ^ a i * z i) = t ^ d * complexEval f z

def IsCriticalPoint {N : ℕ} (f : RealPolynomial N) (z : ComplexAffine N) : Prop :=
  ∀ i : Fin N, complexEval (MvPolynomial.pderiv i f) z = 0

def HasIsolatedCriticalPointAtOrigin {N : ℕ} (f : RealPolynomial N) : Prop :=
  IsCriticalPoint f 0 ∧
    ∃ U : Set (ComplexAffine N), IsOpen U ∧ (0 : ComplexAffine N) ∈ U ∧
      ∀ z ∈ U, IsCriticalPoint f z → z = 0

def AmbientlyHomeomorphicAtOrigin {N : ℕ} (f g : RealPolynomial N) : Prop :=
  ∃ U V : Set (ComplexAffine N), IsOpen U ∧ IsOpen V ∧
    ∃ (hU : (0 : ComplexAffine N) ∈ U) (hV : (0 : ComplexAffine N) ∈ V)
      (h : U ≃ₜ V),
      h ⟨0, hU⟩ = ⟨0, hV⟩ ∧
      ∀ z : U, (z : ComplexAffine N) ∈ hypersurface f ↔
        (h z : ComplexAffine N) ∈ hypersurface g

end
end MultiplicityCounterexample

namespace MultiplicityCounterexample.Chains
noncomputable section
open MvPolynomial
open scoped BigOperators

def polynomial {n : ℕ} (R : Type*) [CommSemiring R] (a : Fin (n + 1) → ℕ) :
    MvPolynomial (Fin (n + 1)) R :=
  (∑ i : Fin n, X i.castSucc ^ a i.castSucc * X i.succ) +
    X (Fin.last n) ^ a (Fin.last n)

@[simp] lemma map_polynomial {n : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S) (a : Fin (n + 1) → ℕ) :
    map φ (polynomial R a) = polynomial S a := by
  classical
  simp [polynomial]

lemma tail_decomposition {n : ℕ} (R : Type*) [CommSemiring R]
    (a : Fin (n + 2) → ℕ) :
    polynomial R a = X 0 ^ a 0 * X (Fin.succ 0) +
      rename Fin.succ (polynomial R (fun i : Fin (n + 1) => a i.succ)) := by
  classical
  simp only [polynomial, map_add, map_sum, map_mul, map_pow, rename_X,
    Fin.sum_univ_succ, Fin.castSucc_zero, Fin.castSucc_succ]
  simp only [add_assoc, Fin.succ_last]

variable {n : ℕ} {K : Type*} [Field K]

def next (z : Fin (n + 1) → K) : Fin (n + 1) → K :=
  Fin.snoc (fun i : Fin n => z i.succ) 1

def previous (a : Fin (n + 1) → ℕ) (z : Fin (n + 1) → K) : Fin (n + 1) → K :=
  Fin.cons 0 (fun i : Fin n => z i.castSucc ^ a i.castSucc)

@[simp] lemma next_castSucc (z : Fin (n + 1) → K) (i : Fin n) :
    next z i.castSucc = z i.succ := by simp [next]
@[simp] lemma next_last (z : Fin (n + 1) → K) :
    next z (Fin.last n) = 1 := by simp [next]
@[simp] lemma previous_zero (a : Fin (n + 1) → ℕ) (z : Fin (n + 1) → K) :
    previous a z 0 = 0 := by simp [previous]
@[simp] lemma previous_succ (a : Fin (n + 1) → ℕ) (z : Fin (n + 1) → K)
    (i : Fin n) : previous a z i.succ = z i.castSucc ^ a i.castSucc := by
  simp [previous]

lemma eval_pderiv (a : Fin (n + 1) → ℕ) (z : Fin (n + 1) → K)
    (j : Fin (n + 1)) :
    eval z (pderiv j (polynomial K a)) =
      (a j : K) * z j ^ (a j - 1) * next z j + previous a z j := by
  classical
  have own :
      (∑ i : Fin n, if i.castSucc = j then
        (a i.castSucc : K) * z i.castSucc ^ (a i.castSucc - 1) * z i.succ else 0) +
      (if Fin.last n = j then
        (a (Fin.last n) : K) * z (Fin.last n) ^ (a (Fin.last n) - 1) else 0) =
      (a j : K) * z j ^ (a j - 1) * next z j := by
    have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin (n + 1))) j
      (fun i => (a i : K) * z i ^ (a i - 1) * next z i)
    simpa only [Finset.mem_univ, ite_true, Fin.sum_univ_castSucc,
      next_castSucc, next_last, mul_one] using h
  have prev :
      (∑ i : Fin n, if i.succ = j then z i.castSucc ^ a i.castSucc else 0) =
        previous a z j := by
    have h := Finset.sum_ite_eq' (Finset.univ : Finset (Fin (n + 1))) j
      (previous a z)
    simpa only [Finset.mem_univ, ite_true, Fin.sum_univ_succ,
      previous_zero, ite_self, zero_add, previous_succ] using h
  calc
    eval z (pderiv j (polynomial K a)) =
        (∑ i : Fin n, ((if i.castSucc = j then
          (a i.castSucc : K) * z i.castSucc ^ (a i.castSucc - 1) * z i.succ else 0) +
          (if i.succ = j then z i.castSucc ^ a i.castSucc else 0))) +
        (if Fin.last n = j then
          (a (Fin.last n) : K) * z (Fin.last n) ^ (a (Fin.last n) - 1) else 0) := by
      simp only [polynomial, map_add, map_sum, pderiv_mul, pderiv_pow, pderiv_X,
        eval_mul, eval_pow, map_natCast, eval_X]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        by_cases h : i.castSucc = j <;> by_cases h' : i.succ = j <;>
          simp [h, h']
      · by_cases h : Fin.last n = j <;> simp [h]
    _ = _ := by rw [Finset.sum_add_distrib]; rw [add_right_comm, own, prev]

lemma previous_eq_zero_of_first (a : Fin (n + 1) → ℕ)
    (ha : ∀ i, 0 < a i) (z : Fin (n + 1) → K) (j : Fin (n + 1))
    (hz : ∀ i < j, z i = 0) : previous a z j = 0 := by
  revert hz
  refine Fin.cases ?_ ?_ j
  · intro _
    exact previous_zero a z
  · intro i hz
    rw [previous_succ, hz i.castSucc Fin.castSucc_lt_succ,
      zero_pow (ha i.castSucc).ne']

section Critical
variable [CharZero K]

theorem critical_locus (a : Fin (n + 1) → ℕ) (ha : ∀ i, 2 ≤ a i)
    (z : Fin (n + 1) → K) :
    (∀ j, eval z (pderiv j (polynomial K a)) = 0) ↔ z = 0 := by
  classical
  constructor
  · intro hz
    by_contra hne
    have hex : ∃ j, z j ≠ 0 := by
      by_contra hn
      apply hne
      funext j
      simpa using not_exists.mp hn j
    let j := Fin.find (fun j => z j ≠ 0) hex
    have hj : z j ≠ 0 := Fin.find_spec hex
    have hfirst : ∀ i < j, z i = 0 := by
      intro i hi
      exact not_not.mp (Fin.find_min hex hi)
    have hprev : previous a z j = 0 :=
      previous_eq_zero_of_first a (fun i => lt_of_lt_of_le (by decide) (ha i)) z j hfirst
    have hnext : next z j = 0 := by
      have hpow : (a j : K) * z j ^ (a j - 1) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr (by have := ha j; omega)) (pow_ne_zero _ hj)
      have h := hz j
      rw [eval_pderiv, hprev, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hpow
    have hjlast : j ≠ Fin.last n := by
      intro h
      rw [h, next_last] at hnext
      exact one_ne_zero hnext
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hjlast
    have hznext : z i.succ = 0 := by simpa only [← hi, next_castSucc] using hnext
    have hcrit := hz i.succ
    have hapos : a i.succ - 1 ≠ 0 := by have := ha i.succ; omega
    rw [eval_pderiv, hznext, zero_pow hapos, mul_zero, zero_mul, zero_add,
      previous_succ] at hcrit
    exact pow_ne_zero _ (hi ▸ hj) hcrit
  · rintro rfl j
    have hn : a j - 1 ≠ 0 := by have := ha j; omega
    rw [eval_pderiv]
    simp only [Pi.zero_apply, zero_pow hn, mul_zero, zero_mul, zero_add]
    apply previous_eq_zero_of_first a (fun i => lt_of_lt_of_le (by decide) (ha i))
    intro _ _
    rfl

end Critical

lemma eval_scale (a w : Fin (n + 1) → ℕ) (D : ℕ)
    (hw : ∀ i : Fin n, a i.castSucc * w i.castSucc + w i.succ = D)
    (hlast : a (Fin.last n) * w (Fin.last n) = D) (t : K)
    (z : Fin (n + 1) → K) :
    eval (fun i => t ^ w i * z i) (polynomial K a) =
      t ^ D * eval z (polynomial K a) := by
  classical
  simp only [polynomial, eval_add, eval_sum, eval_mul, eval_pow, eval_X]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, ← pow_mul, Nat.mul_comm (w i.castSucc) (a i.castSucc),
      ← hw i, pow_add]
    ring
  · rw [mul_pow, ← pow_mul, Nat.mul_comm (w (Fin.last n)) (a (Fin.last n)), hlast]

lemma monomial_degrees (a : Fin (n + 1) → ℕ) (ha : ∀ i, 2 ≤ a i)
    (hlast : 3 ≤ a (Fin.last n)) (m : Fin (n + 1) →₀ ℕ)
    (hm : m ∈ (polynomial K a).support) : 3 ≤ m.sum (fun _ e => e) := by
  classical
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (support_sum hm)
    have h : a i.castSucc + 1 = m.sum (fun _ e => e) :=
      ((isHomogeneous_X_pow i.castSucc (a i.castSucc)).mul
        (isHomogeneous_X K i.succ)).degree_eq_sum_deg_support hi
    have := ha i.castSucc
    omega
  · have h : a (Fin.last n) = m.sum (fun _ e => e) :=
      (isHomogeneous_X_pow (Fin.last n) (a (Fin.last n))).degree_eq_sum_deg_support hm
    omega

theorem exists_chain_data (D c : ℕ) (hc : 0 < c) (hD : 2 * c < D) :
    ∃ (n : ℕ) (a w : Fin (n + 1) → ℕ),
      w 0 = c ∧
      (∀ i, 0 < w i ∧ 2 * w i < D ∧ 2 ≤ a i) ∧
      3 ≤ a (Fin.last n) ∧
      (∀ i : Fin n, a i.castSucc * w i.castSucc + w i.succ = D) ∧
      a (Fin.last n) * w (Fin.last n) = D := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    have hq : 2 ≤ D / c := (Nat.le_div_iff_mul_le hc).2 (by omega)
    have hdiv : D / c * c + D % c = D := by
      simpa only [Nat.mul_comm c (D / c)] using Nat.div_add_mod D c
    by_cases hr : D % c = 0
    · refine ⟨0, fun _ => D / c, fun _ => c, rfl,
        (fun _ => ⟨hc, hD, hq⟩), ?_, (fun i => Fin.elim0 i), ?_⟩
      · simp only at *
        nlinarith
      · simpa only [hr, add_zero] using hdiv
    · have hrc : D % c < c := Nat.mod_lt D hc
      have hrpos : 0 < D % c := Nat.pos_of_ne_zero hr
      have hrD : 2 * (D % c) < D := by omega
      obtain ⟨n, a, w, hw0, hw, ha, heq, hlast⟩ := ih (D % c) hrc hrpos hrD
      refine ⟨n + 1, Fin.cons (D / c) a, Fin.cons c w, rfl, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · exact ⟨hc, hD, hq⟩
        · simpa only [Fin.cons_succ] using hw i
      · simpa using ha
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hw0] using hdiv
        · simpa only [Fin.castSucc_succ, Fin.cons_succ] using heq i
      · simpa using hlast

end
end MultiplicityCounterexample.Chains

namespace MultiplicityCounterexample
noncomputable section
open MvPolynomial

lemma complexEval_chain {n : ℕ} (a : Fin (n + 1) → ℕ)
    (z : ComplexAffine (n + 1)) :
    complexEval (Chains.polynomial ℝ a) z = eval z (Chains.polynomial ℂ a) := by
  rw [complexEval, ← eval_map, Chains.map_polynomial]

lemma complexEval_pderiv_chain {n : ℕ} (a : Fin (n + 1) → ℕ)
    (i : Fin (n + 1)) (z : ComplexAffine (n + 1)) :
    complexEval (pderiv i (Chains.polynomial ℝ a)) z =
      eval z (pderiv i (Chains.polynomial ℂ a)) := by
  rw [complexEval, ← eval_map, ← pderiv_map, Chains.map_polynomial]

theorem real_chain_critical_iff {n : ℕ} (a : Fin (n + 1) → ℕ)
    (ha : ∀ i, 2 ≤ a i) (z : ComplexAffine (n + 1)) :
    IsCriticalPoint (Chains.polynomial ℝ a) z ↔ z = 0 := by
  simp only [IsCriticalPoint, complexEval_pderiv_chain]
  exact Chains.critical_locus a ha z

theorem real_chain_isolated {n : ℕ} (a : Fin (n + 1) → ℕ) (ha : ∀ i, 2 ≤ a i) :
    HasIsolatedCriticalPointAtOrigin (Chains.polynomial ℝ a) := by
  refine ⟨(real_chain_critical_iff a ha 0).2 rfl, Set.univ, isOpen_univ,
    Set.mem_univ _, ?_⟩
  intro z _ hz
  exact (real_chain_critical_iff a ha z).1 hz

theorem real_chain_weighted {n : ℕ} (a w : Fin (n + 1) → ℕ) (D : ℕ)
    (hD : 0 < D) (hwpos : ∀ i, 0 < w i)
    (hw : ∀ i : Fin n, a i.castSucc * w i.castSucc + w i.succ = D)
    (ht : a (Fin.last n) * w (Fin.last n) = D) :
    IsPositivelyWeightedHomogeneous (Chains.polynomial ℝ a) := by
  refine ⟨w, D, hD, hwpos, ?_⟩
  intro t z
  simp only [complexEval_chain]
  exact Chains.eval_scale a w D hw ht t z

theorem real_chain_order_ge_three {n : ℕ} (a : Fin (n + 1) → ℕ)
    (ha : ∀ i, 2 ≤ a i) (ht : 3 ≤ a (Fin.last n)) :
    3 ≤ orderAtOrigin (Chains.polynomial ℝ a) := by
  apply Finset.le_inf
  intro m hm
  exact_mod_cast Chains.monomial_degrees a ha ht m hm

theorem exists_real_chain (D c : ℕ) (hc : 0 < c) (hD : 2 * c < D) :
    ∃ (n : ℕ) (a w : Fin (n + 1) → ℕ),
      w 0 = c ∧
      (∀ i, 0 < (w i : ℚ) / D ∧ (w i : ℚ) / D < 1 / 2) ∧
      (∀ (t : ℂ) (z : ComplexAffine (n + 1)),
        complexEval (Chains.polynomial ℝ a) (fun i => t ^ w i * z i) =
          t ^ D * complexEval (Chains.polynomial ℝ a) z) ∧
      IsPositivelyWeightedHomogeneous (Chains.polynomial ℝ a) ∧
      (∀ m ∈ (Chains.polynomial ℝ a).support, 3 ≤ m.sum (fun _ e => e)) ∧
      3 ≤ orderAtOrigin (Chains.polynomial ℝ a) ∧
      HasIsolatedCriticalPointAtOrigin (Chains.polynomial ℝ a) := by
  obtain ⟨n, a, w, hw0, hw, ha, hrel, ht⟩ := Chains.exists_chain_data D c hc hD
  have hDpos : 0 < D := by omega
  have ha2 : ∀ i, 2 ≤ a i := fun i => (hw i).2.2
  refine ⟨n, a, w, hw0, ?_, ?_, real_chain_weighted a w D hDpos
    (fun i => (hw i).1) hrel ht, ?_, real_chain_order_ge_three a ha2 ha,
    real_chain_isolated a ha2⟩
  · intro i
    have hpos : (0 : ℚ) < D := by exact_mod_cast hDpos
    constructor
    · exact div_pos (by exact_mod_cast (hw i).1) hpos
    · apply (div_lt_iff₀ hpos).2
      have hlt : (2 : ℚ) * w i < D := by exact_mod_cast (hw i).2.1
      linarith
  · intro t z
    simp only [complexEval_chain]
    exact Chains.eval_scale a w D hrel ht t z
  · intro m hm
    exact Chains.monomial_degrees a ha2 ha m hm

end
end MultiplicityCounterexample

namespace MultiplicityCounterexample
noncomputable section
open MvPolynomial

variable {σ K : Type*} [Field K]

lemma squarefree_of_pderiv_power (f : MvPolynomial σ K) (i : σ) (m : ℕ)
    (c : K) (hc : c ≠ 0) (hd : pderiv i f = C c * X i ^ m)
    (hX : ¬ (X i : MvPolynomial σ K) ∣ f) : Squarefree f := by
  classical
  have hrel : IsRelPrime f (X i) :=
    ((X_prime (R := K) (i := i)).irreducible.isRelPrime_iff_not_dvd.2 hX).symm
  intro g hg
  have hgf : g ∣ f := dvd_trans (dvd_mul_right g g) hg
  obtain ⟨b, hb⟩ := hg
  have hgd : g ∣ pderiv i f := by
    refine ⟨2 * pderiv i g * b + g * pderiv i b, ?_⟩
    rw [hb]
    simp only [pderiv_mul]
    ring
  rw [hd] at hgd
  have hunit : IsUnit (C c : MvPolynomial σ K) :=
    IsUnit.map C (isUnit_iff_ne_zero.2 hc)
  exact hrel.pow_right hgf (hunit.dvd_mul_left.1 hgd)

lemma squarefree_add_pure_power [CharZero K] (g : MvPolynomial σ K)
    (i : σ) (r : ℕ) (hr : 0 < r) (hg : pderiv i g = 0)
    (z : σ → K) (hzi : z i = 0) (hgz : eval z g ≠ 0) :
    Squarefree (g + X i ^ r) := by
  classical
  apply squarefree_of_pderiv_power (g + X i ^ r) i (r - 1) (r : K)
    (Nat.cast_ne_zero.2 hr.ne')
  · simp [hg]
  · intro hdvd
    have hh := map_dvd (eval z) hdvd
    simp only [eval_X, hzi, eval_add, eval_pow, zero_pow hr.ne', add_zero,
      zero_dvd_iff] at hh
    exact hgz hh

end
end MultiplicityCounterexample

namespace MultiplicityCounterexample
noncomputable section
open MvPolynomial

theorem isReduced_add_pure_power {N : ℕ} (g : RealPolynomial N)
    (i : Fin N) (r : ℕ) (hr : 0 < r) (hg : pderiv i g = 0)
    (z : ComplexAffine N) (hzi : z i = 0) (hgz : complexEval g z ≠ 0) :
    IsReduced (g + X i ^ r) := by
  unfold IsReduced
  rw [map_add, map_pow, map_X]
  refine squarefree_add_pure_power _ i r hr ?_ z hzi ?_
  · rw [pderiv_map, hg, map_zero]
  · rwa [eval_map]

end
end MultiplicityCounterexample

end OAI
