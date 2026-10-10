import Mathlib

namespace OAI

/-! Finite-dimensional analytic inversion and convergent preparation of polynomial graph equations. -/

namespace AmbientMultiplicity.Preparation
noncomputable section
open Filter
open scoped Topology

abbrev V (n : ℕ) := Fin n → ℂ
abbrev proj {n : ℕ} (i : Fin n) : V n →L[ℂ] ℂ := ContinuousLinearMap.proj i

def high {n : ℕ} (k : ℕ) (x : V n) (j : ℕ) : ℂ :=
  if h : k + j < n then x ⟨k + j, h⟩ else 0

def highL {n : ℕ} (k j : ℕ) : V n →L[ℂ] ℂ :=
  if h : k + j < n then proj ⟨k + j, h⟩ else 0

lemma highL_apply {n : ℕ} (k j : ℕ) (x : V n) : highL k j x = high k x j := by
  unfold highL high
  split <;> rfl

 

def polyMap {n k : ℕ} (hk : k < n) (x : V n) : V n := fun i =>
  (if k ≤ (i : ℕ) then x i else 0) +
    ∑ j : Fin k, if (j : ℕ) ≤ i then x ⟨j, lt_trans j.isLt hk⟩ * high k x (i - j) else 0

def tangent {n k : ℕ} (hk : k < n) (x₀ : V n) : V n →L[ℂ] V n :=
  ContinuousLinearMap.pi fun i =>
    (if k ≤ (i : ℕ) then proj i else 0) +
      ∑ j : Fin k, if (j : ℕ) ≤ i then high k x₀ (i - j) • proj ⟨j, lt_trans j.isLt hk⟩ else 0

lemma tangent_apply {n k : ℕ} (hk : k < n) (x₀ x : V n) (i : Fin n) :
    tangent hk x₀ x i = (if k ≤ (i : ℕ) then x i else 0) +
      ∑ j : Fin k, if (j : ℕ) ≤ i then high k x₀ (i - j) * x ⟨j, lt_trans j.isLt hk⟩ else 0 := by
  simp only [tangent, ContinuousLinearMap.pi_apply, add_apply, sum_apply]
  congr 1
  · split <;> rfl
  · apply Finset.sum_congr rfl
    intro j hj
    split <;> rfl

lemma high_strict {n : ℕ} (k j : ℕ) (x : V n) :
    HasStrictFDerivAt (fun y => high k y j) (highL k j) x := by
  unfold high highL
  split
  · exact (proj _).hasStrictFDerivAt
  · exact hasStrictFDerivAt_const 0 x

lemma polyMap_strict {n k : ℕ} (hk : k < n) (x₀ : V n)
    (hzero : ∀ j : Fin k, x₀ ⟨j, lt_trans j.isLt hk⟩ = 0) :
    HasStrictFDerivAt (polyMap hk) (tangent hk x₀) x₀ := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  apply HasStrictFDerivAt.add
  · split
    · exact (proj _).hasStrictFDerivAt
    · exact hasStrictFDerivAt_const 0 x₀
  · apply HasStrictFDerivAt.fun_sum
    intro j hj
    split
    · convert! ((proj ⟨j, lt_trans j.isLt hk⟩).hasStrictFDerivAt (x := x₀)).fun_mul
          (high_strict k (i - j) x₀) using 1
      ext v
      simp [hzero j]
    · exact hasStrictFDerivAt_const 0 x₀

lemma polyMap_analytic {n k : ℕ} (hk : k < n) (x : V n) :
    AnalyticAt ℂ (polyMap hk) x := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.add
  · split
    · exact (proj i).analyticAt x
    · exact analyticAt_const
  · apply Finset.analyticAt_fun_sum
    intro j hj
    split
    · apply AnalyticAt.mul ((proj _).analyticAt x)
      unfold high
      split
      · exact (proj _).analyticAt x
      · exact analyticAt_const
    · exact analyticAt_const

 

lemma tangent_injective {n k : ℕ} (hk : k < n) (x₀ : V n)
    (hone : x₀ ⟨k, hk⟩ = 1) : Function.Injective (tangent hk x₀) := by
  apply (tangent hk x₀).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hx' : ∀ i : Fin n, tangent hk x₀ x i = 0 := fun i => congrFun hx i
  have hz : ∀ t : ℕ, ∀ ht : t < n, x ⟨t, ht⟩ = 0 := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      have he := hx' ⟨t, ht⟩
      rw [tangent_apply] at he
      by_cases hkt : k ≤ t
      · rw [ite_eq_left hkt] at he
        have hs : (∑ j : Fin k, if (j : ℕ) ≤ t then
            high k x₀ (t - j) * x ⟨j, lt_trans j.isLt hk⟩ else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [ih j (lt_of_lt_of_le j.isLt hkt)]
          simp
        simpa [hs] using he
      · have htk : t < k := by omega
        rw [ite_eq_right hkt] at he
        have hs : (∑ j : Fin k, if (j : ℕ) ≤ t then
            high k x₀ (t - j) * x ⟨j, lt_trans j.isLt hk⟩ else 0) = x ⟨t, ht⟩ := by
          rw [Finset.sum_eq_single (⟨t, htk⟩ : Fin k)]
          · simp [high, hk, hone]
          · intro j hj hne
            by_cases hjt : (j : ℕ) ≤ t
            · have hjt' : (j : ℕ) < t := by
                have hn : (j : ℕ) ≠ t := fun h => hne (Fin.ext h)
                omega
              simp [hjt, ih j hjt']
            · simp [hjt]
          · simp
        simpa [hs] using he
  ext i
  exact hz i i.isLt

 
lemma analytic_inverse {n : ℕ} {f : V n → V n} {x : V n}
    (e : V n ≃L[ℂ] V n) (hf : AnalyticAt ℂ f x)
    (hd : HasStrictFDerivAt f e.toContinuousLinearMap x) :
    ∃ g : V n → V n, AnalyticAt ℂ g (f x) ∧ g (f x) = x ∧
      ∀ᶠ y in 𝓝 (f x), f (g y) = y := by
  let R := hd.toOpenPartialHomeomorph f
  have hx : x ∈ R.source := hd.mem_toOpenPartialHomeomorph_source
  obtain ⟨p, hp⟩ := hf
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (V n) (V n)).symm e.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ (V n) (V n)).injective
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hp.hasFDerivAt.unique hd.hasFDerivAt
  have hg : AnalyticAt ℂ R.symm (f x) :=
    (R.hasFPowerSeriesAt_symm hx hp hp1).analyticAt
  exact ⟨R.symm, hg, R.left_inv hx, R.eventually_right_inverse' hx⟩

 

theorem factor_coordinates {n k : ℕ} (hk : k < n) (x₀ : V n)
    (hzero : ∀ j : Fin k, x₀ ⟨j, lt_trans j.isLt hk⟩ = 0)
    (hone : x₀ ⟨k, hk⟩ = 1) :
    ∃ g : V n → V n, AnalyticAt ℂ g (polyMap hk x₀) ∧
      g (polyMap hk x₀) = x₀ ∧
      ∀ᶠ y in 𝓝 (polyMap hk x₀), polyMap hk (g y) = y := by
  let e : V n ≃L[ℂ] V n :=
    (LinearEquiv.ofInjectiveEndo (tangent hk x₀).toLinearMap
      (tangent_injective hk x₀ hone)).toContinuousLinearEquiv
  exact analytic_inverse e (polyMap_analytic hk x₀) (polyMap_strict hk x₀ hzero)

open Polynomial

def lowPoly {n k : ℕ} (hk : k < n) (x : V n) : Polynomial ℂ :=
  ofFn k (fun j => x ⟨j, lt_trans j.isLt hk⟩)

def highPoly {n k : ℕ} (hk : k < n) (x : V n) : Polynomial ℂ :=
  ofFn (n-k) (fun j => x ⟨k+j, by omega⟩)

def rootPoly {n k : ℕ} (hk : k < n) (x : V n) : Polynomial ℂ :=
  X^k + lowPoly hk x

lemma coeff_highPoly {n k : ℕ} (hk : k < n) (x : V n) (i : ℕ) :
    (highPoly hk x).coeff i = high k x i := by
  unfold highPoly high
  by_cases hi : i < n-k
  · rw [ofFn_coeff_eq_val_of_lt _ hi, dite_eq_left (by omega)]
  · rw [ofFn_coeff_eq_zero_of_ge _ (by omega), dite_eq_right (by omega)]

lemma coeff_monomial_mul_any (p : Polynomial ℂ) (i j : ℕ) (c : ℂ) :
    (monomial j c * p).coeff i = if j ≤ i then c * p.coeff (i-j) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split <;> simp_all

lemma coeff_factor {n k : ℕ} (hk : k < n) (x : V n) (i : Fin n) :
    (rootPoly hk x * highPoly hk x).coeff i = polyMap hk x i := by
  rw [rootPoly, add_mul, coeff_add, coeff_X_pow_mul', lowPoly,
    ofFn_eq_sum_monomial, Finset.sum_mul, finsetSum_coeff]
  simp_rw [coeff_monomial_mul_any, coeff_highPoly]
  unfold polyMap
  congr 1
  split
  · rename_i h
    simp [high, show k + (i-k) = i by omega, i.isLt]
  · rfl

lemma factor_natDegree_lt {n k : ℕ} (hk : k < n) (x : V n) :
    (rootPoly hk x * highPoly hk x).natDegree < n := by
  have hr : (rootPoly hk x).natDegree ≤ k := by
    exact (natDegree_add_le _ _).trans (max_le (by simp) (by
      by_cases h : k = 0
      · subst k; simp [lowPoly]
      · exact (ofFn_natDegree_lt (by omega) _).le))
  have hu : (highPoly hk x).natDegree < n-k := ofFn_natDegree_lt (by omega) _
  have hd := natDegree_mul_le (p := rootPoly hk x) (q := highPoly hk x)
  omega

lemma factor_eq_ofFn {n k : ℕ} (hk : k < n) (x : V n) :
    rootPoly hk x * highPoly hk x = ofFn n (polyMap hk x) := by
  have ht : toFn n (rootPoly hk x * highPoly hk x) = polyMap hk x := by
    ext i
    exact coeff_factor hk x i
  rw [← ht, ofFn_comp_toFn_eq_id_of_natDegree_lt (factor_natDegree_lt hk x)]

 
def CoeffAnalytic {m : ℕ} (f : V m → Polynomial ℂ) : Prop :=
  ∀ i, AnalyticAt ℂ (fun p => (f p).coeff i) 0

lemma coeffAnalytic_const {m : ℕ} (q : Polynomial ℂ) :
    CoeffAnalytic (fun _ : V m => q) := fun _ => analyticAt_const

lemma coeffAnalytic_C {m : ℕ} {f : V m → ℂ} (hf : AnalyticAt ℂ f 0) :
    CoeffAnalytic (fun p => C (f p)) := by
  intro i
  simp only [coeff_C]
  by_cases h : i = 0
  · simpa [h] using hf
  · simpa [h] using (analyticAt_const (E := V m) (v := (0 : ℂ)) (x := 0))

lemma CoeffAnalytic.add {m : ℕ} {f g : V m → Polynomial ℂ}
    (hf : CoeffAnalytic f) (hg : CoeffAnalytic g) :
    CoeffAnalytic (fun p => f p + g p) := by
  intro i
  convert! (hf i).add (hg i) using 1

lemma CoeffAnalytic.sub {m : ℕ} {f g : V m → Polynomial ℂ}
    (hf : CoeffAnalytic f) (hg : CoeffAnalytic g) :
    CoeffAnalytic (fun p => f p - g p) := by
  intro i
  convert! (hf i).sub (hg i) using 1

lemma CoeffAnalytic.mul {m : ℕ} {f g : V m → Polynomial ℂ}
    (hf : CoeffAnalytic f) (hg : CoeffAnalytic g) :
    CoeffAnalytic (fun p => f p * g p) := by
  intro i
  simp only [coeff_mul]
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (hf j.1).mul (hg j.2)

lemma CoeffAnalytic.pow {m : ℕ} {f : V m → Polynomial ℂ}
    (hf : CoeffAnalytic f) (n : ℕ) : CoeffAnalytic (fun p => f p ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using coeffAnalytic_const (m := m) 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma polyMap_fixed {n k : ℕ} (hk : k < n) (x₀ : V n)
    (hzero : ∀ j : Fin k, x₀ ⟨j, lt_trans j.isLt hk⟩ = 0) :
    polyMap hk x₀ = x₀ := by
  ext i
  unfold polyMap
  have hs : (∑ j : Fin k, if (j : ℕ) ≤ i then
      x₀ ⟨j, lt_trans j.isLt hk⟩ * high k x₀ (i-j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hzero j]
  rw [hs, add_zero]
  split
  · rfl
  · rename_i h
    exact (hzero ⟨i, by omega⟩).symm

 

theorem prepare_polynomial {m n k : ℕ} (hk : k < n)
    (f : V m → Polynomial ℂ) (hf : CoeffAnalytic f)
    (hdeg : ∀ p, (f p).natDegree < n)
    (hzero : ∀ j : Fin k, (f 0).coeff j = 0)
    (hone : (f 0).coeff k = 1) :
    ∃ A : V m → V n, AnalyticAt ℂ A 0 ∧ A 0 = toFn n (f 0) ∧
      ∀ᶠ p in 𝓝 0, f p = rootPoly hk (A p) * highPoly hk (A p) := by
  let x₀ := toFn n (f 0)
  have hz : ∀ j : Fin k, x₀ ⟨j, lt_trans j.isLt hk⟩ = 0 := hzero
  have ho : x₀ ⟨k, hk⟩ = 1 := hone
  obtain ⟨g, hg, hg0, heq⟩ := factor_coordinates hk x₀ hz ho
  rw [polyMap_fixed hk x₀ hz] at hg hg0 heq
  have hc : AnalyticAt ℂ (fun p => toFn n (f p)) 0 := AnalyticAt.pi (fun i => hf i)
  refine ⟨fun p => g (toFn n (f p)), hg.comp hc, hg0, ?_⟩
  filter_upwards [hc.continuousAt heq] with p hp
  rw [factor_eq_ofFn, hp, ofFn_comp_toFn_eq_id_of_natDegree_lt (hdeg p)]

def q1 {R : Type*} [CommRing R] (u w : R) : R :=
  (u-w-w^8)*(u-w-2*w^8)*(u-w^2)
def q2 {R : Type*} [CommRing R] (u w : R) : R := q1 u w-u^2
def psi {R : Type*} [CommRing R] (x w : R) : R :=
  (x+w)*(x+w-w^2)*q2 (x+w) w

def graph0 (p : V 2) : Polynomial ℂ := C (p 0) - C (p 1)^2 - q1 (C (p 1)) X
def graph1 (p : V 2) : Polynomial ℂ := C (p 1) - psi (C (p 0)) X

lemma graph0_analytic : CoeffAnalytic graph0 := by
  have ht := coeffAnalytic_C ((proj (1 : Fin 2)).analyticAt (0 : V 2))
  have hx := coeffAnalytic_C ((proj (0 : Fin 2)).analyticAt (0 : V 2))
  have hw := coeffAnalytic_const (m := 2) (X : Polynomial ℂ)
  have hc := coeffAnalytic_const (m := 2) (2 : Polynomial ℂ)
  exact hx.sub (ht.pow 2) |>.sub (((ht.sub hw).sub (hw.pow 8)).mul
    ((ht.sub hw).sub (hc.mul (hw.pow 8))) |>.mul (ht.sub (hw.pow 2)))

lemma graph1_analytic : CoeffAnalytic graph1 := by
  have ht := coeffAnalytic_C ((proj (1 : Fin 2)).analyticAt (0 : V 2))
  have hx := coeffAnalytic_C ((proj (0 : Fin 2)).analyticAt (0 : V 2))
  have hw := coeffAnalytic_const (m := 2) (X : Polynomial ℂ)
  have hc := coeffAnalytic_const (m := 2) (2 : Polynomial ℂ)
  have hu := hx.add hw
  have hq := (((hu.sub hw).sub (hw.pow 8)).mul
    ((hu.sub hw).sub (hc.mul (hw.pow 8))) |>.mul (hu.sub (hw.pow 2)))
  exact ht.sub ((hu.mul (hu.sub (hw.pow 2))).mul (hq.sub (hu.pow 2)))

lemma graph0_degree (p : V 2) : (graph0 p).natDegree < 19 := by
  unfold graph0 q1
  compute_degree!

lemma graph1_degree (p : V 2) : (graph1 p).natDegree < 22 := by
  unfold graph1 psi q2 q1
  compute_degree!

lemma graph0_specialization : graph0 0 = X^4 * (1+3*X^7+2*X^14) := by
  simp only [graph0, q1, Pi.zero_apply, map_zero]
  ring

lemma graph1_specialization : graph1 0 = X^4 * (1-X-2*X^15+4*X^16-2*X^17) := by
  simp only [graph1, psi, q2, q1, Pi.zero_apply, map_zero]
  ring

 
theorem prepare_graph0 :
    ∃ A : V 2 → V 19, AnalyticAt ℂ A 0 ∧ A 0 = toFn 19 (graph0 0) ∧
      ∀ᶠ p in 𝓝 0, graph0 p = rootPoly (by norm_num : 4 < 19) (A p) *
        highPoly (by norm_num : 4 < 19) (A p) := by
  apply prepare_polynomial _ graph0 graph0_analytic graph0_degree
  · intro j
    rw [graph0_specialization, coeff_X_pow_mul', ite_eq_right (by omega)]
  · rw [graph0_specialization]
    norm_num [coeff_X_pow_mul']

 
theorem prepare_graph1 :
    ∃ A : V 2 → V 22, AnalyticAt ℂ A 0 ∧ A 0 = toFn 22 (graph1 0) ∧
      ∀ᶠ p in 𝓝 0, graph1 p = rootPoly (by norm_num : 4 < 22) (A p) *
        highPoly (by norm_num : 4 < 22) (A p) := by
  apply prepare_polynomial _ graph1 graph1_analytic graph1_degree
  · intro j
    rw [graph1_specialization, coeff_X_pow_mul', ite_eq_right (by omega)]
  · rw [graph1_specialization]
    norm_num [coeff_X_pow_mul']

 

def coeff0 : V 2 → V 19 := Classical.choose prepare_graph0
def coeff1 : V 2 → V 22 := Classical.choose prepare_graph1

lemma coeff0_spec : AnalyticAt ℂ coeff0 0 ∧ coeff0 0 = toFn 19 (graph0 0) ∧
    ∀ᶠ p in 𝓝 0, graph0 p = rootPoly (by norm_num : 4 < 19) (coeff0 p) *
      highPoly (by norm_num : 4 < 19) (coeff0 p) := Classical.choose_spec prepare_graph0
lemma coeff1_spec : AnalyticAt ℂ coeff1 0 ∧ coeff1 0 = toFn 22 (graph1 0) ∧
    ∀ᶠ p in 𝓝 0, graph1 p = rootPoly (by norm_num : 4 < 22) (coeff1 p) *
      highPoly (by norm_num : 4 < 22) (coeff1 p) := Classical.choose_spec prepare_graph1

lemma eval_rootPoly {n k : ℕ} (hk : k < n) (x : V n) (w : ℂ) :
    (rootPoly hk x).eval w = w^k + ∑ j : Fin k, x ⟨j, lt_trans j.isLt hk⟩ * w^(j : ℕ) := by
  simp [rootPoly, lowPoly, ofFn_eq_sum_monomial, eval_finsetSum]

lemma eval_highPoly {n k : ℕ} (hk : k < n) (x : V n) (w : ℂ) :
    (highPoly hk x).eval w = ∑ j : Fin (n-k), x ⟨k+j, by omega⟩ * w^(j : ℕ) := by
  simp [highPoly, ofFn_eq_sum_monomial, eval_finsetSum]

lemma analytic_rootPoly {m n k : ℕ} (hk : k < n) {A : V m → V n} {w : V m → ℂ}
    (hA : AnalyticAt ℂ A 0) (hw : AnalyticAt ℂ w 0) :
    AnalyticAt ℂ (fun p => (rootPoly hk (A p)).eval (w p)) 0 := by
  simp only [eval_rootPoly]
  apply AnalyticAt.add (hw.pow k)
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact ((proj _).analyticAt (A 0) |>.comp hA).mul (hw.pow j)

lemma analytic_highPoly {m n k : ℕ} (hk : k < n) {A : V m → V n} {w : V m → ℂ}
    (hA : AnalyticAt ℂ A 0) (hw : AnalyticAt ℂ w 0) :
    AnalyticAt ℂ (fun p => (highPoly hk (A p)).eval (w p)) 0 := by
  simp only [eval_highPoly]
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact ((proj _).analyticAt (A 0) |>.comp hA).mul (hw.pow j)

def base3 : V 3 →L[ℂ] V 2 := ContinuousLinearMap.pi fun i => proj i.castSucc

def root0 (p : V 2) (w : ℂ) : ℂ := (rootPoly (by norm_num : 4 < 19) (coeff0 p)).eval w
def root1 (p : V 2) (w : ℂ) : ℂ := (rootPoly (by norm_num : 4 < 22) (coeff1 p)).eval w
def unit0 (p : V 2) (w : ℂ) : ℂ := (highPoly (by norm_num : 4 < 19) (coeff0 p)).eval w
def unit1 (p : V 2) (w : ℂ) : ℂ := (highPoly (by norm_num : 4 < 22) (coeff1 p)).eval w

def r0 (z : V 3) : ℂ := root0 (base3 z) (z 2)
def r1 (z : V 3) : ℂ := root1 (base3 z) (z 2)
def u0 (z : V 3) : ℂ := unit0 (base3 z) (z 2)
def u1 (z : V 3) : ℂ := unit1 (base3 z) (z 2)

lemma r0_analytic : AnalyticAt ℂ r0 0 := by
  apply analytic_rootPoly _ (w := proj (2 : Fin 3))
  · have ha : AnalyticAt ℂ coeff0 (base3 (0 : V 3)) := by simpa using coeff0_spec.1
    exact ha.comp (base3.analyticAt 0)
  · exact (proj _).analyticAt 0
lemma r1_analytic : AnalyticAt ℂ r1 0 := by
  apply analytic_rootPoly _ (w := proj (2 : Fin 3))
  · have ha : AnalyticAt ℂ coeff1 (base3 (0 : V 3)) := by simpa using coeff1_spec.1
    exact ha.comp (base3.analyticAt 0)
  · exact (proj _).analyticAt 0
lemma u0_analytic : AnalyticAt ℂ u0 0 := by
  apply analytic_highPoly _ (w := proj (2 : Fin 3))
  · have ha : AnalyticAt ℂ coeff0 (base3 (0 : V 3)) := by simpa using coeff0_spec.1
    exact ha.comp (base3.analyticAt 0)
  · exact (proj _).analyticAt 0
lemma u1_analytic : AnalyticAt ℂ u1 0 := by
  apply analytic_highPoly _ (w := proj (2 : Fin 3))
  · have ha : AnalyticAt ℂ coeff1 (base3 (0 : V 3)) := by simpa using coeff1_spec.1
    exact ha.comp (base3.analyticAt 0)
  · exact (proj _).analyticAt 0

lemma root0_at_base_zero (w : ℂ) : root0 0 w = w^4 := by
  rw [root0, eval_rootPoly, coeff0_spec.2.1]
  have hs : (∑ j : Fin 4, toFn 19 (graph0 0) ⟨j, by omega⟩ * w^(j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    change (graph0 0).coeff j * w^(j : ℕ) = 0
    rw [graph0_specialization, coeff_X_pow_mul', ite_eq_right (by omega), zero_mul]
  rw [hs, add_zero]
lemma root1_at_base_zero (w : ℂ) : root1 0 w = w^4 := by
  rw [root1, eval_rootPoly, coeff1_spec.2.1]
  have hs : (∑ j : Fin 4, toFn 22 (graph1 0) ⟨j, by omega⟩ * w^(j : ℕ)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    change (graph1 0).coeff j * w^(j : ℕ) = 0
    rw [graph1_specialization, coeff_X_pow_mul', ite_eq_right (by omega), zero_mul]
  rw [hs, add_zero]

lemma r0_zero : r0 0 = 0 := by simp [r0, root0_at_base_zero]
lemma r1_zero : r1 0 = 0 := by simp [r1, root1_at_base_zero]
lemma u0_zero : u0 0 = 1 := by
  simp only [u0, unit0, map_zero, Pi.zero_apply, coeff0_spec.2.1, ← coeff_zero_eq_eval_zero, coeff_highPoly]
  change (graph0 0).coeff 4 = 1
  rw [graph0_specialization]
  norm_num [coeff_X_pow_mul']
lemma u1_zero : u1 0 = 1 := by
  simp only [u1, unit1, map_zero, Pi.zero_apply, coeff1_spec.2.1, ← coeff_zero_eq_eval_zero, coeff_highPoly]
  change (graph1 0).coeff 4 = 1
  rw [graph1_specialization]
  norm_num [coeff_X_pow_mul']

lemma graph0_factor : ∀ᶠ z : V 3 in 𝓝 0,
    z 0 - (z 1)^2 - q1 (z 1) (z 2) = r0 z * u0 z := by
  have hb : Tendsto base3 (𝓝 (0 : V 3)) (𝓝 0) := by simpa using base3.continuous.tendsto 0
  filter_upwards [hb.eventually coeff0_spec.2.2] with z hz
  have h := congrArg (Polynomial.eval (z 2)) hz
  simpa [graph0, q1, r0, u0, root0, unit0, base3] using h
lemma graph1_factor : ∀ᶠ z : V 3 in 𝓝 0,
    z 1 - psi (z 0) (z 2) = r1 z * u1 z := by
  have hb : Tendsto base3 (𝓝 (0 : V 3)) (𝓝 0) := by simpa using base3.continuous.tendsto 0
  filter_upwards [hb.eventually coeff1_spec.2.2] with z hz
  have h := congrArg (Polynomial.eval (z 2)) hz
  simpa [graph1, psi, q2, q1, r1, u1, root1, unit1, base3] using h

lemma strict_mul_vanishing {m : ℕ} {f g : V m → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    HasStrictFDerivAt (fun z => f z*g z) (0 : V m →L[ℂ] ℂ) 0 := by
  convert! hf.hasStrictFDerivAt.fun_mul hg.hasStrictFDerivAt using 1
  ext v
  simp [hf0, hg0]

lemma graph0_deriv : HasStrictFDerivAt
    (fun z : V 3 => z 0 - (z 1)^2 - q1 (z 1) (z 2)) (proj 0) 0 := by
  have ht : HasStrictFDerivAt (fun z : V 3 => (z 1)^2) (0 : V 3 →L[ℂ] ℂ) 0 := by
    convert! (proj (1 : Fin 3)).hasStrictFDerivAt.pow 2 using 1
    ext v
    simp
  have ap := (proj (1 : Fin 3)).analyticAt (0 : V 3)
  have aw := (proj (2 : Fin 3)).analyticAt (0 : V 3)
  have ac : AnalyticAt ℂ (fun _ : V 3 => (2 : ℂ)) 0 := analyticAt_const
  have hf : AnalyticAt ℂ (fun z : V 3 => z 1-z 2-(z 2)^8) 0 := by
    convert! (ap.sub aw).sub (aw.pow 8) using 1
  have hg : AnalyticAt ℂ (fun z : V 3 => (z 1-z 2-2*(z 2)^8)*(z 1-(z 2)^2)) 0 := by
    convert! ((ap.sub aw).sub (ac.mul (aw.pow 8))).mul (ap.sub (aw.pow 2)) using 1
  have hq : HasStrictFDerivAt (fun z : V 3 => q1 (z 1) (z 2)) (0 : V 3 →L[ℂ] ℂ) 0 := by
    convert! strict_mul_vanishing hf hg (by simp) (by simp) using 1
    ext z
    simp only [q1, mul_assoc]
  convert! (proj (0 : Fin 3)).hasStrictFDerivAt.sub ht |>.sub hq using 1
  simp

lemma graph1_deriv : HasStrictFDerivAt
    (fun z : V 3 => z 1 - psi (z 0) (z 2)) (proj 1) 0 := by
  have ax := (proj (0 : Fin 3)).analyticAt (0 : V 3)
  have aw := (proj (2 : Fin 3)).analyticAt (0 : V 3)
  have ac : AnalyticAt ℂ (fun _ : V 3 => (2 : ℂ)) 0 := analyticAt_const
  have hf : AnalyticAt ℂ (fun z : V 3 => z 0+z 2) 0 := by
    convert! ax.add aw using 1
  have hq1 := ((hf.sub aw).sub (aw.pow 8)).mul ((hf.sub aw).sub (ac.mul (aw.pow 8)))
    |>.mul (hf.sub (aw.pow 2))
  have hg : AnalyticAt ℂ (fun z : V 3 => (z 0+z 2-(z 2)^2)*q2 (z 0+z 2) (z 2)) 0 := by
    convert! (hf.sub (aw.pow 2)).mul (hq1.sub (hf.pow 2)) using 1
  have hq : HasStrictFDerivAt (fun z : V 3 => psi (z 0) (z 2)) (0 : V 3 →L[ℂ] ℂ) 0 := by
    convert! strict_mul_vanishing hf hg (by simp) (by simp) using 1
    ext z
    simp only [psi, mul_assoc]
  convert! (proj (1 : Fin 3)).hasStrictFDerivAt.sub hq using 1
  simp

lemma derivative_unit_factor {m : ℕ} {r u f : V m → ℂ} {L : V m →L[ℂ] ℂ}
    (hr : AnalyticAt ℂ r 0) (hu : AnalyticAt ℂ u 0)
    (hr0 : r 0 = 0) (hu0 : u 0 = 1)
    (heq : ∀ᶠ z in 𝓝 0, f z = r z * u z) (hf : HasStrictFDerivAt f L 0) :
    HasStrictFDerivAt r L 0 := by
  have h : HasStrictFDerivAt (fun z => r z * u z) (fderiv ℂ r 0) 0 := by
    convert! hr.hasStrictFDerivAt.fun_mul hu.hasStrictFDerivAt using 1
    ext v
    simp [hr0, hu0]
  have he : fderiv ℂ r 0 = L := (h.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)).hasFDerivAt.unique hf.hasFDerivAt
  simpa only [he] using hr.hasStrictFDerivAt

lemma r0_deriv : HasStrictFDerivAt r0 (proj 0) 0 :=
  derivative_unit_factor r0_analytic u0_analytic r0_zero u0_zero graph0_factor graph0_deriv
lemma r1_deriv : HasStrictFDerivAt r1 (proj 1) 0 :=
  derivative_unit_factor r1_analytic u1_analytic r1_zero u1_zero graph1_factor graph1_deriv

 
def rescale (s : ℂ) : V 5 →L[ℂ] V 3 :=
  ContinuousLinearMap.pi ![proj 0, proj 1, s⁻¹ • proj 4]

def ambient0 (s : ℂ) (z : V 5) : V 5 :=
  ![r0 (rescale s z) - (s^4)⁻¹ * z 2 * z 3, z 1, z 2, z 3, z 4]
def ambient1 (s : ℂ) (z : V 5) : V 5 :=
  ![z 0, r1 (rescale s z) - (s^4)⁻¹ * z 2 * z 3, z 2, z 3, z 4]

lemma ambient0_zero (s : ℂ) : ambient0 s 0 = 0 := by
  ext i; fin_cases i <;> simp [ambient0, r0_zero]
lemma ambient1_zero (s : ℂ) : ambient1 s 0 = 0 := by
  ext i; fin_cases i <;> simp [ambient1, r1_zero]

lemma ambient0_analytic (s : ℂ) : AnalyticAt ℂ (ambient0 s) 0 := by
  have hr : AnalyticAt ℂ (fun z => r0 (rescale s z)) 0 := by
    have ha : AnalyticAt ℂ r0 (rescale s 0) := by simpa using r0_analytic
    exact ha.comp ((rescale s).analyticAt 0)
  have hyz : AnalyticAt ℂ (fun z : V 5 => (s^4)⁻¹ * z 2 * z 3) 0 := by
    convert! (analyticAt_const.mul ((proj (2 : Fin 5)).analyticAt 0)).mul
      ((proj (3 : Fin 5)).analyticAt 0) using 1
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hr.sub hyz
  all_goals exact (proj _).analyticAt 0
lemma ambient1_analytic (s : ℂ) : AnalyticAt ℂ (ambient1 s) 0 := by
  have hr : AnalyticAt ℂ (fun z => r1 (rescale s z)) 0 := by
    have ha : AnalyticAt ℂ r1 (rescale s 0) := by simpa using r1_analytic
    exact ha.comp ((rescale s).analyticAt 0)
  have hyz : AnalyticAt ℂ (fun z : V 5 => (s^4)⁻¹ * z 2 * z 3) 0 := by
    convert! (analyticAt_const.mul ((proj (2 : Fin 5)).analyticAt 0)).mul
      ((proj (3 : Fin 5)).analyticAt 0) using 1
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (proj _).analyticAt 0
  · exact hr.sub hyz
  all_goals exact (proj _).analyticAt 0

lemma yz_deriv (s : ℂ) : HasStrictFDerivAt
    (fun z : V 5 => (s^4)⁻¹ * z 2 * z 3) (0 : V 5 →L[ℂ] ℂ) 0 := by
  have ha : AnalyticAt ℂ (fun z : V 5 => (s^4)⁻¹ * z 2) 0 := by
    convert! analyticAt_const.mul ((proj (2 : Fin 5)).analyticAt 0) using 1
  exact strict_mul_vanishing ha ((proj (3 : Fin 5)).analyticAt 0) (by simp) (by simp)

lemma ambient0_deriv (s : ℂ) : HasStrictFDerivAt (ambient0 s)
    (ContinuousLinearEquiv.refl ℂ (V 5)).toContinuousLinearMap 0 := by
  have hr : HasStrictFDerivAt (fun z => r0 (rescale s z)) (proj 0) 0 := by
    have hr' : HasStrictFDerivAt r0 (proj 0) (rescale s 0) := by simpa using r0_deriv
    convert! hr'.comp 0 (rescale s).hasStrictFDerivAt using 1
  have hid : (ContinuousLinearEquiv.refl ℂ (V 5)).toContinuousLinearMap =
      ContinuousLinearMap.pi (fun i : Fin 5 => proj i) := by ext z i; rfl
  rw [hid]
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [ambient0] using hr.fun_sub (yz_deriv s)
  all_goals exact (proj _).hasStrictFDerivAt
lemma ambient1_deriv (s : ℂ) : HasStrictFDerivAt (ambient1 s)
    (ContinuousLinearEquiv.refl ℂ (V 5)).toContinuousLinearMap 0 := by
  have hr : HasStrictFDerivAt (fun z => r1 (rescale s z)) (proj 1) 0 := by
    have hr' : HasStrictFDerivAt r1 (proj 1) (rescale s 0) := by simpa using r1_deriv
    convert! hr'.comp 0 (rescale s).hasStrictFDerivAt using 1
  have hid : (ContinuousLinearEquiv.refl ℂ (V 5)).toContinuousLinearMap =
      ContinuousLinearMap.pi (fun i : Fin 5 => proj i) := by ext z i; rfl
  rw [hid]
  apply hasStrictFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (proj _).hasStrictFDerivAt
  · simpa [ambient1] using hr.fun_sub (yz_deriv s)
  all_goals exact (proj _).hasStrictFDerivAt

lemma inverse_map_analytic {n : ℕ} {f : V n → V n} {x : V n}
    (e : V n ≃L[ℂ] V n) (hf : AnalyticAt ℂ f x)
    (hd : HasStrictFDerivAt f e.toContinuousLinearMap x) :
    AnalyticAt ℂ (hd.toOpenPartialHomeomorph f).symm (f x) := by
  let R := hd.toOpenPartialHomeomorph f
  have hx : x ∈ R.source := hd.mem_toOpenPartialHomeomorph_source
  obtain ⟨p, hp⟩ := hf
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (V n) (V n)).symm e.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℂ (V n) (V n)).injective
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hp.hasFDerivAt.unique hd.hasFDerivAt
  exact (R.hasFPowerSeriesAt_symm hx hp hp1).analyticAt

def ambientEquiv0 (s : ℂ) : OpenPartialHomeomorph (V 5) (V 5) :=
  (ambient0_deriv s).toOpenPartialHomeomorph (ambient0 s)
def ambientEquiv1 (s : ℂ) : OpenPartialHomeomorph (V 5) (V 5) :=
  (ambient1_deriv s).toOpenPartialHomeomorph (ambient1 s)

lemma ambientEquiv0_apply (s : ℂ) : (ambientEquiv0 s : V 5 → V 5) = ambient0 s := rfl
lemma ambientEquiv1_apply (s : ℂ) : (ambientEquiv1 s : V 5 → V 5) = ambient1 s := rfl
lemma ambientEquiv0_source (s : ℂ) : (0 : V 5) ∈ (ambientEquiv0 s).source :=
  (ambient0_deriv s).mem_toOpenPartialHomeomorph_source
lemma ambientEquiv1_source (s : ℂ) : (0 : V 5) ∈ (ambientEquiv1 s).source :=
  (ambient1_deriv s).mem_toOpenPartialHomeomorph_source
lemma inverse0_zero (s : ℂ) : (ambientEquiv0 s).symm 0 = 0 := by
  have h := (ambientEquiv0 s).left_inv (ambientEquiv0_source s)
  simpa only [ambientEquiv0_apply, ambient0_zero] using h
lemma inverse1_zero (s : ℂ) : (ambientEquiv1 s).symm 0 = 0 := by
  have h := (ambientEquiv1 s).left_inv (ambientEquiv1_source s)
  simpa only [ambientEquiv1_apply, ambient1_zero] using h
lemma inverse0_analytic (s : ℂ) : AnalyticAt ℂ (ambientEquiv0 s).symm 0 := by
  simpa only [ambientEquiv0, ambient0_zero] using inverse_map_analytic
    (ContinuousLinearEquiv.refl ℂ (V 5)) (ambient0_analytic s) (ambient0_deriv s)
lemma inverse1_analytic (s : ℂ) : AnalyticAt ℂ (ambientEquiv1 s).symm 0 := by
  simpa only [ambientEquiv1, ambient1_zero] using inverse_map_analytic
    (ContinuousLinearEquiv.refl ℂ (V 5)) (ambient1_analytic s) (ambient1_deriv s)

def embed0 : V 4 →L[ℂ] V 5 := ContinuousLinearMap.pi ![0, proj 0, proj 1, proj 2, proj 3]
def embed1 : V 4 →L[ℂ] V 5 := ContinuousLinearMap.pi ![proj 0, 0, proj 1, proj 2, proj 3]
 
def chart0 (s : ℂ) (x : V 4) : V 5 := (ambientEquiv0 s).symm (embed0 x)
def chart1 (s : ℂ) (x : V 4) : V 5 := (ambientEquiv1 s).symm (embed1 x)
lemma chart0_zero (s : ℂ) : chart0 s 0 = 0 := by simp [chart0, inverse0_zero]
lemma chart1_zero (s : ℂ) : chart1 s 0 = 0 := by simp [chart1, inverse1_zero]
lemma chart0_analytic (s : ℂ) : AnalyticAt ℂ (chart0 s) 0 := by
  have hi : AnalyticAt ℂ (ambientEquiv0 s).symm (embed0 0) := by simpa using inverse0_analytic s
  exact hi.comp (embed0.analyticAt 0)
lemma chart1_analytic (s : ℂ) : AnalyticAt ℂ (chart1 s) 0 := by
  have hi : AnalyticAt ℂ (ambientEquiv1 s).symm (embed1 0) := by simpa using inverse1_analytic s
  exact hi.comp (embed1.analyticAt 0)
lemma chart0_eq (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4), ambient0 s (chart0 s x) = embed0 x := by
  have h := (ambientEquiv0 s).eventually_right_inverse' (ambientEquiv0_source s)
  rw [ambientEquiv0_apply, ambient0_zero] at h
  have ht : Tendsto embed0 (𝓝 (0 : V 4)) (𝓝 0) := by simpa using embed0.continuous.tendsto 0
  exact ht.eventually h
lemma chart1_eq (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4), ambient1 s (chart1 s x) = embed1 x := by
  have h := (ambientEquiv1 s).eventually_right_inverse' (ambientEquiv1_source s)
  rw [ambientEquiv1_apply, ambient1_zero] at h
  have ht : Tendsto embed1 (𝓝 (0 : V 4)) (𝓝 0) := by simpa using embed1.continuous.tendsto 0
  exact ht.eventually h

lemma chart0_coordinates (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart0 s x 1 = x 0 ∧ chart0 s x 2 = x 1 ∧ chart0 s x 3 = x 2 ∧
    chart0 s x 4 = x 3 ∧ r0 (rescale s (chart0 s x)) = (s^4)⁻¹*x 1*x 2 := by
  filter_upwards [chart0_eq s] with x hx
  have h (i : Fin 5) := congrFun hx i
  have h1 : chart0 s x 1 = x 0 := by simpa [ambient0, embed0] using h 1
  have h2 : chart0 s x 2 = x 1 := by simpa [ambient0, embed0] using h 2
  have h3 : chart0 s x 3 = x 2 := by simpa [ambient0, embed0] using h 3
  have h4 : chart0 s x 4 = x 3 := by simpa [ambient0, embed0] using h 4
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hr := h 0
  simpa [ambient0, embed0, h2, h3, sub_eq_zero] using hr
lemma chart1_coordinates (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart1 s x 0 = x 0 ∧ chart1 s x 2 = x 1 ∧ chart1 s x 3 = x 2 ∧
    chart1 s x 4 = x 3 ∧ r1 (rescale s (chart1 s x)) = (s^4)⁻¹*x 1*x 2 := by
  filter_upwards [chart1_eq s] with x hx
  have h (i : Fin 5) := congrFun hx i
  have h0 : chart1 s x 0 = x 0 := by simpa [ambient1, embed1] using h 0
  have h2 : chart1 s x 2 = x 1 := by simpa [ambient1, embed1] using h 2
  have h3 : chart1 s x 3 = x 2 := by simpa [ambient1, embed1] using h 3
  have h4 : chart1 s x 4 = x 3 := by simpa [ambient1, embed1] using h 4
  refine ⟨h0, h2, h3, h4, ?_⟩
  have hr := h 1
  simpa [ambient1, embed1, h2, h3, sub_eq_zero] using hr

lemma chart0_implicit (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart0 s x 0 = (x 0)^2 + q1 (x 0) (x 3/s) +
      (s^4)⁻¹*x 1*x 2 * u0 (rescale s (chart0 s x)) := by
  have ht : Tendsto (fun x => rescale s (chart0 s x)) (𝓝 (0 : V 4)) (𝓝 0) := by
    convert! (rescale s).continuous.tendsto (chart0 s 0) |>.comp
      (chart0_analytic s).continuousAt using 1
    simp [chart0_zero]
  filter_upwards [ht.eventually graph0_factor, chart0_coordinates s] with x hf hx
  rcases hx with ⟨ht, hy, hz, hw, hr⟩
  have he : chart0 s x 0 - (x 0)^2 - q1 (x 0) (x 3/s) =
      (s^4)⁻¹*x 1*x 2 * u0 (rescale s (chart0 s x)) := by
    rw [hr] at hf
    simpa [rescale, ht, hw, div_eq_mul_inv, mul_comm] using hf
  linear_combination he
lemma chart1_implicit (s : ℂ) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart1 s x 1 = psi (x 0) (x 3/s) +
      (s^4)⁻¹*x 1*x 2 * u1 (rescale s (chart1 s x)) := by
  have ht : Tendsto (fun x => rescale s (chart1 s x)) (𝓝 (0 : V 4)) (𝓝 0) := by
    convert! (rescale s).continuous.tendsto (chart1 s 0) |>.comp
      (chart1_analytic s).continuousAt using 1
    simp [chart1_zero]
  filter_upwards [ht.eventually graph1_factor, chart1_coordinates s] with x hf hx
  rcases hx with ⟨hx, hy, hz, hw, hr⟩
  have he : chart1 s x 1 - psi (x 0) (x 3/s) =
      (s^4)⁻¹*x 1*x 2 * u1 (rescale s (chart1 s x)) := by
    rw [hr] at hf
    simpa [rescale, hx, hw, div_eq_mul_inv, mul_comm] using hf
  linear_combination he

 
def eliminated0 (s : ℂ) (x : V 4) : ℂ := chart0 s x 0
def eliminated1 (s : ℂ) (x : V 4) : ℂ := chart1 s x 1
lemma eliminated0_analytic (s : ℂ) : AnalyticAt ℂ (eliminated0 s) 0 :=
  ((proj (0 : Fin 5)).analyticAt _).comp (chart0_analytic s)
lemma eliminated1_analytic (s : ℂ) : AnalyticAt ℂ (eliminated1 s) 0 :=
  ((proj (1 : Fin 5)).analyticAt _).comp (chart1_analytic s)
lemma eliminated0_zero (s : ℂ) : eliminated0 s 0 = 0 := by simp [eliminated0, chart0_zero]
lemma eliminated1_zero (s : ℂ) : eliminated1 s 0 = 0 := by simp [eliminated1, chart1_zero]

def perturbation (a b : ℕ) (x : V 4) : ℂ := x 3*((x 1)^a + (x 2)^b)
lemma perturbation_analytic (a b : ℕ) : AnalyticAt ℂ (perturbation a b) 0 := by
  convert! ((proj (3 : Fin 4)).analyticAt 0).mul
    ((((proj (1 : Fin 4)).analyticAt 0).pow a).add (((proj (2 : Fin 4)).analyticAt 0).pow b)) using 1

def f5 (s : ℂ) (a b : ℕ) (x : V 4) : ℂ :=
  x 0*(eliminated0 s x - (x 0)^2)*(eliminated0 s x - 2*(x 0)^2) + perturbation a b x
def f4 (s : ℂ) (a b : ℕ) (x : V 4) : ℂ :=
  eliminated1 s x*(x 0 - (eliminated1 s x)^2)*(x 0 - 2*(eliminated1 s x)^2) + perturbation a b x

lemma f5_analytic (s : ℂ) (a b : ℕ) : AnalyticAt ℂ (f5 s a b) 0 := by
  have ht := (proj (0 : Fin 4)).analyticAt (0 : V 4)
  have he := eliminated0_analytic s
  convert! ((ht.mul (he.sub (ht.pow 2))).mul
    (he.sub (analyticAt_const.mul (ht.pow 2)))).add (perturbation_analytic a b) using 1
lemma f4_analytic (s : ℂ) (a b : ℕ) : AnalyticAt ℂ (f4 s a b) 0 := by
  have hx := (proj (0 : Fin 4)).analyticAt (0 : V 4)
  have he := eliminated1_analytic s
  convert! ((he.mul (hx.sub (he.pow 2))).mul
    (hx.sub (analyticAt_const.mul (he.pow 2)))).add (perturbation_analytic a b) using 1
lemma f5_zero (s : ℂ) (a b : ℕ) : f5 s a b 0 = 0 := by
  simp [f5, perturbation]
lemma f4_zero (s : ℂ) (a b : ℕ) : f4 s a b 0 = 0 := by
  simp [f4, perturbation, eliminated1_zero]

 

lemma f5_source (s : ℂ) (a b : ℕ) : ∀ᶠ x in 𝓝 (0 : V 4),
    f5 s a b x =
      chart0 s x 1*(chart0 s x 0 - (chart0 s x 1)^2)*
        (chart0 s x 0 - 2*(chart0 s x 1)^2) +
      chart0 s x 4*((chart0 s x 2)^a + (chart0 s x 3)^b) := by
  filter_upwards [chart0_coordinates s] with x hx
  simp only [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, f5, eliminated0, perturbation]
lemma f4_source (s : ℂ) (a b : ℕ) : ∀ᶠ x in 𝓝 (0 : V 4),
    f4 s a b x =
      chart1 s x 1*(chart1 s x 0 - (chart1 s x 1)^2)*
        (chart1 s x 0 - 2*(chart1 s x 1)^2) +
      chart1 s x 4*((chart1 s x 2)^a + (chart1 s x 3)^b) := by
  filter_upwards [chart1_coordinates s] with x hx
  simp only [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, f4, eliminated1, perturbation]

lemma chart0_on_hypersurface (s : ℂ) (hs : s ≠ 0) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart0 s x 2*chart0 s x 3 = s^4*r0 (rescale s (chart0 s x)) := by
  filter_upwards [chart0_coordinates s] with x hx
  rw [hx.2.1, hx.2.2.1, hx.2.2.2.2]
  field_simp
lemma chart1_on_hypersurface (s : ℂ) (hs : s ≠ 0) : ∀ᶠ x in 𝓝 (0 : V 4),
    chart1 s x 2*chart1 s x 3 = s^4*r1 (rescale s (chart1 s x)) := by
  filter_upwards [chart1_coordinates s] with x hx
  rw [hx.2.1, hx.2.2.1, hx.2.2.2.2]
  field_simp

end
end AmbientMultiplicity.Preparation

end OAI
