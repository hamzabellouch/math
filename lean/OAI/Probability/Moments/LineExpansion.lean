import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

/- The moment functional of independent line variables, defined algebraically
so only the finitely many moments actually used need be integrable. -/
def tensorMoment (m : L → ℕ → ℝ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials L ℝ).constr ℝ (fun d => ∏ l, m l (d l))

omit [DecidableEq L] in
@[simp] theorem tensorMoment_monomial (m : L → ℕ → ℝ) (d : L →₀ ℕ) (a : ℝ) :
    tensorMoment m (monomial d a) = a * ∏ l, m l (d l) := by
  have hh : monomial d a = a • (MvPolynomial.basisMonomials L ℝ) d := by
    rw [MvPolynomial.coe_basisMonomials]
    rw [← map_smul]
    simp
  rw [hh, map_smul]
  change a • (((MvPolynomial.basisMonomials L ℝ).constr ℝ)
    (fun d => ∏ l, m l (d l))) ((MvPolynomial.basisMonomials L ℝ) d) = _
  rw [Module.Basis.constr_basis, smul_eq_mul]

omit [DecidableEq L] in
@[simp] theorem tensorMoment_one (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1) :
    tensorMoment m 1 = 1 := by
  rw [MvPolynomial.one_def, tensorMoment_monomial]
  simp [hm]

omit [DecidableEq L] in
theorem tensorMoment_sum (m : L → ℕ → ℝ) (p : MvPolynomial L ℝ) :
    tensorMoment m p = ∑ d ∈ p.support, p.coeff d * ∏ l, m l (d l) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, tensorMoment_monomial]

/- Multiplicativity is asserted ONLY across disjoint sets of line variables. -/
omit [DecidableEq L] in
theorem tensorMoment_mul_disjoint (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (p q : MvPolynomial L ℝ) (hd : Disjoint p.vars q.vars) :
    tensorMoment m (p*q) = tensorMoment m p * tensorMoment m q := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial, tensorMoment_monomial]
  rw [tensorMoment_sum, tensorMoment_sum, Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  have heq : ∀ l, m l ((d+e) l) = m l (d l) * m l (e l) := by
    intro l
    by_cases hdl : d l = 0
    · simp [hdl, hm]
    · have hdp : l ∈ p.vars := p.support_subset_vars_of_mem_support hd'
        (Finsupp.mem_support_iff.mpr hdl)
      have hnot : l ∉ q.vars := fun he => Finset.disjoint_left.mp hd hdp he
      have hel := MvPolynomial.mem_support_notMem_vars_zero he' hnot
      simp [hel, hm]
  simp only [heq, Finset.prod_mul_distrib]
  ring

/- One-variable powers really have just the specified one-line moment. -/
omit [DecidableEq L] in
theorem tensorMoment_X_pow (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1) (l : L) (n : ℕ) :
    tensorMoment m (X l ^ n) = m l n := by
  rw [X_pow_eq_monomial, tensorMoment_monomial, one_mul]
  rw [Finset.prod_eq_single l]
  · simp
  · intro a _ ha
    simp [ha, hm]
  · simp

/- Factorization of arbitrary polynomials, one for each distinct line. -/
theorem tensorMoment_prod_separated (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (S : Finset L) (p : L → MvPolynomial L ℝ) (hp : ∀ l ∈ S, (p l).vars ⊆ {l}) :
    tensorMoment m (∏ l ∈ S, p l) = ∏ l ∈ S, tensorMoment m (p l) := by
  induction S using Finset.induction_on with
  | empty => simp [tensorMoment_one m hm]
  | @insert l S hl ih =>
    rw [Finset.prod_insert hl, tensorMoment_mul_disjoint m hm,
      Finset.prod_insert hl, ih (fun a ha => hp a (Finset.mem_insert_of_mem ha))]
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hal : a = l := Finset.mem_singleton.mp (hp l (Finset.mem_insert_self _ _) ha)
    subst a
    have hv := MvPolynomial.vars_prod p hb
    simp only [Finset.mem_biUnion] at hv
    obtain ⟨a,ha,hla⟩ := hv
    have hla' : l = a := Finset.mem_singleton.mp (hp a (Finset.mem_insert_of_mem ha) hla)
    exact hl (hla'.symm ▸ ha)

/- The exact linear functional for a fixed subset of the non-good paths.
Translation by -1 retains all correlations between repeated uses of a line. -/
def shiftedMoment (m : L → ℕ → ℝ) (r : L → ℕ) : MvPolynomial L ℝ →ₗ[ℝ] ℝ :=
  (tensorMoment m).comp
    ((LinearMap.mulLeft ℝ (∏ l, (X l : MvPolynomial L ℝ)^r l)).comp
      (MvPolynomial.aeval (fun l => (X l : MvPolynomial L ℝ)-1)).toLinearMap)

def lineCenteredMoment (m : L → ℕ → ℝ) (l : L) (r u : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) * m l (r+a)

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

omit [Fintype L] in
theorem vars_X_centered_power (l : L) (r u : ℕ) :
    (((X l : MvPolynomial L ℝ)^r) * (X l - 1)^u).vars ⊆ {l} := by
  apply (MvPolynomial.vars_mul _ _).trans
  apply Finset.union_subset
  · exact (MvPolynomial.vars_pow _ _).trans (by simp)
  · apply (MvPolynomial.vars_pow _ _).trans
    exact (MvPolynomial.vars_sub_subset (p := (X l : MvPolynomial L ℝ)) (q := 1)).trans (by simp)

omit [DecidableEq L] in
theorem tensorMoment_X_centered_power (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (l : L) (r u : ℕ) :
    tensorMoment m ((X l : MvPolynomial L ℝ)^r * (X l-1)^u) =
      lineCenteredMoment m l r u := by
  rw [sub_pow, Finset.mul_sum, map_sum]
  unfold lineCenteredMoment
  apply Finset.sum_congr rfl
  intro a _
  have ht : (X l : MvPolynomial L ℝ)^r *
      ((-1)^(a+u) * X l^a * 1^(u-a) * (u.choose a : MvPolynomial L ℝ)) =
      (((-1 : ℝ)^(a+u) * (u.choose a : ℝ)) • (X l : MvPolynomial L ℝ)^(r+a)) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast, pow_add]
    ring
  rw [ht, map_smul, tensorMoment_X_pow m hm, smul_eq_mul]

/- Repeated uses of one line are collected into a SINGLE mixed centered moment. -/
theorem shiftedMoment_monomial (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (d : L →₀ ℕ) (a : ℝ) :
    shiftedMoment m r (monomial d a) = a * ∏ l, lineCenteredMoment m l (r l) (d l) := by
  unfold shiftedMoment
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype d _ (by simp)]
  have he : (∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ((algebraMap ℝ (MvPolynomial L ℝ)) a * ∏ l, (X l-1)^d l) =
      a • (∏ l, (X l : MvPolynomial L ℝ)^r l * (X l-1)^d l) := by
    rw [Finset.prod_mul_distrib, Algebra.smul_def]
    ring
  rw [he, map_smul, tensorMoment_prod_separated m hm _ _ (fun l _ => vars_X_centered_power l _ _)]
  simp only [tensorMoment_X_centered_power m hm, smul_eq_mul]

/- Coefficientwise nonnegativity, used only for the positive centered expansion. -/
def NonnegCoeffs (p : MvPolynomial L ℝ) : Prop := ∀ d, 0 ≤ p.coeff d

omit [Fintype L] in
theorem nonnegCoeffs_one : NonnegCoeffs (1 : MvPolynomial L ℝ) := by
  intro d
  simp only [coeff_one]
  split_ifs <;> norm_num

omit [Fintype L] [DecidableEq L] in
theorem NonnegCoeffs.add {p q : MvPolynomial L ℝ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p+q) := by
  intro d
  exact add_nonneg (hp d) (hq d)

omit [Fintype L] in
theorem NonnegCoeffs.mul {p q : MvPolynomial L ℝ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p*q) := by
  intro d
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (hp e.1) (hq e.2))

omit [Fintype L] in
theorem nonnegCoeffs_X (l : L) : NonnegCoeffs (X l : MvPolynomial L ℝ) := by
  intro d
  simp only [coeff_X]
  split_ifs <;> norm_num

omit [Fintype L] [DecidableEq L] in
theorem nonnegCoeffs_prod {I : Type*} (S : Finset I) (p : I → MvPolynomial L ℝ)
    (hp : ∀ i ∈ S, NonnegCoeffs (p i)) : NonnegCoeffs (∏ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (nonnegCoeffs_one (L := L))
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

omit [Fintype L] [DecidableEq L] in
theorem nonnegCoeffs_sum {I : Type*} (S : Finset I) (p : I → MvPolynomial L ℝ)
    (hp : ∀ i ∈ S, NonnegCoeffs (p i)) : NonnegCoeffs (∑ i ∈ S, p i) := by
  intro d
  rw [coeff_sum]
  exact Finset.sum_nonneg (fun i hi => hp i hi d)

/- Exact tensor moment estimate. Its potential premise is local in each
line and each used degree, not independence of particle factors. -/
theorem shiftedMoment_abs_le_eval (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (p : MvPolynomial L ℝ) (hp : NonnegCoeffs p)
    (C t : ℝ)
    (hb : ∀ d ∈ p.support, ∀ l,
      |lineCenteredMoment m l (r l) (d l)| ≤ C^(r l) * t^(d l)) :
    |shiftedMoment m r p| ≤ C^(∑ l, r l) * MvPolynomial.eval (fun _ => t) p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  calc
    _ ≤ ∑ d ∈ p.support, |shiftedMoment m r (monomial d (p.coeff d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ p.support, p.coeff d * ∏ l, (C^(r l) * t^(d l)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [shiftedMoment_monomial m hm, abs_mul, abs_of_nonneg (hp d), Finset.abs_prod]
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun l _ => hb d hd l)) (hp d)
    _ = C^(∑ l, r l) * MvPolynomial.eval (fun _ => t) p := by
      conv_rhs => rw [p.as_sum]
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype d _ (by simp),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

/- Positive expansion for a centered particle factor. This is a sum over
NONEMPTY subsets of its stages; no independence of particle factors is used. -/
def pathExpansion (S : Finset J) (f : J → L) : MvPolynomial L ℝ :=
  ∑ T ∈ S.powerset.erase ∅, ∏ j ∈ T, X (f j)

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_eq (S : Finset J) (f : J → L) :
    pathExpansion S f = (∏ j ∈ S, ((X (f j) : MvPolynomial L ℝ)+1))-1 := by
  have he := Finset.sum_erase_add S.powerset (fun T => ∏ j ∈ T, (X (f j) : MvPolynomial L ℝ))
    (Finset.empty_mem_powerset S)
  simp only [Finset.prod_empty] at he
  unfold pathExpansion
  rw [Finset.prod_add_one]
  exact eq_sub_of_add_eq he

omit [Fintype L] [Fintype J] in
theorem pathExpansion_nonneg (S : Finset J) (f : J → L) :
    NonnegCoeffs (pathExpansion S f) := by
  exact nonnegCoeffs_sum _ _ (fun T _ => nonnegCoeffs_prod T _ (fun j _ => nonnegCoeffs_X _))

omit [Fintype L] [Fintype J] in
theorem pathExpansion_degree (S : Finset J) (f : J → L) (l : L) :
    (pathExpansion S f).degreeOf l ≤ ∑ j ∈ S, if f j = l then 1 else 0 := by
  rw [pathExpansion_eq]
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  rw [MvPolynomial.degreeOf_one, max_eq_left (Nat.zero_le _)]
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hd := MvPolynomial.degreeOf_add_le l (X (f j) : MvPolynomial L ℝ) 1
  simpa only [MvPolynomial.degreeOf_one, MvPolynomial.degreeOf_X, eq_comm,
    max_eq_left (Nat.zero_le _)] using hd

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_eval (S : Finset J) (f : J → L) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (pathExpansion S f) = (1+t)^S.card-1 := by
  rw [pathExpansion_eq]
  simp [add_comm]

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_shift (S : Finset J) (f : J → L) :
    MvPolynomial.aeval (fun l => (X l : MvPolynomial L ℝ)-1) (pathExpansion S f) =
      (∏ j ∈ S, (X (f j) : MvPolynomial L ℝ))-1 := by
  rw [pathExpansion_eq]
  simp

/- Combined centered expansion, with the actual same variable on a shared line. -/
def goodExpansion (G : Finset I) (path : I → J → L) : MvPolynomial L ℝ :=
  ∏ i ∈ G, pathExpansion Finset.univ (path i)

omit [Fintype L] [DecidableEq I] in
theorem goodExpansion_nonneg (G : Finset I) (path : I → J → L) :
    NonnegCoeffs (goodExpansion G path) := by
  exact nonnegCoeffs_prod _ _ (fun i _ => pathExpansion_nonneg _ _)

omit [Fintype L] [DecidableEq I] in
theorem goodExpansion_degree (G : Finset I) (path : I → J → L) (l : L) :
    (goodExpansion G path).degreeOf l ≤ ∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0 := by
  exact (MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun _ _ => pathExpansion_degree _ _ _))

omit [Fintype L] [DecidableEq L] [DecidableEq I] in
theorem goodExpansion_eval (G : Finset I) (path : I → J → L) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (goodExpansion G path) =
      ((1+t)^Fintype.card J-1)^G.card := by
  simp [goodExpansion, pathExpansion_eval]

/- Uniform estimate for (1+C*x)^b-1, retaining one small factor per particle. -/
theorem centered_power_le (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1) (b : ℕ) :
    (1+C*x)^b-1 ≤ ((1+C)^b-1)*x := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hCx : 0 ≤ C*x := mul_nonneg hC hx
    have hb : 1 ≤ (1+C)^b := one_le_pow₀ (by linarith)
    have hsmall : C*x ≤ C := mul_le_of_le_one_right hC hx1
    have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+C*x)
    have her : ((1+C)^b-1)*x*(1+C*x) ≤ ((1+C)^b-1)*x*(1+C) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hx)
    rw [pow_succ, pow_succ]
    nlinarith

omit [Fintype L] [DecidableEq L] [DecidableEq I] in
theorem goodExpansion_eval_le (G : Finset I) (path : I → J → L)
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    MvPolynomial.eval (fun _ => C*x) (goodExpansion G path) ≤
      (1+C)^(Fintype.card J*G.card) * x^G.card := by
  rw [goodExpansion_eval]
  have h1 : 1 ≤ (1+C*x)^Fintype.card J := one_le_pow₀ (by nlinarith)
  have he := centered_power_le C x hC hx hx1 (Fintype.card J)
  have hu : ((1+C)^Fintype.card J-1)*x ≤ (1+C)^Fintype.card J*x := by nlinarith
  calc
    _ ≤ ((1+C)^Fintype.card J*x)^G.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr h1) (he.trans hu) _
    _ = _ := by rw [mul_pow, ← pow_mul]

/- Core shared-line estimate behind source (10), before inserting the actual
gamma moments. Each line degree is limited by the count of good trajectories
through it, and each good path supplies a factor sqrt(eta). -/
omit [DecidableEq I] in
theorem goodExpansion_moment_le (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (G : Finset I) (path : I → J → L)
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hb : ∀ l u, u ≤ (∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0) →
      |lineCenteredMoment m l (r l) u| ≤ C^(r l) * (C*x)^u) :
    |shiftedMoment m r (goodExpansion G path)| ≤
      C^(∑ l, r l) * (1+C)^(Fintype.card J*G.card) * x^G.card := by
  have he := shiftedMoment_abs_le_eval m hm r (goodExpansion G path)
    (goodExpansion_nonneg G path) C (C*x) (by
      intro d hd l
      exact hb l (d l) ((MvPolynomial.monomial_le_degreeOf l hd).trans
        (goodExpansion_degree G path l)))
  exact he.trans ((mul_le_mul_of_nonneg_left
    (goodExpansion_eval_le G path C x hC hx hx1) (pow_nonneg hC _)).trans_eq (by ring))

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

def incidenceCount (A : Finset I) (path : I → J → L) (l : L) : ℕ :=
  ∑ i ∈ A, ∑ j : J, if path i j = l then 1 else 0

/- A monomial counts line uses, including simultaneous uses by distinct paths. -/
omit [DecidableEq I] [DecidableEq J] in
theorem tensorMoment_path_monomial (m : L → ℕ → ℝ) (r : L → ℕ)
    (A : Finset I) (path : I → J → L) :
    tensorMoment m ((∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ∏ i ∈ A, ∏ j : J, X (path i j)) =
        ∏ l, m l (r l+incidenceCount A path l) := by
  have hr : (∏ l, (X l : MvPolynomial L ℝ)^r l) =
      monomial (∑ l, Finsupp.single l (r l)) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    apply Finset.prod_congr rfl
    intro l _
    exact X_pow_eq_monomial
  have hp : (∏ i ∈ A, ∏ j : J, (X (path i j) : MvPolynomial L ℝ)) =
      monomial (∑ i ∈ A, ∑ j : J, Finsupp.single (path i j) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [hr, hp, MvPolynomial.monomial_mul_monomial, one_mul, tensorMoment_monomial, one_mul]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  simp [incidenceCount, Finsupp.single_apply, eq_comm]

/- Exact alternation identity. The summation set is the omitted subset of good
particles, so its sign is (-1)^|A|. This is source (10)'s inside-expectation
formula, with all shared-line correlations retained by the linear functional. -/
theorem shiftedMoment_goodExpansion_eq (m : L → ℕ → ℝ) (r : L → ℕ)
    (G : Finset I) (path : I → J → L) :
    shiftedMoment m r (goodExpansion G path) =
      ∑ A ∈ G.powerset, (-1 : ℝ)^A.card * ∏ l, m l (r l+incidenceCount (G\A) path l) := by
  unfold shiftedMoment
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    goodExpansion, map_prod, pathExpansion_shift]
  rw [Finset.prod_sub, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.prod_const_one, mul_one]
  have he : (∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ((-1 : MvPolynomial L ℝ)^A.card *
        ∏ i ∈ G\A, ∏ j : J, X (path i j)) =
      (-1 : ℝ)^A.card • ((∏ l, (X l : MvPolynomial L ℝ)^r l) *
        ∏ i ∈ G\A, ∏ j : J, X (path i j)) := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
    ring
  rw [he, map_smul, tensorMoment_path_monomial, smul_eq_mul]

end CoordinateSweeps.MomentExpansion

/- Gamma-moment support. -/

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate), not an assumed random variable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

namespace CoordinateSweeps

theorem integral_gamma_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) =
      ∫ x in Ioi 0, (r^a / Gamma a * x^(a-1) * exp (-(r*x))) * f x := by
  rw [gammaMeasure]
  change (∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a r).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have he : (fun x => gammaPDFReal a r x * f x) =
      (Ici 0).indicator (fun x => (r^a / Gamma a * x^(a-1) * exp (-(r*x))) * f x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [gammaPDFReal, hx, indicator_of_mem, indicator_of_notMem]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_mgf {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    (∫ x, exp (t*x) ∂gammaMeasure a 1) = (1/(1-t))^a := by
  rw [integral_gamma_eq ha zero_lt_one]
  simp only [one_rpow, one_mul]
  have he : (fun x : ℝ => (1 / Gamma a * x^(a-1) * exp (-x)) * exp (t*x)) =
      fun x => (1 / Gamma a) * (x^(a-1) * exp (-((1-t)*x))) := by
    funext x
    rw [mul_assoc, mul_assoc, ← exp_add]
    congr 3
    ring
  rw [he, integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
  field_simp [(Gamma_pos_of_pos ha).ne']

theorem gamma_mgf_integrable {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    Integrable (fun x => exp (t*x)) (gammaMeasure a 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_mgf ha ht]
  exact (rpow_pos_of_pos (one_div_pos.mpr (sub_pos.mpr ht)) _).ne'

theorem gamma_centered_mgf {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    (∫ x, exp (t*(x-a)) ∂gammaMeasure a 1) = exp (a*(-t-log (1-t))) := by
  have he : (fun x => exp (t*(x-a))) = fun x => exp (-t*a) * exp (t*x) := by
    funext x
    rw [← exp_add]
    congr 1
    ring
  rw [he, integral_const_mul, gamma_mgf ha ht,
    rpow_def_of_pos (one_div_pos.mpr (sub_pos.mpr ht)), ← exp_add,
    one_div, log_inv]
  congr 1
  ring

theorem gamma_centered_mgf_integrable {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    Integrable (fun x => exp (t*(x-a))) (gammaMeasure a 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_centered_mgf ha ht]
  exact (exp_pos _).ne'

theorem log_mgf_bound {t : ℝ} (ht : |t| ≤ 1/2) : -t - log (1-t) ≤ 2*t^2 := by
  have ht1 : |t| < 1 := by linarith
  have hh := abs_log_sub_add_sum_range_le ht1 1
  norm_num at hh
  have hb : |t|^2 / (1-|t|) ≤ 2*t^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-|t|)).mpr
    rw [sq_abs]
    nlinarith [sq_nonneg t]
  rw [sq_abs] at hb
  have hl := neg_le_abs (t + log (1-t))
  linarith

theorem gamma_centered_mgf_le {a t : ℝ} (ha : 0 < a) (ht : |t| ≤ 1/2) :
    (∫ x, exp (t*(x-a)) ∂gammaMeasure a 1) ≤ exp (2*a*t^2) := by
  rw [gamma_centered_mgf ha (by have := le_abs_self t; linarith)]
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (log_mgf_bound ht) ha.le]

/- Pointwise exponential domination, used to obtain the actual centered
moments without a separate probabilistic Chernoff axiom. -/
theorem abs_pow_le_exp_sum (x : ℝ) (u : ℕ) {t : ℝ} (ht : 0 < t) :
    |x|^u ≤ ((u : ℝ)/t)^u * (exp (t*x) + exp (-t*x)) := by
  have hp := rpow_abs_le_mul_max_exp_of_pos x (Nat.cast_nonneg u) ht
  rw [rpow_natCast, rpow_natCast] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact max_le (le_add_of_nonneg_right (exp_nonneg _))
    (le_add_of_nonneg_left (exp_nonneg _))

theorem abs_pow_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (u : ℕ) {t : ℝ} (ht : 0 < t)
    (hp : Integrable (fun x => exp (t * X x)) μ)
    (hn : Integrable (fun x => exp (-t * X x)) μ) :
    Integrable (fun x => |X x|^u) μ := by
  apply ((hp.add hn).const_mul (((u : ℝ)/t)^u)).mono'
  · exact (hX.abs.pow_const u).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply] using abs_pow_le_exp_sum (X x) u ht

theorem abs_pow_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (u : ℕ) {t : ℝ} (ht : 0 < t)
    (hp : Integrable (fun x => exp (t * X x)) μ)
    (hn : Integrable (fun x => exp (-t * X x)) μ) :
    (∫ x, |X x|^u ∂μ) ≤ ((u : ℝ)/t)^u *
      ((∫ x, exp (t*X x) ∂μ) + (∫ x, exp (-t*X x) ∂μ)) := by
  calc
    _ ≤ ∫ x, ((u : ℝ)/t)^u * (exp (t*X x) + exp (-t*X x)) ∂μ :=
      integral_mono (abs_pow_integrable hX u ht hp hn)
        ((hp.add hn).const_mul _) (fun x => abs_pow_le_exp_sum (X x) u ht)
    _ = _ := by rw [integral_const_mul, integral_add hp hn]

/- A centered gamma moment in the range needed by every light line. -/
theorem gamma_abs_centered_moment_le {a : ℝ} (ha : 0 < a) {u : ℕ}
    (hu : 1 ≤ u) (hua : 4*(u : ℝ) ≤ a) :
    (∫ x, |x-a|^u ∂gammaMeasure a 1) ≤
      (2 * exp 2 * Real.sqrt (a*u))^u := by
  let t := Real.sqrt ((u : ℝ)/a)
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hu0 ha)
  have ht2 : t^2 = (u : ℝ)/a := Real.sq_sqrt (by positivity)
  have ht_half : t ≤ 1/2 := by
    have hh : (u : ℝ)/a ≤ 1/4 := (div_le_iff₀ ha).mpr (by linarith)
    nlinarith
  have htab : |t| ≤ 1/2 := by rw [abs_of_pos ht]; exact ht_half
  have hp := gamma_centered_mgf_integrable ha (show t < 1 by linarith)
  have hn := gamma_centered_mgf_integrable ha (show -t < 1 by linarith)
  have hh := abs_pow_integral_le
    (X := fun x : ℝ => x-a) (by fun_prop) u ht hp hn
  have hplus := gamma_centered_mgf_le ha htab
  have hminus := gamma_centered_mgf_le ha (t := -t) (by simpa only [abs_neg] using htab)
  have hat : a*t^2 = (u : ℝ) := by rw [ht2]; field_simp
  have hratio : (u : ℝ)/t = Real.sqrt (a*u) := by
    have ht0 : t ≠ 0 := ht.ne'
    have he : (u : ℝ)/t * ((u : ℝ)/t) = a*u := by
      field_simp
      nlinarith [hat]
    have hs := Real.sq_sqrt (show 0 ≤ a*(u : ℝ) by positivity)
    have hr : 0 ≤ (u : ℝ)/t := by positivity
    nlinarith [he, Real.sqrt_nonneg (a*u)]
  calc
    _ ≤ ((u : ℝ)/t)^u * (exp (2*a*t^2) + exp (2*a*(-t)^2)) :=
      hh.trans (mul_le_mul_of_nonneg_left (add_le_add hplus hminus) (by positivity))
    _ = 2 * (exp 2 * Real.sqrt (a*u))^u := by
      rw [hratio, neg_sq]
      have he : 2*a*t^2 = 2*(u : ℝ) := by nlinarith [hat]
      rw [he, mul_comm (2 : ℝ) (u : ℝ), exp_nat_mul, mul_pow]
      ring
    _ ≤ (2 * exp 2 * Real.sqrt (a*u))^u := by
      have htwo : (2 : ℝ) ≤ 2^u := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu)
      calc
        _ ≤ 2^u * (exp 2 * Real.sqrt (a*u))^u :=
          mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring

/- No restriction at the density's null endpoint is needed. -/
theorem integral_gamma_congr {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {f g : ℝ → ℝ} (hfg : ∀ x, 0 < x → f x = g x) :
    (∫ x, f x ∂gammaMeasure a r) = ∫ x, g x ∂gammaMeasure a r := by
  rw [integral_gamma_eq ha hr, integral_gamma_eq ha hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [hfg x hx]

/- The exact inverse-power density tilt used, with all gamma laws concrete. -/
theorem gamma_inverse_tilt {a m : ℝ} (k : ℕ) (hak : (k : ℝ) < a)
    (f : ℝ → ℝ) :
    (∫ x, (m/x)^k * f x ∂gammaMeasure a 1) =
      (m^k * Gamma (a-k) / Gamma a) * (∫ x, f x ∂gammaMeasure (a-k) 1) := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg k) hak
  have ha' : 0 < a-k := sub_pos.mpr hak
  rw [integral_gamma_eq ha zero_lt_one, integral_gamma_eq ha' zero_lt_one,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp : x^(a-1) = x^((a-k)-1) * x^k := by
    rw [← rpow_natCast x k, ← rpow_add hx]
    congr 1
    ring
  rw [hp]
  simp only [one_rpow, one_mul, div_pow]
  field_simp [(Gamma_pos_of_pos ha').ne', (Gamma_pos_of_pos ha).ne', hx0]

/- The gamma-ratio is the exact falling factorial, not an asymptotic. -/
theorem gamma_ratio_descFactorial {n k : ℕ} (hk : k ≤ n) :
    Gamma ((n : ℝ)+1-k) / Gamma ((n : ℝ)+1) = (n.descFactorial k : ℝ)⁻¹ := by
  have he : (n : ℝ)+1-k = (n-k : ℕ)+1 := by rw [Nat.cast_sub hk]; ring
  rw [he, Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
  have hh : ((n-k).factorial : ℝ) * (n.descFactorial k : ℝ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hnp : (n.factorial : ℝ) ≠ 0 := by positivity
  have hdp : (n.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  field_simp
  exact hh

/- The first equality of manuscript (11). -/
theorem gamma_light_line_identity {m h u v : ℕ} (hm : 0 < m) (huv : h+u+v ≤ m) :
    (∫ x, ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u
      ∂gammaMeasure ((m-h : ℕ)+1) 1) =
      ((m : ℝ)^(u+v) / ((m-h).descFactorial (u+v) : ℝ)) *
      (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure ((m-h : ℕ)+1-(u+v : ℕ)) 1) := by
  have hh : h ≤ m := by omega
  have hk : u+v ≤ m-h := by omega
  have ha : (0 : ℝ) < (m-h : ℕ)+1 := by positivity
  have hak : ((u+v : ℕ) : ℝ) < (m-h : ℕ)+1 := by exact_mod_cast (by omega : u+v < m-h+1)
  have he := integral_gamma_congr ha zero_lt_one
    (f := fun x => ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u)
    (g := fun x => ((m : ℝ)/x)^(u+v) * |1-x/(m : ℝ)|^u) (by
      intro x hx
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hx0 : x ≠ 0 := hx.ne'
      have hz : (m : ℝ)/x-1 = ((m : ℝ)/x)*(1-x/(m : ℝ)) := by
        field_simp
      rw [hz, abs_mul, abs_of_pos (div_pos (by exact_mod_cast hm) hx), mul_pow, pow_add]
      ring)
  rw [he, gamma_inverse_tilt (u+v) hak]
  rw [mul_div_assoc, gamma_ratio_descFactorial hk, ← div_eq_mul_inv]

/- Scale and bias estimate for the tilted gamma law. -/
theorem gamma_normalized_moment_le {a m η : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) {u : ℕ} (hu : 1 ≤ u)
    (hua : 4*(u : ℝ) ≤ a) (ham : a ≤ m) (huη : (u : ℝ) ≤ m*η)
    (hbias : |1-a/m| ≤ η) :
    (∫ x, |1-x/m|^u ∂gammaMeasure a 1) ≤
      (8 * exp 2 * Real.sqrt η)^u := by
  let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hηsqrt : η ≤ Real.sqrt η := by
    have hs := Real.sq_sqrt hη
    nlinarith [Real.sqrt_nonneg η]
  have hcenter : Integrable (fun x : ℝ => |x-a|^u) (gammaMeasure a 1) :=
    abs_pow_integrable (by fun_prop) u (t := 1/4) (by norm_num)
      (gamma_centered_mgf_integrable ha (by norm_num))
      (gamma_centered_mgf_integrable ha (by norm_num))
  have hratio : Real.sqrt (a*u)/m ≤ Real.sqrt η := by
    apply (div_le_iff₀ hm).mpr
    have hs := Real.sq_sqrt (show 0 ≤ a*(u : ℝ) by positivity)
    have hsη := Real.sq_sqrt hη
    have hp : a*(u : ℝ) ≤ m^2*η := by
      nlinarith [mul_le_mul_of_nonneg_right ham hu0,
        mul_le_mul_of_nonneg_left huη hm.le]
    have hsq : (Real.sqrt η*m)^2 = m^2*η := by nlinarith [hsη]
    nlinarith [Real.sqrt_nonneg (a*u), mul_nonneg (Real.sqrt_nonneg η) hm.le]
  let B := 2 * exp 2 * Real.sqrt η
  have he1 : (1 : ℝ) ≤ exp 2 := one_le_exp_iff.mpr (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsB : Real.sqrt η ≤ B := by dsimp [B]; nlinarith [Real.sqrt_nonneg η]
  have hcB : (2*exp 2*Real.sqrt (a*u))/m ≤ B := by
    calc
      _ = (2*exp 2)*(Real.sqrt (a*u)/m) := by ring
      _ ≤ B := mul_le_mul_of_nonneg_left hratio (by positivity)
  have hmoment : (m^u)⁻¹ * (∫ x, |x-a|^u ∂gammaMeasure a 1) ≤ B^u := by
    calc
      _ ≤ (m^u)⁻¹ * (2*exp 2*Real.sqrt (a*u))^u :=
        mul_le_mul_of_nonneg_left (gamma_abs_centered_moment_le ha hu hua) (by positivity)
      _ = ((2*exp 2*Real.sqrt (a*u))/m)^u := by rw [div_pow]; ring
      _ ≤ B^u := pow_le_pow_left₀ (by positivity) hcB u
  have hgint : Integrable (fun x : ℝ => (2 : ℝ)^u *
      ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u)) (gammaMeasure a 1) :=
    ((integrable_const _).add (hcenter.const_mul _)).const_mul _
  have hpt (x : ℝ) : |1-x/m|^u ≤ (2 : ℝ)^u *
      ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u) := by
    have hde : 1-x/m = (1-a/m) + (-(x-a))/m := by ring
    have hh : |1-x/m| ≤ Real.sqrt η + |x-a|/m := by
      rw [hde]
      apply (abs_add_le _ _).trans
      rw [abs_div, abs_neg, abs_of_pos hm]
      exact add_le_add (hbias.trans hηsqrt) le_rfl
    calc
      _ ≤ (Real.sqrt η + |x-a|/m)^u := pow_le_pow_left₀ (abs_nonneg _) hh u
      _ ≤ 2^(u-1) * ((Real.sqrt η)^u + (|x-a|/m)^u) :=
        add_pow_le (Real.sqrt_nonneg _) (by positivity) u
      _ ≤ 2^u * ((Real.sqrt η)^u + (|x-a|/m)^u) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ∫ x, (2 : ℝ)^u * ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u)
        ∂gammaMeasure a 1 := integral_mono_of_nonneg
      (ae_of_all _ (fun _ => by positivity)) hgint (ae_of_all _ hpt)
    _ = 2^u * ((Real.sqrt η)^u + (m^u)⁻¹ *
        (∫ x, |x-a|^u ∂gammaMeasure a 1)) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hcenter.const_mul _),
        integral_const, integral_const_mul]
      simp
    _ ≤ 2^u * (B^u + B^u) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsB _) hmoment
    _ ≤ (8*exp 2*Real.sqrt η)^u := by
      have htwo : (2 : ℝ) ≤ 2^u := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu)
      calc
        _ = 2^u * 2 * B^u := by ring
        _ ≤ 2^u * 2^u * B^u := by gcongr
        _ = (8*exp 2*Real.sqrt η)^u := by
          rw [← mul_pow, ← mul_pow]
          congr 1
          dsimp [B]
          ring

/- Uniform bound for the inverse-gamma prefactor, a light line cannot have
more than half of its sites assigned. -/
theorem light_prefactor_le {m h k : ℕ} (hm : 0 < m) (hk : 2*(h+k) ≤ m) :
    (m : ℝ)^k / ((m-h).descFactorial k : ℝ) ≤ 2^k := by
  have hkm : k ≤ m-h := by omega
  have hpos : (0 : ℝ) < (m-h).descFactorial k := by
    exact_mod_cast Nat.descFactorial_pos.mpr hkm
  apply (div_le_iff₀ hpos).mpr
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  calc
    (m : ℝ)^k = ∏ j ∈ Finset.range k, (m : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range k, (2 : ℝ)*(m-h-j : ℕ) := by
      apply Finset.prod_le_prod₀
      · intro _ _; positivity
      · intro j hj
        have hjk := Finset.mem_range.mp hj
        have hjm : j ≤ m-h := by omega
        rw [Nat.cast_sub hjm, Nat.cast_sub (show h ≤ m by omega)]
        have hn : (2 : ℝ)*(h+k) ≤ m := by exact_mod_cast hk
        have hjr : (j : ℝ) ≤ k := by exact_mod_cast (by omega : j ≤ k)
        nlinarith
    _ = 2^k * ∏ j ∈ Finset.range k, ((m-h-j : ℕ) : ℝ) := by
      rw [Finset.prod_mul_distrib]
      simp

/- The light-line estimate (11), with an explicit absolute constant. -/
theorem gamma_light_line_bound {m h u v : ℕ} (hm : 0 < m) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ)*η) :
    (∫ x, ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u
      ∂gammaMeasure ((m-h : ℕ)+1) 1) ≤
      (16 * exp 2)^(u+v) * (Real.sqrt η)^u := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have htot : ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ)/8 := by
    nlinarith [mul_le_mul_of_nonneg_left hηsmall hm0.le]
  have ht : h+u+v ≤ m := by
    exact_mod_cast (show ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ) by linarith)
  have ht2 : 2*(h+(u+v)) ≤ m := by
    have hh : (2 : ℝ)*(h+u+v) ≤ m := by push_cast at htot; linarith
    simpa only [Nat.add_assoc] using (show 2*(h+u+v) ≤ m by exact_mod_cast hh)
  have hh : h ≤ m := by omega
  let a : ℝ := (m-h : ℕ)+1-(u+v : ℕ)
  have hae : a = (m : ℝ)-(h+u+v : ℕ)+1 := by
    dsimp [a]
    rw [Nat.cast_sub hh]
    push_cast
    ring
  have ha : 0 < a := by rw [hae]; linarith
  have hnorm : (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure a 1) ≤
      (8 * exp 2 * Real.sqrt η)^u := by
    by_cases hu : u = 0
    · subst u
      let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha zero_lt_one
      simp
    · have hu1 : 1 ≤ u := by omega
      have huS : (u : ℝ) ≤ (h+u+v : ℕ) := by exact_mod_cast (by omega : u ≤ h+u+v)
      have hS1 : (1 : ℝ) ≤ (h+u+v : ℕ) := by exact_mod_cast (by omega : 1 ≤ h+u+v)
      have hua : 4*(u : ℝ) ≤ a := by rw [hae]; linarith
      have ham : a ≤ m := by rw [hae]; linarith
      apply gamma_normalized_moment_le ha hm0 hη (by linarith) hu1 hua ham (huS.trans hlight)
      have he : 1-a/(m : ℝ) = ((m : ℝ)-a)/m := by field_simp
      rw [he, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ham) hm0.le)]
      apply (div_le_iff₀ hm0).mpr
      rw [hae]
      linarith
  rw [gamma_light_line_identity hm ht]
  have hpre := light_prefactor_le hm ht2
  change _ * (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure a 1) ≤ _
  calc
    _ ≤ (2 : ℝ)^(u+v) * (8 * exp 2 * Real.sqrt η)^u := by
      apply mul_le_mul hpre hnorm
      · exact integral_nonneg (fun _ => by positivity)
      · positivity
    _ = 2^(u+v) * (8*exp 2)^u * (Real.sqrt η)^u := by rw [mul_pow]; ring
    _ ≤ 2^(u+v) * (8*exp 2)^(u+v) * (Real.sqrt η)^u := by
      have hC : (1 : ℝ) ≤ 8*exp 2 := by nlinarith [one_le_exp_iff.mpr (show (0 : ℝ) ≤ 2 by norm_num)]
      have hp := pow_le_pow_right₀ hC (Nat.le_add_right u v)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = (16 * exp 2)^(u+v) * (Real.sqrt η)^u := by
      rw [← mul_pow]
      congr 2
      ring

/- Exactly the power convention printed in manuscript (11). -/
theorem gamma_light_line_bound_rpow {m h u v : ℕ} (hm : 0 < m) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ)*η) :
    (∫ x, ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u
      ∂gammaMeasure ((m-h : ℕ)+1) 1) ≤
      (16 * exp 2)^(u+v) * η^((u : ℝ)/2) := by
  have he : (Real.sqrt η)^u = η^((u : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (η^(1/2 : ℝ)) u,
      ← Real.rpow_mul hη]
    congr 1
    ring
  simpa only [he] using gamma_light_line_bound hm hη hηsmall hlight

end CoordinateSweeps

namespace CoordinateSweeps.MomentExpansion
open MeasureTheory ProbabilityTheory Real

/- Source light-line factorial moment, with its exact finite-population shift. -/
def fallingMoment (m h n : ℕ) : ℝ := (m : ℝ)^n / ((m-h).descFactorial n : ℝ)

@[simp] theorem fallingMoment_zero (m h : ℕ) : fallingMoment m h 0 = 1 := by
  simp [fallingMoment]

/- The algebraic moment is the ACTUAL inverse-gamma moment in every used degree. -/
theorem fallingMoment_eq_integral {m h n : ℕ} (hn : n ≤ m-h) :
    fallingMoment m h n =
      ∫ x, ((m : ℝ)/x)^n ∂gammaMeasure ((m-h : ℕ)+1) 1 := by
  have hak : (n : ℝ) < (m-h : ℕ)+1 := by exact_mod_cast (by omega : n < m-h+1)
  have ha : (0 : ℝ) < (m-h : ℕ)+1-n := by linarith
  let : IsProbabilityMeasure (gammaMeasure ((m-h : ℕ)+1-n) 1) :=
    isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have he := gamma_inverse_tilt (m := (m : ℝ)) n hak (fun _ => (1 : ℝ))
  simp only [mul_one, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_div_assoc, gamma_ratio_descFactorial hn] at he
  simpa only [fallingMoment, div_eq_mul_inv] using he.symm

theorem fallingMoment_integrable {m h n : ℕ} (hm : 0 < m) (hn : n ≤ m-h) :
    Integrable (fun x => ((m : ℝ)/x)^n) (gammaMeasure ((m-h : ℕ)+1) 1) := by
  apply Integrable.of_integral_ne_zero
  rw [← fallingMoment_eq_integral hn]
  apply ne_of_gt
  unfold fallingMoment
  exact div_pos (pow_pos (by exact_mod_cast hm) _)
    (by exact_mod_cast Nat.descFactorial_pos.mpr hn)

/- Centered finite differences collect all occurrences of the SAME line. -/
theorem fallingCenteredMoment_eq_integral {L : Type*} (m h : L → ℕ) (l : L)
    (hm : 0 < m l) (v u : ℕ) (huv : v+u ≤ m l-h l) :
    lineCenteredMoment (fun l => fallingMoment (m l) (h l)) l v u =
      ∫ x, ((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
  have he (a : ℕ) (ha : a ∈ Finset.range (u+1)) :
      v+a ≤ m l-h l := by simp only [Finset.mem_range] at ha; omega
  have hi (a : ℕ) (ha : a ∈ Finset.range (u+1)) :
      Integrable (fun x => (-1 : ℝ)^(a+u) * (u.choose a : ℝ) * ((m l : ℝ)/x)^(v+a))
        (gammaMeasure ((m l-h l : ℕ)+1) 1) :=
    (fallingMoment_integrable hm (he a ha)).const_mul _
  unfold lineCenteredMoment
  have hs : (∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) *
      fallingMoment (m l) (h l) (v+a)) =
      ∫ x, ∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) *
        ((m l : ℝ)/x)^(v+a) ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
    rw [integral_finsetSum _ hi]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_const_mul, ← fallingMoment_eq_integral (he a ha)]
  rw [hs]
  congr 1
  funext x
  rw [sub_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_add]
  ring

/- Source (11) now applies directly to the exact finite-difference moment.
The gamma centered bound already existed; this bridge to Q's required moments is new. -/
theorem fallingCenteredMoment_abs_le {L : Type*} (m h : L → ℕ) (l : L)
    (hm : 0 < m l) (v u : ℕ) {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ((h l+u+v : ℕ) : ℝ) ≤ (m l : ℝ)*η) :
    |lineCenteredMoment (fun l => fallingMoment (m l) (h l)) l v u| ≤
      (16 * exp 2)^v * ((16 * exp 2)*Real.sqrt η)^u := by
  have huvn : h l+u+v ≤ m l := by
    have hm0 : (0 : ℝ) ≤ m l := Nat.cast_nonneg _
    have ht : (m l : ℝ)*η ≤ m l := mul_le_of_le_one_right hm0 (by linarith)
    exact_mod_cast hlight.trans ht
  rw [fallingCenteredMoment_eq_integral m h l hm v u (by omega)]
  have ha : (0 : ℝ) < (m l-h l : ℕ)+1 := by positivity
  have he : (∫ x, |((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u|
      ∂gammaMeasure ((m l-h l : ℕ)+1) 1) =
      ∫ x, ((m l : ℝ)/x)^v * |(m l : ℝ)/x-1|^u
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
    apply integral_gamma_congr ha zero_lt_one
    intro x hx
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le)]
  calc
    _ ≤ ∫ x, |((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u|
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => ((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u)
    _ = _ := he
    _ ≤ (16 * exp 2)^(u+v) * (Real.sqrt η)^u := gamma_light_line_bound hm hη hηsmall hlight
    _ = _ := by rw [pow_add, mul_pow]; ring

/- Actual inverse-gamma specialization of the shared-line expansion. -/
theorem goodExpansion_fallingMoment_le {L I J : Type*}
    [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]
    (m h r : L → ℕ) (hm : ∀ l, 0 < m l) (G : Finset I) (path : I → J → L)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ∀ l, ((h l+r l+(∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0) : ℕ) : ℝ)
      ≤ (m l : ℝ)*η) :
    |shiftedMoment (fun l => fallingMoment (m l) (h l)) r (goodExpansion G path)| ≤
      (16 * exp 2)^(∑ l, r l) * (1+16 * exp 2)^(Fintype.card J*G.card) *
        η^((G.card : ℝ)/2) := by
  have he := goodExpansion_moment_le (fun l => fallingMoment (m l) (h l))
    (fun l => fallingMoment_zero _ _) r G path (16*exp 2) (Real.sqrt η)
    (by positivity) (Real.sqrt_nonneg _) (by
      apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      linarith) (by
      intro l u hu
      apply fallingCenteredMoment_abs_le m h l (hm l) (r l) u hη hηsmall
      apply le_trans _ (hlight l)
      exact_mod_cast (show h l+u+r l ≤ h l+r l+∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0 by omega))
  have hs : (Real.sqrt η)^G.card = η^((G.card : ℝ)/2) := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hη]
    congr 1; ring
  simpa only [hs] using he

end CoordinateSweeps.MomentExpansion

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
