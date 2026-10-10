import OAI.Analysis.NumericalRange.OrderedMultiplication

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_61 u_62 u_63 u_64

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
section

variable {A : Type u_61} [Ring A] [Algebra ℂ A]

lemma aeval_nilpotent {N : A} {s : ℕ} (hs : N ^ s = 0) (p : ℂ[X]) :
    Polynomial.aeval N p = ∑ i ∈ range s, p.coeff i • N ^ i := by
  rw [Polynomial.aeval_eq_sum_range]
  rcases le_total (p.natDegree+1) s with h | h
  · apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hn
    have hi' : p.natDegree < i := by simpa using hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi', zero_smul]
  · symm
    apply Finset.sum_subset (Finset.range_mono h)
    intro i _ hn
    have hi' : s ≤ i := by simpa using hn
    rw [pow_eq_zero_of_le hi' hs, smul_zero]

lemma iteratedDeriv_polynomial (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z => p.eval z) = fun z => ((Polynomial.derivative^[k]) p).eval z := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun z => p.eval z) = fun z => p.derivative.eval z :=
      funext fun z => p.deriv
    rw [hd, ih]
    rfl

lemma taylor_coeff_iteratedDeriv (p : ℂ[X]) (β : ℂ) (k : ℕ) :
    (Polynomial.taylor β p).coeff k =
      iteratedDeriv k (fun z => p.eval z) β / (k.factorial : ℂ) := by
  rw [Polynomial.taylor_coeff, iteratedDeriv_polynomial]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).mpr
  have h := congrArg (fun q : ℂ[X] => q.eval β)
    (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) k) p)
  simpa [nsmul_eq_mul, mul_comm] using h

def scalarJetEval (β : ℂ) (N : A) (s : ℕ) (f : ℂ → ℂ) : A :=
  ∑ i ∈ range s, (iteratedDeriv i f β / (i.factorial : ℂ)) • N ^ i

lemma scalarJetEval_polynomial {N : A} {s : ℕ} (hs : N ^ s = 0)
    (β : ℂ) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval z) =
      Polynomial.aeval (N + algebraMap ℂ A β) p := by
  have he : Polynomial.aeval N (Polynomial.taylor β p) =
      Polynomial.aeval (N + algebraMap ℂ A β) p := by
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [← he, aeval_nilpotent hs]
  unfold scalarJetEval
  apply Finset.sum_congr rfl
  intro i _
  rw [taylor_coeff_iteratedDeriv]

lemma scalarJetEval_eventuallyEq {f g : ℂ → ℂ} {β : ℂ}
    (h : f =ᶠ[nhds β] g) (N : A) (s : ℕ) :
    scalarJetEval β N s f = scalarJetEval β N s g := by
  unfold scalarJetEval
  apply Finset.sum_congr rfl
  intro i _
  rw [h.iteratedDeriv_eq i]

lemma nilpotent_resolvent_product {N : A} {s : ℕ} (hs : N ^ s = 0)
    {c : ℂ} (hc : c ≠ 0) :
    (∑ i ∈ range s, (c⁻¹ ^ (i+1)) • N ^ i) * (algebraMap ℂ A c - N) = 1 := by
  let T : A := c⁻¹ • N
  have ht : T ^ s = 0 := by simp [T, _root_.smul_pow, hs]
  have hx : ∑ i ∈ range s, (c⁻¹ ^ (i+1)) • N ^ i =
      c⁻¹ • ∑ i ∈ range s, T ^ i := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [T, _root_.smul_pow, smul_smul, pow_succ']
  have hy : algebraMap ℂ A c - N = c • ((1 : A) - T) := by
    dsimp only [T]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
    simp only [Algebra.smul_def, mul_one]
  rw [hx, hy, smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul,
    geom_sum_mul_neg, ht, sub_zero]

lemma matrix_nilpotent_resolvent {n : Type u_62} [Fintype n] [DecidableEq n]
    {N : Matrix n n ℂ} {s : ℕ} (hs : N ^ s = 0) {z β : ℂ} (hz : z ≠ β) :
    (z • (1 : Matrix n n ℂ) - (β • 1 + N))⁻¹ =
      ∑ i ∈ range s, ((z-β)⁻¹ ^ (i+1)) • N ^ i := by
  apply Matrix.inv_eq_left_inv
  convert nilpotent_resolvent_product hs (sub_ne_zero.mpr hz) using 1
  congr 1
  simp only [Algebra.algebraMap_eq_smul_one, sub_smul]
  abel

def jetPolynomial (β : ℂ) (s : ℕ) (f : ℂ → ℂ) : ℂ[X] :=
  ∑ i ∈ range s, C (iteratedDeriv i f β / (i.factorial : ℂ)) * (X - C β) ^ i

lemma jetPolynomial_eval (β z : ℂ) (s : ℕ) (f : ℂ → ℂ) :
    (jetPolynomial β s f).eval z =
      ∑ i ∈ range s, ((z-β)^i / (i.factorial : ℂ)) * iteratedDeriv i f β := by
  simp only [jetPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma analytic_taylor_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (s : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z = (jetPolynomial β s f).eval z + (z-β)^s * R z := by
  have hshift : AnalyticAt ℂ (fun z => f (z+β)) 0 :=
    (show AnalyticAt ℂ f ((fun z : ℂ => z+β) 0) from by simpa using hf).comp
      (f := fun z : ℂ => z+β) (by fun_prop)
  obtain ⟨R, hR, hEq⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul s
  refine ⟨fun z => R (z-β), ?_, ?_⟩
  · exact (show AnalyticAt ℂ R ((fun z : ℂ => z-β) β) from by simpa using hR).comp
      (f := fun z : ℂ => z-β) (by fun_prop)
  · have ht : Filter.Tendsto (fun z : ℂ => z-β) (nhds β) (nhds 0) := by
      simpa only [ContinuousAt, sub_self] using
        (continuous_sub_right β).continuousAt (x := β)
    have he := ht.eventually hEq
    filter_upwards [he] with z hz
    simpa only [Function.comp_apply, sub_add_cancel, iteratedDeriv_comp_add_const,
      zero_add, smul_eq_mul, jetPolynomial_eval] using hz

lemma scalarJetEval_eq_of_remainder {f g R : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (hR : AnalyticAt ℂ R β)
    (N : A) (s : ℕ)
    (he : ∀ᶠ z in nhds β, f z - g z = (z-β)^s * R z) :
    scalarJetEval β N s f = scalarJetEval β N s g := by
  have hord : (s : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) β :=
    (natCast_le_analyticOrderAt (hf.fun_sub hg)).mpr ⟨R, hR, by simpa using he⟩
  have hd := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (hf.fun_sub hg)).mp hord
  apply Finset.sum_congr rfl
  intro i hi
  have h := hd i (Finset.mem_range.mp hi)
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, sub_eq_zero] at h
  rw [h]

lemma scalarJetEval_taylor {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s f = Polynomial.aeval (N + algebraMap ℂ A β)
      (jetPolynomial β s f) := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf s
  rw [← scalarJetEval_polynomial hs]
  apply scalarJetEval_eq_of_remainder hf
    (AnalyticOnNhd.eval_polynomial (jetPolynomial β s f) β (Set.mem_univ β)) hR
  filter_upwards [he] with z hz
  rw [hz]
  ring

lemma scalarJetEval_mul {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β)
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => f z * g z) =
      scalarJetEval β N s f * scalarJetEval β N s g := by
  let p := jetPolynomial β s f
  let q := jetPolynomial β s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf s
  obtain ⟨S, hS, hj⟩ := analytic_taylor_remainder hg s
  have hp : AnalyticAt ℂ (fun z => p.eval z) β :=
    AnalyticOnNhd.eval_polynomial p β (Set.mem_univ β)
  have hpq : AnalyticAt ℂ (fun z => (p*q).eval z) β :=
    AnalyticOnNhd.eval_polynomial (p*q) β (Set.mem_univ β)
  have hpoly : scalarJetEval β N s (fun z => f z * g z) =
      scalarJetEval β N s (fun z => (p*q).eval z) := by
    apply scalarJetEval_eq_of_remainder (hf.fun_mul hg) hpq
      (show AnalyticAt ℂ (fun z => R z * g z + p.eval z * S z) β from by fun_prop)
    filter_upwards [he, hj] with z hz hw
    change f z = p.eval z + (z-β)^s * R z at hz
    change g z = q.eval z + (z-β)^s * S z at hw
    simp only [Polynomial.eval_mul]
    rw [hz, hw]
    ring
  rw [hpoly, scalarJetEval_polynomial hs, map_mul,
    scalarJetEval_taylor hf hs, scalarJetEval_taylor hg hs]

lemma scalarJetEval_add {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z + g z) =
      scalarJetEval β N s f + scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,
    add_div, add_smul, Finset.sum_add_distrib]

lemma scalarJetEval_sub {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g β) (N : A) (s : ℕ) :
    scalarJetEval β N s (fun z => f z - g z) =
      scalarJetEval β N s f - scalarJetEval β N s g := by
  unfold scalarJetEval
  simp only [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt,
    sub_div, sub_smul, Finset.sum_sub_distrib]

lemma scalarJetEval_const {N : A} {s : ℕ} (hs : N^s = 0) (β c : ℂ) :
    scalarJetEval β N s (fun _ => c) = algebraMap ℂ A c := by
  simpa using scalarJetEval_polynomial hs β (C c)

lemma scalarJetEval_pow {f : ℂ → ℂ} {β : ℂ} (hf : AnalyticAt ℂ f β)
    {N : A} {s : ℕ} (hs : N^s = 0) (k : ℕ) :
    scalarJetEval β N s (fun z => f z ^ k) = (scalarJetEval β N s f) ^ k := by
  induction k with
  | zero => simpa using scalarJetEval_const hs β 1
  | succ k ih =>
    simp only [pow_succ]
    rw [scalarJetEval_mul (hf.fun_pow k) hf hs, ih]

lemma scalarJetEval_polynomial_comp {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) (p : ℂ[X]) :
    scalarJetEval β N s (fun z => p.eval (f z)) =
      Polynomial.aeval (scalarJetEval β N s f) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add, map_add]
    rw [scalarJetEval_add ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) ((AnalyticOnNhd.eval_polynomial q (f β) (Set.mem_univ _)).fun_comp hf), hp, hq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial, Polynomial.aeval_monomial]
    rw [scalarJetEval_mul (analyticAt_const ..) (hf.fun_pow k) hs,
      scalarJetEval_const hs, scalarJetEval_pow hf hs]

lemma analytic_first_order_remainder {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R β ∧ ∀ᶠ z in nhds β,
      f z - f β = (z-β)*R z := by
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hf 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [he] with z hz
  simpa [jetPolynomial_eval, sub_eq_iff_eq_add, add_comm] using hz

lemma scalarJetEval_nilpotent_part {f : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) {N : A} {s : ℕ} (hs : N^s = 0) :
    (scalarJetEval β N s f - algebraMap ℂ A (f β)) ^ s = 0 := by
  obtain ⟨R, hR, he⟩ := analytic_first_order_remainder hf
  have hzero : scalarJetEval β N s (fun z => (f z - f β)^s) =
      scalarJetEval β N s (fun _ => (0 : ℂ)) := by
    apply scalarJetEval_eq_of_remainder (by fun_prop) (analyticAt_const ..) (hR.fun_pow s)
    filter_upwards [he] with z hz
    rw [sub_zero, hz, mul_pow]
  rw [scalarJetEval_pow (by fun_prop) hs,
    scalarJetEval_sub hf (analyticAt_const ..), scalarJetEval_const hs,
    scalarJetEval_const hs, map_zero] at hzero
  exact hzero

lemma scalarJetEval_comp {f g : ℂ → ℂ} {β : ℂ}
    (hf : AnalyticAt ℂ f β) (hg : AnalyticAt ℂ g (f β))
    {N : A} {s : ℕ} (hs : N^s = 0) :
    scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval (f β) (scalarJetEval β N s f - algebraMap ℂ A (f β)) s g := by
  let p := jetPolynomial (f β) s g
  obtain ⟨R, hR, he⟩ := analytic_taylor_remainder hg s
  obtain ⟨S, hS, hj⟩ := analytic_first_order_remainder hf
  have hRp : AnalyticAt ℂ (fun z => S z ^ s * R (f z)) β :=
    (hS.fun_pow s).fun_mul (hR.fun_comp hf)
  have hpoly : scalarJetEval β N s (fun z => g (f z)) =
      scalarJetEval β N s (fun z => p.eval (f z)) := by
    apply scalarJetEval_eq_of_remainder (hg.fun_comp hf) ((AnalyticOnNhd.eval_polynomial p (f β) (Set.mem_univ _)).fun_comp hf) hRp
    filter_upwards [hf.continuousAt.eventually he, hj] with z hz hw
    change g (f z) = p.eval (f z) + (f z-f β)^s * R (f z) at hz
    rw [hz, hw, mul_pow]
    ring
  rw [hpoly, scalarJetEval_polynomial_comp hf hs,
    scalarJetEval_taylor hg (scalarJetEval_nilpotent_part hf hs), sub_add_cancel]

end

open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

noncomputable def primaryEquiv (T : Module.End ℂ V) :
    V ≃ₗ[ℂ] ⨁ β : ℂ, T.maxGenEigenspace β := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap T.maxGenEigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.independent_maxGenEigenspace T.iSup_maxGenEigenspace_eq_top)).symm

lemma primaryEquiv_coe (T : Module.End ℂ V) (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEquiv T (x : V) = DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x := by
  classical
  apply (primaryEquiv T).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (x : V) = DirectSum.coeLinearMap T.maxGenEigenspace
    (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x)
  simp

lemma primaryEquiv_symm_lof (T : Module.End ℂ V) (β : ℂ) (x : T.maxGenEigenspace β) :
    (primaryEquiv T).symm (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x) = x := by
  classical
  change DirectSum.coeLinearMap T.maxGenEigenspace
    (DirectSum.lof ℂ ℂ (fun β => T.maxGenEigenspace β) β x) = (x : V)
  simp

noncomputable def primaryNilpotent (T : Module.End ℂ V) (β : ℂ) :
    Module.End ℂ (T.maxGenEigenspace β) :=
  (T - algebraMap ℂ (Module.End ℂ V) β).restrict
    (fun x hx => T.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes T β) β (show x ∈ T.maxGenEigenspace β from hx))

lemma primaryNilpotent_pow (T : Module.End ℂ V) (β : ℂ) :
    primaryNilpotent T β ^ finrank ℂ V = 0 := by
  ext x
  have hx := x.property
  simp only [T.maxGenEigenspace_eq_genEigenspace_finrank β,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx
  dsimp only [primaryNilpotent]
  rw [Module.End.pow_restrict]
  change ((T - algebraMap ℂ (Module.End ℂ V) β) ^ finrank ℂ V) (x : V) = 0
  simpa only [Algebra.algebraMap_eq_smul_one] using hx

noncomputable def primaryEval (T : Module.End ℂ V) (f : ℂ → ℂ) : Module.End ℂ V :=
  (primaryEquiv T).symm.toLinearMap ∘ₗ
    (DirectSum.lmap fun β => scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f) ∘ₗ
      (primaryEquiv T).toLinearMap

lemma primaryEval_coe (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      ((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f x :
        T.maxGenEigenspace β) : V) := by
  classical
  simp only [primaryEval, LinearMap.comp_apply, LinearEquiv.coe_coe,
    primaryEquiv_coe, DirectSum.lmap_lof, primaryEquiv_symm_lof]

lemma primary_end_ext {T F G : Module.End ℂ V}
    (h : ∀ β (x : T.maxGenEigenspace β), F x = G x) : F = G := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ ⨆ β, T.maxGenEigenspace β := by rw [T.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun x => F x = G x) hx
    (fun β x hx => h β ⟨x,hx⟩) ?_ ?_
  · simp
  · intro x y hx hy
    simp [hx, hy]

lemma aeval_primary_restrict
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (β : ℂ) (p : ℂ[X])
    (x : T.maxGenEigenspace β) :
    ((Polynomial.aeval (primaryNilpotent T β +
      algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β) p) x : V) =
      (Polynomial.aeval T p) (x : V) := by
  have hid (y : T.maxGenEigenspace β) :
      ((primaryNilpotent T β + algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β) y : V) =
      T (y : V) := by
    change (T - algebraMap ℂ (Module.End ℂ V) β) (y : V) + β • (y : V) = T (y : V)
    simp [algebraMap_end_apply]
  have hpow (k : ℕ) (y : T.maxGenEigenspace β) :
      (((primaryNilpotent T β + algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) β)^k) y : V) =
      (T^k) (y : V) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, hid, ih]
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, hpow]

lemma primaryEval_polynomial (T : Module.End ℂ V) (p : ℂ[X]) :
    primaryEval T (fun z => p.eval z) = Polynomial.aeval T p := by
  apply primary_end_ext (T := T)
  intro β x
  rw [primaryEval_coe, scalarJetEval_polynomial (primaryNilpotent_pow T β)]
  exact aeval_primary_restrict T β p x

lemma primaryEval_mul (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g β) :
    primaryEval T (fun z => f z * g z) = primaryEval T f * primaryEval T g := by
  apply primary_end_ext (T := T)
  intro β x
  rw [Module.End.mul_apply, primaryEval_coe, primaryEval_coe, primaryEval_coe]
  by_cases hβ : β ∈ spectrum ℂ T
  · rw [scalarJetEval_mul (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β),
      Module.End.mul_apply]
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma scalarJetEval_intertwine
    {V : Type u_63} [AddCommGroup V] [_root_.Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type u_64} [AddCommGroup W] [Module ℂ W]
    (L : W →ₗ[ℂ] V) (S : Module.End ℂ W) (T : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (β : ℂ) (s : ℕ) (f : ℂ → ℂ) (x : W) :
    scalarJetEval β T s f (L x) = L (scalarJetEval β S s f x) := by
  have hp (k : ℕ) (x : W) : (T^k) (L x) = L ((S^k) x) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h,
        pow_succ', Module.End.mul_apply]
  simp only [scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hp]

lemma primaryEval_on_generalized (T : Module.End ℂ V) (f : ℂ → ℂ)
    (β : ℂ) (x : T.maxGenEigenspace β) :
    primaryEval T f (x : V) =
      scalarJetEval β (T - algebraMap ℂ (Module.End ℂ V) β) (finrank ℂ V) f (x : V) := by
  rw [primaryEval_coe]
  exact (scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    (primaryNilpotent T β) (T - algebraMap ℂ (Module.End ℂ V) β)
    (fun _ => rfl) β (finrank ℂ V) f x).symm

lemma primaryEval_mapsTo_generalized (T : Module.End ℂ V) {f : ℂ → ℂ}
    (β : ℂ) (hf : AnalyticAt ℂ f β) :
    MapsTo (T.maxGenEigenspace β).subtype Set.univ
      ((primaryEval T f).maxGenEigenspace (f β)) := by
  intro x _
  change (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β)
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
  have hp (k : ℕ) (x : T.maxGenEigenspace β) :
      ((primaryEval T f - algebraMap ℂ (Module.End ℂ V) (f β))^k) (x : V) =
        (((scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f -
          algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace β)) (f β))^k) x : V) := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
        primaryEval_coe, pow_succ', Module.End.mul_apply]
      rfl
  have he := hp (finrank ℂ V) x
  rw [scalarJetEval_nilpotent_part hf (primaryNilpotent_pow T β)] at he
  simpa only [Algebra.algebraMap_eq_smul_one,
    LinearMap.zero_apply, Submodule.coe_zero] using he

lemma primaryEval_comp (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g (f β)) :
    primaryEval T (fun z => g (f z)) = primaryEval (primaryEval T f) g := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · have hx : (x : V) ∈ (primaryEval T f).maxGenEigenspace (f β) :=
      primaryEval_mapsTo_generalized T β (hf β hβ) (by trivial : x ∈ Set.univ)
    rw [primaryEval_coe, primaryEval_on_generalized (primaryEval T f) g (f β) ⟨x, hx⟩]
    rw [scalarJetEval_comp (hf β hβ) (hg β hβ) (primaryNilpotent_pow T β)]
    symm
    apply scalarJetEval_intertwine (T.maxGenEigenspace β).subtype
    intro y
    change primaryEval T f (y : V) - (f β) • (y : V) = _
    rw [primaryEval_coe]
    rfl
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primary_end_ext_spectrum {T F G : Module.End ℂ V}
    (h : ∀ β ∈ spectrum ℂ T, ∀ x : T.maxGenEigenspace β, F x = G x) : F = G := by
  apply primary_end_ext (T := T)
  intro β x
  by_cases hβ : β ∈ spectrum ℂ T
  · exact h β hβ x
  · have hspace : T.maxGenEigenspace β = ⊥ := by
      by_contra hn
      have he : T.HasGenEigenvalue β (finrank ℂ V) := by
        rwa [T.maxGenEigenspace_eq_genEigenspace_finrank β] at hn
      exact hβ (Module.End.hasEigenvalue_of_hasGenEigenvalue he).mem_spectrum
    have hx : x = 0 := by
      apply Subtype.ext
      simpa [hspace] using x.property
    simp [hx]

lemma primaryEval_const (T : Module.End ℂ V) (c : ℂ) :
    primaryEval T (fun _ => c) = algebraMap ℂ (Module.End ℂ V) c := by
  simpa using primaryEval_polynomial T (C c)

lemma primaryEval_id (T : Module.End ℂ V) : primaryEval T id = T := by
  change primaryEval T (fun z => z) = T
  simpa using primaryEval_polynomial T (X : ℂ[X])

lemma primaryEval_sub (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β)
    (hg : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ g β) :
    primaryEval T (fun z => f z - g z) = primaryEval T f - primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  rw [LinearMap.sub_apply, primaryEval_coe, primaryEval_coe, primaryEval_coe,
    scalarJetEval_sub (hf β hβ) (hg β hβ)]
  rfl

lemma primaryEval_eventuallyEq (T : Module.End ℂ V) {f g : ℂ → ℂ}
    (h : ∀ β ∈ spectrum ℂ T, f =ᶠ[nhds β] g) :
    primaryEval T f = primaryEval T g := by
  apply primary_end_ext_spectrum (T := T)
  intro β hβ x
  rw [primaryEval_coe, primaryEval_coe, scalarJetEval_eventuallyEq (h β hβ)]

lemma primaryEval_spectrum_subset (T : Module.End ℂ V) {f : ℂ → ℂ}
    (hf : ∀ β ∈ spectrum ℂ T, AnalyticAt ℂ f β) :
    spectrum ℂ (primaryEval T f) ⊆ f '' spectrum ℂ T := by
  intro z hz
  by_contra hn
  have hne (β : ℂ) (hβ : β ∈ spectrum ℂ T) : z - f β ≠ 0 := by
    intro he
    exact hn ⟨β, hβ, (sub_eq_zero.mp he).symm⟩
  have ha (β : ℂ) (hβ : β ∈ spectrum ℂ T) :
      AnalyticAt ℂ (fun w => z - f w) β := (analyticAt_const ..).sub (hf β hβ)
  have hb (β : ℂ) (hβ : β ∈ spectrum ℂ T) :
      AnalyticAt ℂ (fun w => (z - f w)⁻¹) β := (ha β hβ).inv (hne β hβ)
  have he : primaryEval T (fun w => (z-f w) * (z-f w)⁻¹) = 1 := by
    rw [primaryEval_eventuallyEq T (g := fun _ => 1) ?_, primaryEval_const, map_one]
    intro β hβ
    filter_upwards [(ha β hβ).continuousAt.eventually_ne (hne β hβ)] with w hw
    exact mul_inv_cancel₀ hw
  rw [primaryEval_mul T ha hb,
    primaryEval_sub T (fun _ _ => analyticAt_const ..) hf, primaryEval_const] at he
  exact (spectrum.mem_iff.mp hz) (IsUnit.of_mul_eq_one _ he)

lemma primaryEval_intertwine (S T L : Module.End ℂ V)
    (h : ∀ x, T (L x) = L (S x)) (f : ℂ → ℂ) :
    primaryEval T f * L = L * primaryEval S f := by
  apply primary_end_ext (T := S)
  intro β x
  have hsub (y : V) :
      (T - algebraMap ℂ (Module.End ℂ V) β) (L y) =
        L ((S - algebraMap ℂ (Module.End ℂ V) β) y) := by
    simp only [LinearMap.sub_apply, algebraMap_end_apply, map_sub, map_smul, h]
  have hp (k : ℕ) (y : V) :
      ((T - algebraMap ℂ (Module.End ℂ V) β)^k) (L y) =
        L (((S - algebraMap ℂ (Module.End ℂ V) β)^k) y) := by
    induction k generalizing y with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hsub, pow_succ', Module.End.mul_apply]
  have hx : L (x : V) ∈ T.maxGenEigenspace β := by
    have he := x.property
    simp only [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at he ⊢
    simpa only [Algebra.algebraMap_eq_smul_one, he, map_zero] using hp (finrank ℂ V) x
  change primaryEval T f (L x) = L (primaryEval S f x)
  rw [primaryEval_on_generalized T f β ⟨L x, hx⟩, primaryEval_on_generalized S f β x]
  exact scalarJetEval_intertwine L _ _ hsub β (finrank ℂ V) f x

lemma primaryEval_similarity (T : Module.End ℂ V) (e : V ≃ₗ[ℂ] V) (f : ℂ → ℂ) :
    primaryEval (e.conj T) f = e.conj (primaryEval T f) := by
  have he := primaryEval_intertwine T (e.conj T) e.toLinearMap (by
    intro x
    simp) f
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun he (e.symm x)
  simpa using hx


end CompleteCrouzeix

end

end OAI
