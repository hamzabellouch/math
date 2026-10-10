import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros


namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {K σ τ : Type*} [CommSemiring K]
    (v : σ → MvPolynomial τ K) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (f : MvPolynomial σ K) : (MvPolynomial.aeval v f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hmul := totalDegree_mul (C (f.coeff d)) (d.prod fun i k => v i ^ k)
  simp only [totalDegree_C, zero_add] at hmul
  apply hmul.trans
  refine (totalDegree_finsetProd d.support (fun i => v i ^ d i)).trans ?_
  apply le_trans _ (le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i _
  simpa only [Nat.mul_one] using
    (totalDegree_pow (v i) (d i)).trans (Nat.mul_le_mul_left (d i) (hv i))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

noncomputable def linearShearHom (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (Fin.cases (X 0) (fun i => X i.succ + C (c i) * X 0))

@[simp] theorem linearShearHom_X_succ (c : Fin n → K) (i : Fin n) :
    linearShearHom c (X i.succ) = X i.succ + C (c i) * X 0 := by
  simp [linearShearHom]

theorem linearShearHom_comp_neg (c : Fin n → K) :
    (linearShearHom c).comp (linearShearHom (-c)) = AlgHom.id K _ := by
  ext i
  cases i using Fin.cases <;> simp [map_add, map_mul, linearShearHom]

noncomputable def linearShear (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (linearShearHom c) (linearShearHom (-c))
    (linearShearHom_comp_neg c) (by simpa using linearShearHom_comp_neg (-c))

theorem totalDegree_linearShear_le (c : Fin n → K) (f : MvPolynomial (Fin (n + 1)) K) :
    (linearShear c f).totalDegree ≤ f.totalDegree := by
  change (linearShearHom c f).totalDegree ≤ f.totalDegree
  apply WeightedTorusJets.Geometry.totalDegree_aeval_le_of_linear
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [Fin.cases_succ]
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    apply (totalDegree_mul _ _).trans
    simp

@[simp] theorem totalDegree_linearShear (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    (linearShear c f).totalDegree = f.totalDegree := by
  apply le_antisymm (totalDegree_linearShear_le c f)
  have h := totalDegree_linearShear_le (-c) (linearShear c f)
  have hc : linearShear (-c) (linearShear c f) = f := by
    exact congrArg (fun h : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K => h f)
      (by simpa using linearShearHom_comp_neg (-c))
  simpa only [hc] using h

theorem isHomogeneous_linearShear (c : Fin n → K)
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (linearShear c f).IsHomogeneous d := by
  change (linearShearHom c f).IsHomogeneous d
  have hvars : ∀ i : Fin (n + 1),
      (Fin.cases (X 0 : MvPolynomial (Fin (n + 1)) K)
        (fun j => X j.succ + C (c j) * X 0) i : MvPolynomial (Fin (n + 1)) K).IsHomogeneous 1 := by
    intro i
    cases i using Fin.cases with
    | zero => exact isHomogeneous_X K 0
    | succ i => exact (isHomogeneous_X K i.succ).add (isHomogeneous_C_mul_X _ _)
  simpa only [linearShearHom, one_mul] using hf.aeval _ hvars

theorem eval_mul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (a : K) (r : σ → K) :
    eval (fun i => a * r i) f = a ^ d * eval r f := by
  classical
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial e b he =>
    rw [eval_monomial, eval_monomial]
    simp_rw [mul_pow, Finsupp.prod_mul]
    have he' : e.sum (fun _ k => k) = d := by
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] using he
    have hp : e.prod (fun _ k => a ^ k) = a ^ d := by
      simpa only [Finsupp.prod, Finsupp.sum, Finset.prod_pow_eq_pow_sum] using congrArg (fun k => a ^ k) he'
    rw [hp]
    ring

theorem exists_eval_cons_one_ne_zero [Infinite K]
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) f ≠ 0 := by
  have hxf : (X 0 : MvPolynomial (Fin (n + 1)) K) * f ≠ 0 :=
    mul_ne_zero (X_ne_zero _) hf0
  obtain ⟨r, hr⟩ : ∃ r : Fin (n + 1) → K, eval r (X 0 * f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hxf (((isHomogeneous_X K 0).mul hf).eq_zero_of_forall_eval_eq_zero h)
  have hrs : r 0 ≠ 0 ∧ eval r f ≠ 0 := by
    simpa only [map_mul, eval_X, mul_ne_zero_iff] using hr
  have hr0 := hrs.1
  have hrf := hrs.2
  refine ⟨fun i => (r 0)⁻¹ * r i.succ, ?_⟩
  have hc : Fin.cons 1 (fun i => (r 0)⁻¹ * r i.succ) =
      fun i => (r 0)⁻¹ * r i := by
    funext i
    cases i using Fin.cases <;> simp [hr0]
  rw [hc, eval_mul_of_isHomogeneous hf]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hr0)) hrf

theorem homogeneousComponent_linearShear (c : Fin n → K)
    (d : ℕ) (f : MvPolynomial (Fin (n + 1)) K) :
    homogeneousComponent d (linearShear c f) =
      linearShear c (homogeneousComponent d f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [homogeneousComponent_of_mem
      (isHomogeneous_linearShear c (isHomogeneous_monomial b rfl)),
      homogeneousComponent_of_mem (isHomogeneous_monomial b rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem eval_cons_one_zero_of_isHomogeneous
    {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    eval (Fin.cons 1 0) f =
      constantCoeff ((finSuccEquiv K n f).coeff d) := by
  have hdeg : (finSuccEquiv K n f).natDegree < d + 1 := by
    have ht := hf.totalDegree_le
    have h := degreeOf_le_totalDegree f 0
    rw [← natDegree_finSuccEquiv f] at h
    omega
  have aux : ∀ i ∈ Finset.range d,
      constantCoeff ((finSuccEquiv K n f).coeff i) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply (hf.finSuccEquiv_coeff_isHomogeneous i (d - i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  simp_rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map,
    Polynomial.eval_eq_sum_range' hdeg, eval_zero, one_pow, mul_one, map_sum,
    Finset.sum_range_succ, Finset.sum_eq_zero aux, zero_add]

theorem eval_cons_one_zero_linearShear (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    eval (Fin.cons 1 0) (linearShear c f) = eval (Fin.cons 1 c) f := by
  have h : (eval (Fin.cons 1 0)).comp (linearShearHom c).toRingHom =
      eval (Fin.cons 1 c) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [linearShearHom]
    · intro i
      cases i using Fin.cases <;> simp [linearShearHom]
  exact congrArg (fun g : MvPolynomial (Fin (n + 1)) K →+* K => g f) h

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal Polynomial RingHom
variable {K : Type*} [Field K] {n : ℕ}

theorem algEquiv_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) : e.toAlgHom.IsIntegral :=
  RingHom.isIntegral_of_surjective e.toAlgHom.toRingHom e.surjective

theorem isUnit_leadingCoeff_finSuccEquiv_of_full_degree
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f ≠ 0)
    (hd : degreeOf 0 f = f.totalDegree) :
    IsUnit (finSuccEquiv K n f).leadingCoeff := by
  have hp : finSuccEquiv K n f ≠ 0 := by
    intro h
    exact hf ((finSuccEquiv K n).injective (by simpa using h))
  have hnd : (finSuccEquiv K n f).natDegree = f.totalDegree := by
    simpa only [natDegree_finSuccEquiv] using hd
  have hl : (finSuccEquiv K n f).coeff f.totalDegree ≠ 0 := by
    rw [← hnd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  have ht := totalDegree_coeff_finSuccEquiv_add_le f f.totalDegree hl
  have hz : ((finSuccEquiv K n f).coeff f.totalDegree).totalDegree = 0 := by omega
  have he := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : ((finSuccEquiv K n f).coeff f.totalDegree).coeff 0 ≠ 0 := by
    intro hc
    exact hl (by rw [he, hc, map_zero])
  rw [← coeff_natDegree, hnd, he]
  exact hc.isUnit.map MvPolynomial.C

noncomputable def eliminationEquiv (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  (linearShear c).trans (finSuccEquiv K n)

noncomputable def eliminationIdeal (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Ideal (Polynomial (MvPolynomial (Fin n) K)) := I.map (eliminationEquiv c)

noncomputable def eliminationQuotientEquiv (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    (Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I) ≃ₐ[K]
      MvPolynomial (Fin (n + 1)) K ⧸ I :=
  Ideal.quotientEquivAlg _ I (eliminationEquiv c).symm (by
    change I = Ideal.map (eliminationEquiv c).symm.toRingEquiv.toRingHom
      (Ideal.map (eliminationEquiv c).toRingEquiv.toRingHom I)
    rw [Ideal.map_map]
    have hc : (eliminationEquiv c).symm.toRingEquiv.toRingHom.comp
        (eliminationEquiv c).toRingEquiv.toRingHom = RingHom.id _ :=
      (eliminationEquiv c).toRingEquiv.symm_toRingHom_comp_toRingHom
    rw [hc, Ideal.map_id])

noncomputable def eliminationBaseHom (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    MvPolynomial (Fin n) K →ₐ[MvPolynomial (Fin n) K]
      Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I :=
  (Ideal.Quotient.mkₐ _ _).comp (Algebra.ofId _ _)

noncomputable def eliminationHom (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K ⧸ I :=
  (eliminationQuotientEquiv c I).toAlgHom.comp
    ((eliminationBaseHom c I).restrictScalars K)

theorem eliminationHom_isIntegral (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f ≠ 0) (hfi : f ∈ I)
    (hd : degreeOf 0 (linearShear c f) = f.totalDegree) :
    (eliminationHom c I).IsIntegral := by
  have hsf : linearShear c f ≠ 0 := by
    intro h
    exact hf ((linearShear c).injective (by simpa using h))
  have hu := isUnit_leadingCoeff_finSuccEquiv_of_full_degree hsf
    (by simpa only [totalDegree_linearShear] using hd)
  have hb : (eliminationBaseHom c I).IsIntegral := by
    exact (monic_of_isUnit_leadingCoeff_inv_smul hu).quotient_isIntegral
      (Submodule.smul_of_tower_mem _ hu.unit⁻¹.val (Ideal.mem_map_of_mem _ hfi))
  have he := algEquiv_isIntegral
    (A := Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I)
    (B := MvPolynomial (Fin (n + 1)) K ⧸ I) (eliminationQuotientEquiv c I)
  exact hb.trans _ _ he

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
variable {K : Type*} [Field K] {n : ℕ}

@[simp] theorem linearShear_apply_neg (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    linearShear c (linearShear (-c) f) = f := by
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) K →ₐ[K]
    MvPolynomial (Fin (n + 1)) K => h f) (linearShearHom_comp_neg c)

@[simp] theorem eliminationQuotientEquiv_mk (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (p : Polynomial (MvPolynomial (Fin n) K)) :
    eliminationQuotientEquiv c I (Ideal.Quotient.mk (eliminationIdeal c I) p) =
      Ideal.Quotient.mk I ((eliminationEquiv c).symm p) := by
  simp only [eliminationQuotientEquiv, Ideal.quotientEquivAlg_mk]

theorem eliminationHom_apply_raw (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (p : MvPolynomial (Fin n) K) :
    eliminationHom c I p = Ideal.Quotient.mk I
      ((eliminationEquiv c).symm (Polynomial.C p)) := by
  exact eliminationQuotientEquiv_mk c I (Polynomial.C p)

theorem eliminationEquiv_linearShear_neg (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    eliminationEquiv c (linearShear (-c) f) = finSuccEquiv K n f := by
  rw [eliminationEquiv, AlgEquiv.trans_apply, linearShear_apply_neg]

theorem eliminationEquiv_symm_C_X (c : Fin n → K) (i : Fin n) :
    (eliminationEquiv c).symm (Polynomial.C (MvPolynomial.X i)) =
      linearShear (-c) (MvPolynomial.X i.succ) := by
  apply (eliminationEquiv c).symm_apply_eq.mpr
  rw [eliminationEquiv_linearShear_neg, finSuccEquiv_X_succ]

@[simp] theorem eliminationHom_X (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (i : Fin n) :
    eliminationHom c I (MvPolynomial.X i) =
      Ideal.Quotient.mk I (linearShear (-c) (MvPolynomial.X i.succ)) := by
  rw [eliminationHom_apply_raw, eliminationEquiv_symm_C_X]

theorem eliminationHom_apply (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (p : MvPolynomial (Fin n) K) :
    eliminationHom c I p =
      Ideal.Quotient.mk I (linearShear (-c) (MvPolynomial.rename Fin.succ p)) := by
  have h : eliminationHom c I = (Ideal.Quotient.mkₐ K I).comp
      ((linearShear (-c)).toAlgHom.comp (MvPolynomial.rename Fin.succ)) := by
    ext i
    simp only [eliminationHom_X, AlgHom.comp_apply, rename_X,
      AlgEquiv.coe_toAlgHom, Quotient.mkₐ_eq_mk]
  exact congrArg (fun g : MvPolynomial (Fin n) K →ₐ[K]
    MvPolynomial (Fin (n + 1)) K ⧸ I => g p) h

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.Geometry

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_homogeneous_relation_not_dvd_coordinate
    {R σ : Type*} [CommRing R] [IsDomain R]
    (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ R)) (hP0 : P ≠ ⊥)
    (i : σ) (hi : X i ∉ P) :
    ∃ (n : ℕ) (f : MvPolynomial σ R),
      f ≠ 0 ∧ f ∈ P ∧ f.IsHomogeneous n ∧ ¬ X i ∣ f := by
  classical
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hex : ∃ n : ℕ, ∃ f : MvPolynomial σ R,
      f ∈ P ∧ f ≠ 0 ∧ f.totalDegree = n := ⟨a.totalDegree, a, haP, ha0, rfl⟩
  obtain ⟨f, hfP, hf0, hfdeg⟩ := Nat.find_spec hex
  obtain ⟨n, hn, hn0⟩ : ∃ n ∈ Finset.range (f.totalDegree + 1),
      homogeneousComponent n f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    rw [← sum_homogeneousComponent f]
    exact Finset.sum_eq_zero h
  have hnP := homogeneousComponent_mem_of_mem hP hfP n
  have hhom := homogeneousComponent_isHomogeneous n f
  refine ⟨n, homogeneousComponent n f, hn0, hnP, hhom, ?_⟩
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro hzero
    apply hn0
    rw [hg, hzero, mul_zero]
  have hgP : g ∈ P :=
    (Ideal.IsPrime.mem_or_mem inferInstance (hg ▸ hnP)).resolve_left hi
  have hmin := Nat.find_min' hex ⟨g, hgP, hg0, rfl⟩
  have hdeg := congrArg MvPolynomial.totalDegree hg
  rw [hhom.totalDegree hn0, totalDegree_mul_of_isDomain (X_ne_zero i) hg0,
    totalDegree_X] at hdeg
  have hnle : n ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  omega

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem coordinate_dvd_sub_aeval_update_zero
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ R) :
    X i ∣ p - aeval (Function.update (X (R := R)) i 0) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    by_cases hji : j = i
    · subst j
      simp only [map_mul, aeval_X, Function.update_self, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · simp only [map_mul, aeval_X, Function.update_of_ne hji]
      rw [← sub_mul]
      exact dvd_mul_of_dvd_left hp _

theorem aeval_update_zero_eq_zero_iff
    {R σ : Type*} [CommRing R] [DecidableEq σ]
    (i : σ) (p : MvPolynomial σ R) :
    aeval (Function.update (X (R := R)) i 0) p = 0 ↔ X i ∣ p := by
  constructor
  · intro h
    simpa only [h, sub_zero] using coordinate_dvd_sub_aeval_update_zero i p
  · rintro ⟨q, rfl⟩
    simp

theorem isHomogeneous_aeval_update_zero
    {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (aeval (Function.update (X (R := R)) i 0) p).IsHomogeneous n := by
  simpa only [one_mul] using hp.aeval (n := 1) (Function.update (X (R := R)) i 0)
    (fun j => by
      by_cases h : j = i
      · subst j
        simpa only [Function.update_self] using isHomogeneous_zero (R := R) (σ := σ) 1
      · simpa only [Function.update_of_ne h] using isHomogeneous_X R j)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial
variable {K : Type*} [Field K] {n : ℕ}

theorem eval_aeval_update_zero {σ : Type*} [DecidableEq σ]
    (i : σ) (r : σ → K) (f : MvPolynomial σ K) :
    eval r (aeval (Function.update (X (R := K)) i 0) f) =
      eval (Function.update r i 0) f := by
  have h : (eval r).comp (aeval (Function.update (X (R := K)) i 0)).toRingHom =
      eval (Function.update r i 0) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp
    · intro j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hji]
  exact congrArg (fun g : MvPolynomial σ K →+* K => g f) h

theorem exists_eval_cons_one_with_zero [Infinite K]
    (j : Fin n) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hnot : ¬ X j.succ ∣ f) :
    ∃ c : Fin n → K, c j = 0 ∧ eval (Fin.cons 1 c) f ≠ 0 := by
  have hne : aeval (Function.update (X (R := K)) j.succ 0) f ≠ 0 :=
    (WeightedTorusJets.Geometry.aeval_update_zero_eq_zero_iff j.succ f).not.mpr hnot
  obtain ⟨c, hc⟩ := exists_eval_cons_one_ne_zero
    (WeightedTorusJets.Geometry.isHomogeneous_aeval_update_zero j.succ hf) hne
  refine ⟨Function.update c j 0, Function.update_self j 0 c, ?_⟩
  have hvec : Function.update (Fin.cons 1 c : Fin (n + 1) → K) j.succ 0 =
      (Fin.cons 1 (Function.update c j 0) : Fin (n + 1) → K) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    | succ i => simp [Function.update_apply, Fin.succ_inj]
  rwa [eval_aeval_update_zero, hvec] at hc

theorem degreeOf_linearShear_eq_of_isHomogeneous
    (c : Fin n → K) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (heval : eval (Fin.cons 1 c) f ≠ 0) :
    degreeOf 0 (linearShear c f) = f.totalDegree := by
  have hf0 : f ≠ 0 := by
    intro h
    exact heval (by simp [h])
  have htd := hf.totalDegree hf0
  apply le_antisymm
  · simpa only [totalDegree_linearShear] using degreeOf_le_totalDegree (linearShear c f) 0
  · rw [← eval_cons_one_zero_linearShear, eval_cons_one_zero_of_isHomogeneous
      (isHomogeneous_linearShear c hf), constantCoeff_eq, finSuccEquiv_coeff_coeff] at heval
    have hdeg := le_degreeOf_of_mem_support 0 (mem_support_iff.mpr heval)
    simpa only [Finsupp.cons_zero, htd] using hdeg

theorem exists_linearShear_fix_coordinate_full [Infinite K]
    (j : Fin n) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hnot : ¬ X j.succ ∣ f) :
    ∃ c : Fin n → K, c j = 0 ∧
      degreeOf 0 (linearShear c f) = f.totalDegree ∧
      linearShear c (X j.succ) = X j.succ := by
  obtain ⟨c, hc, hv⟩ := exists_eval_cons_one_with_zero j hf hnot
  refine ⟨c, hc, degreeOf_linearShear_eq_of_isHomogeneous c hf hv, ?_⟩
  change linearShearHom c (X j.succ) = X j.succ
  simp [hc]

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {n : ℕ}

theorem eliminationKer_isHomogeneous (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K)) :
    (RingHom.ker (eliminationHom c I)).IsHomogeneous
      (homogeneousSubmodule (Fin n) K) := by
  intro d p hp
  rw [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply]
  have hpI : linearShear (-c) (MvPolynomial.rename Fin.succ p) ∈ I := by
    have hp0 : eliminationHom c I p = 0 := hp
    rw [eliminationHom_apply, Ideal.Quotient.eq_zero_iff_mem] at hp0
    exact hp0
  have hd := homogeneousComponent_mem_of_mem hI hpI d
  rw [homogeneousComponent_linearShear, ← rename_homogeneousComponent] at hd
  change eliminationHom c I (homogeneousComponent d p) = 0
  rw [eliminationHom_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact hd

theorem homogeneous_prime_finOne_eq_bot
    (P : Ideal (MvPolynomial (Fin 1) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin 1) K))
    (hX : X (0 : Fin 1) ∉ P) : P = ⊥ := by
  by_contra hP0
  obtain ⟨d, f, hf0, hfP, hf, hnot⟩ :=
    WeightedTorusJets.Geometry.exists_homogeneous_relation_not_dvd_coordinate P hP hP0 0 hX
  have hne : aeval (Function.update (X (R := K)) (0 : Fin 1) 0) f ≠ 0 :=
    (WeightedTorusJets.Geometry.aeval_update_zero_eq_zero_iff 0 f).not.mpr hnot
  have hu : Function.update (X (R := K)) (0 : Fin 1) 0 =
      (0 : Fin 1 → MvPolynomial (Fin 1) K) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  have hc : f.coeff 0 ≠ 0 := by
    intro hc
    apply hne
    rw [hu, aeval_zero, constantCoeff_eq, hc, map_zero]
  have hd : d = 0 := by
    have hd' := hf hc
    simpa only [map_zero] using hd'.symm
  subst d
  have he : f = C (f.coeff 0) := by
    simpa only [homogeneousComponent_zero] using (homogeneousComponent_eq_self hf).symm
  exact (Ideal.IsPrime.ne_top inferInstance)
    (P.eq_top_of_isUnit_mem hfP (he ▸ hc.isUnit.map MvPolynomial.C))

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem exists_integral_injective_linear_quotient_fixed_last [Infinite K]
    {n : ℕ} (P : Ideal (MvPolynomial (Fin (n + 1)) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (hX : X (Fin.last n) ∉ P) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K]
      (MvPolynomial (Fin (n + 1)) K ⧸ P),
      Function.Injective g ∧ g.IsIntegral ∧
      (∀ i, ∃ l : MvPolynomial (Fin (n + 1)) K,
        l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l) ∧
      g (X (Fin.last s)) = Ideal.Quotient.mk P (X (Fin.last n)) := by
  induction n with
  | zero =>
    have hP0 : P = ⊥ := homogeneous_prime_finOne_eq_bot P hP hX
    have hbij : Function.Bijective (Ideal.Quotient.mkₐ K P) :=
      (Ideal.Quotient.mk_bijective_iff_eq_bot P).mpr hP0
    exact ⟨0, le_rfl, Ideal.Quotient.mkₐ K P, hbij.1,
      RingHom.isIntegral_of_surjective _ hbij.2,
      fun i => ⟨MvPolynomial.X i, isHomogeneous_X K i, rfl⟩, rfl⟩
  | succ n ih =>
    by_cases hP0 : P = ⊥
    · have hbij : Function.Bijective (Ideal.Quotient.mkₐ K P) :=
        (Ideal.Quotient.mk_bijective_iff_eq_bot P).mpr hP0
      exact ⟨n + 1, le_rfl, Ideal.Quotient.mkₐ K P, hbij.1,
        RingHom.isIntegral_of_surjective _ hbij.2,
        fun i => ⟨MvPolynomial.X i, isHomogeneous_X K i, rfl⟩, rfl⟩
    · obtain ⟨d, f, hf0, hfP, hf, hnot⟩ :=
        WeightedTorusJets.Geometry.exists_homogeneous_relation_not_dvd_coordinate
          P hP hP0 (Fin.last (n + 1)) hX
      obtain ⟨c, hc, hdeg, _⟩ := exists_linearShear_fix_coordinate_full (Fin.last n) hf
        (by simpa using hnot)
      have hfix : linearShear (-c) (X (Fin.last n).succ) = X (Fin.last (n + 1)) := by
        change linearShearHom (-c) (X (Fin.last n).succ) = _
        rw [linearShearHom_X_succ]
        simp [hc]
      let e := eliminationHom c P
      let J := RingHom.ker e
      let φ := Ideal.kerLiftAlg e
      let : J.IsPrime := RingHom.ker_isPrime e
      have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
        eliminationKer_isHomogeneous c P hP
      have hXJ : X (Fin.last n) ∉ J := by
        intro hx
        have hx0 : e (X (Fin.last n)) = 0 := hx
        change eliminationHom c P (X (Fin.last n)) = 0 at hx0
        rw [eliminationHom_X, hfix, Ideal.Quotient.eq_zero_iff_mem] at hx0
        exact hX hx0
      obtain ⟨s, hs, g, hinj, hint, hlin, hlast⟩ := ih J hJ hXJ
      refine ⟨s, Nat.le_succ_of_le hs, φ.comp g, ?_, ?_, ?_, ?_⟩
      · exact (φ.coe_comp g) ▸ (Ideal.kerLiftAlg_injective e).comp hinj
      · exact hint.trans g.toRingHom φ.toRingHom
          (eliminationHom_isIntegral c P hf0 hfP hdeg).kerLift
      · intro i
        obtain ⟨l, hl, hgl⟩ := hlin i
        refine ⟨linearShear (-c) (MvPolynomial.rename Fin.succ l),
          isHomogeneous_linearShear (-c) hl.rename_isHomogeneous, ?_⟩
        rw [AlgHom.comp_apply, hgl]
        change e l = _
        exact eliminationHom_apply c P l
      · rw [AlgHom.comp_apply, hlast]
        change eliminationHom c P (X (Fin.last n)) = _
        rw [eliminationHom_X, hfix]

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem exists_integral_injective_linear_quotient_fixed_coordinate [Infinite K]
    {n : ℕ} (P : Ideal (MvPolynomial (Fin (n + 1)) K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K))
    (i : Fin (n + 1)) (hX : X i ∉ P) :
    ∃ s ≤ n, ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K]
      (MvPolynomial (Fin (n + 1)) K ⧸ P),
      Function.Injective g ∧ g.IsIntegral ∧
      (∀ j, ∃ l : MvPolynomial (Fin (n + 1)) K,
        l.IsHomogeneous 1 ∧ g (MvPolynomial.X j) = Ideal.Quotient.mk P l) ∧
      g (X 0) = Ideal.Quotient.mk P (X i) := by
  classical
  let e := MvPolynomial.renameEquiv K (Equiv.swap i (Fin.last n))
  let J := Ideal.comap e.toAlgHom.toRingHom P
  let : J.IsPrime := Ideal.comap_isPrime e.toAlgHom.toRingHom P
  have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
    intro d p hp
    rw [← DirectSum.Decomposition.decompose'_eq,
      MvPolynomial.decomposition.decompose'_apply]
    change MvPolynomial.rename (Equiv.swap i (Fin.last n)) (homogeneousComponent d p) ∈ P
    rw [MvPolynomial.rename_homogeneousComponent]
    exact homogeneousComponent_mem_of_mem hP hp d
  have hlast : X (Fin.last n) ∉ J := by
    change e (X (Fin.last n)) ∉ P
    simpa only [e, renameEquiv_apply, rename_X, Equiv.swap_apply_right] using hX
  have hIJ : P = J.map e.toAlgHom.toRingHom :=
    (Ideal.map_comap_of_surjective e.toAlgHom.toRingHom e.surjective P).symm
  let E := Ideal.quotientEquivAlg J P e hIJ
  have hE : ∀ p, E (Ideal.Quotient.mk J p) = Ideal.Quotient.mk P (e p) := by
    intro p
    exact Ideal.quotientEquivAlg_mk (I := J) (J := P) e hIJ p
  obtain ⟨s, hs, g, hinj, hint, hlin, hfix⟩ :=
    exists_integral_injective_linear_quotient_fixed_last J hJ hlast
  let r := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin (s + 1)) (Fin.last s))
  refine ⟨s, hs, E.toAlgHom.comp (g.comp r.toAlgHom), ?_, ?_, ?_, ?_⟩
  · exact E.injective.comp (hinj.comp r.injective)
  · have hrint := algEquiv_isIntegral r
    have hEint := algEquiv_isIntegral
      (A := MvPolynomial (Fin (n + 1)) K ⧸ J)
      (B := MvPolynomial (Fin (n + 1)) K ⧸ P) E
    exact (hrint.trans r.toAlgHom.toRingHom g.toRingHom hint).trans _ _ hEint
  · intro j
    obtain ⟨l, hl, hgl⟩ := hlin ((Equiv.swap (0 : Fin (s + 1)) (Fin.last s)) j)
    refine ⟨e l, hl.rename_isHomogeneous, ?_⟩
    change E (g (r (X j))) = Ideal.Quotient.mk P (e l)
    simp only [r, renameEquiv_apply, rename_X]
    rw [hgl]
    exact hE l
  · change E (g (r (X 0))) = Ideal.Quotient.mk P (X i)
    simp only [r, renameEquiv_apply, rename_X, Equiv.swap_apply_left]
    rw [hfix, hE]
    simp only [e, renameEquiv_apply, rename_X, Equiv.swap_apply_right]

theorem finite_of_integral_quotient {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I))
    (hint : g.IsIntegral) : g.Finite := by
  let : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  have h : algebraMap K (MvPolynomial (Fin n) K ⧸ I) =
      g.toRingHom.comp (algebraMap K (MvPolynomial (Fin s) K)) := by
    ext a
    exact (g.commutes a).symm
  exact hint.to_finite
    ((h ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType)

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.Geometry

theorem ringKrullDim_eq_of_integral_faithful_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    apply iSup_le
    intro l
    obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := S) l.last.asIdeal
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.1
    simpa only [hlen] using Order.LTSeries.length_le_krullDim L

theorem ringKrullDim_eq_of_integral_faithful_normal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [Algebra.IsIntegral R S] [FaithfulSMul R S] [IsIntegrallyClosed R] :
    ringKrullDim S = ringKrullDim R :=
  ringKrullDim_eq_of_integral_faithful_goingDown

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

theorem ringKrullDim_quotient_eq_normalization_variables {n s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial (Fin n) K ⧸ I))
    (hg : Function.Injective g) (hint : g.IsIntegral) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ I) = s := by
  let : Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    g.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  let : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective
      (MvPolynomial (Fin s) K) (MvPolynomial (Fin n) K ⧸ I)).mpr hg
  rw [WeightedTorusJets.Geometry.ringKrullDim_eq_of_integral_faithful_normal
    (R := MvPolynomial (Fin s) K)]
  simp

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_finite_linear_normalization_finite_variables
    {K σ : Type*} [Field K] [Infinite K] [Finite σ]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ K))
    (i : σ) (hX : X i ∉ P) :
    ∃ s : ℕ, s + 1 ≤ Nat.card σ ∧
      ∃ g : MvPolynomial (Fin (s + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ P),
        Function.Injective g ∧ g.IsIntegral ∧ g.Finite ∧
        (∀ j, ∃ l : MvPolynomial σ K,
          l.IsHomogeneous 1 ∧ g (MvPolynomial.X j) = Ideal.Quotient.mk P l) ∧
        g (X 0) = Ideal.Quotient.mk P (X i) ∧
        ringKrullDim (MvPolynomial σ K ⧸ P) = (s + 1 : ℕ) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  cases m with
  | zero => exact Fin.elim0 (e i)
  | succ n =>
    let r := MvPolynomial.renameEquiv K e.symm
    let J := Ideal.comap r.toAlgHom.toRingHom P
    let : J.IsPrime := Ideal.comap_isPrime r.toAlgHom.toRingHom P
    have hJ : J.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) := by
      intro d p hp
      rw [← DirectSum.Decomposition.decompose'_eq,
        MvPolynomial.decomposition.decompose'_apply]
      change MvPolynomial.rename e.symm (homogeneousComponent d p) ∈ P
      rw [MvPolynomial.rename_homogeneousComponent]
      exact homogeneousComponent_mem_of_mem hP hp d
    have hXi : X (e i) ∉ J := by
      change r (X (e i)) ∉ P
      simpa only [r, renameEquiv_apply, rename_X, Equiv.symm_apply_apply] using hX
    have hJP : P = J.map r.toAlgHom.toRingHom :=
      (Ideal.map_comap_of_surjective r.toAlgHom.toRingHom r.surjective P).symm
    let E := Ideal.quotientEquivAlg J P r hJP
    have hE : ∀ p, E (Ideal.Quotient.mk J p) = Ideal.Quotient.mk P (r p) := by
      intro p
      exact Ideal.quotientEquivAlg_mk (I := J) (J := P) r hJP p
    obtain ⟨s, hs, g, hinj, hint, hlin, hfix⟩ :=
      exists_integral_injective_linear_quotient_fixed_coordinate J hJ (e i) hXi
    have hcard : Nat.card σ = n + 1 := by
      simpa using Nat.card_congr e
    let G := E.toAlgHom.comp g
    have hEint := algEquiv_isIntegral
      (A := MvPolynomial (Fin (n + 1)) K ⧸ J)
      (B := MvPolynomial σ K ⧸ P) E
    have hGint : G.IsIntegral := hint.trans _ _ hEint
    have hEfin : E.toAlgHom.Finite :=
      RingHom.Finite.of_surjective E.toAlgHom.toRingHom E.surjective
    have hGfin : G.Finite := hEfin.comp (finite_of_integral_quotient J g hint)
    refine ⟨s, by rw [hcard]; omega, G, E.injective.comp hinj, hGint, hGfin, ?_, ?_, ?_⟩
    · intro j
      obtain ⟨l, hl, hgl⟩ := hlin j
      refine ⟨r l, hl.rename_isHomogeneous, ?_⟩
      change E (g (X j)) = _
      rw [hgl]
      exact hE l
    · change E (g (X 0)) = _
      rw [hfix, hE]
      simp only [r, renameEquiv_apply, rename_X, Equiv.symm_apply_apply]
    · rw [← ringKrullDim_eq_of_ringEquiv E.toRingEquiv]
      exact ringKrullDim_quotient_eq_normalization_variables J g hinj hint

end WeightedTorusJets.LinearNormalization



end SiegelZeros

end OAI
