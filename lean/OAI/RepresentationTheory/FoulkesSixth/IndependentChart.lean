import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.InvariantPolarization
import OAI.RepresentationTheory.FoulkesSixth.Collision

namespace OAI

noncomputable section

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization Foulkes.PolynomialSpan

def dehom (a n : ℕ) : P a (n + 1) →ₐ[ℂ] P a n :=
  aeval (fun ij : Fin a × Fin (n + 1) => Fin.cases 1 (fun k => X (ij.1, k)) ij.2)

@[simp] lemma dehom_X_zero {a n : ℕ} (i : Fin a) :
    dehom a n (X (i, 0)) = 1 := by simp [dehom]
@[simp] lemma dehom_X_succ {a n : ℕ} (i : Fin a) (k : Fin n) :
    dehom a n (X (i, k.succ)) = X (i, k) := by simp [dehom]

lemma dehom_rowForm {a n : ℕ} (i : Fin a) (v : Fin (n + 1) → ℂ) :
    dehom a n (rowForm i v) = algebraMap ℂ (P a n) (v 0) + rowForm i (fun k => v k.succ) := by
  simp [rowForm, Fin.sum_univ_succ, Algebra.smul_def]

lemma dehom_z_cons {a n : ℕ} (s : ℂ) (u : Fin n → ℂ) :
    dehom a n (z (Fin.cons s u)) = ∏ i : Fin a, (algebraMap ℂ (P a n) s + rowForm i u) := by
  simp [z, dehom_rowForm]

lemma dehom_renameRow {a n : ℕ} (σ : Equiv.Perm (Fin a)) (f : P a (n+1)) :
    dehom a n (renameRow σ f) = renameRow σ (dehom a n f) := by
  have hh : (dehom a n).comp (renameRow σ) = (renameRow σ).comp (dehom a n) := by
    ext ij
    rcases ij with ⟨i, k⟩
    refine Fin.cases ?_ (fun k => ?_) k <;> simp [renameRow]
  exact DFunLike.congr_fun hh f

def E (a n : ℕ) : Submodule ℂ (P a n) := (R a (n+1) 1).map (dehom a n).toLinearMap

lemma dehom_z_mem_E {a n : ℕ} (v : Fin (n+1) → ℂ) :
    dehom a n (z v) ∈ E a n := Submodule.mem_map.mpr ⟨z v, z_mem_R v, rfl⟩

lemma one_mem_E (a n : ℕ) : (1 : P a n) ∈ E a n := by
  have hh := dehom_z_mem_E (a := a) (Fin.cons (1 : ℂ) (fun _ : Fin n => 0))
  simpa [dehom_z_cons, rowForm] using hh

lemma pow_mono {a n k l : ℕ} (h : k ≤ l) : E a n ^ k ≤ E a n ^ l := by
  exact pow_le_pow_right₀ (Submodule.one_le.mpr (one_mem_E a n)) h

lemma elementary_mem_E {a n : ℕ} (u : Fin n → ℂ) (h : ℕ) :
    aeval (fun i : Fin a => rowForm i u) (esymm (Fin a) ℂ h) ∈ E a n := by
  classical
  let G : MvPolynomial Unit (P a n) := ∏ i : Fin a, (X () * C (rowForm i u) + 1)
  have heval (s : Unit → ℂ) : eval (fun i => algebraMap ℂ (P a n) (s i)) G ∈ E a n := by
    have hh := dehom_z_mem_E (a := a) (Fin.cons (1 : ℂ) (fun k => s () * u k))
    convert hh using 1
    simp only [G, eval_prod, eval_add, eval_mul, eval_X, eval_C, map_one,
      dehom_z_cons, map_one, rowForm,
      Algebra.smul_def]
    apply Finset.prod_congr rfl
    intro i _
    simp [map_mul, Finset.mul_sum, mul_assoc, add_comm]
  have hc := coeff_mem_of_evaluations G (E a n) heval (Finsupp.single () h)
  have hg : G = ∑ s ∈ (Finset.univ : Finset (Fin a)).powerset,
      (X () : MvPolynomial Unit (P a n)) ^ s.card * C (∏ i ∈ s, rowForm i u) := by
    simp only [G, Finset.prod_add, Finset.prod_const_one, mul_one, Finset.prod_mul_distrib,
      Finset.prod_const, ← map_prod]
  rw [hg] at hc
  have hcoeff (s : Finset (Fin a)) :
      (X () ^ s.card * C (∏ i ∈ s, rowForm i u)).coeff (Finsupp.single () h) =
        if s.card = h then ∏ i ∈ s, rowForm i u else 0 := by
    rw [mul_comm, coeff_C_mul, X_pow_eq_monomial]
    simp only [coeff_monomial]
    simp [eq_comm]
  simp only [coeff_sum, hcoeff] at hc
  simpa only [esymm, map_sum, map_prod, aeval_X, Finset.powersetCard_eq_filter,
    Finset.sum_filter, apply_ite, map_prod, aeval_X, map_zero] using hc

lemma powersum_mem {a n : ℕ} (u : Fin n → ℂ) (d : ℕ) :
    (∑ i : Fin a, rowForm i u ^ d) ∈ E a n ^ d := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d = 0
    · subst d
      simpa using (Submodule.sum_mem (1 : Submodule ℂ (P a n))
        (fun (i : Fin a) (_ : i ∈ Finset.univ) => (Submodule.one_le.mp le_rfl)))
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hn := congrArg (aeval (fun i : Fin a => rowForm i u))
      (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin a) ℂ d hdpos)
    simp only [psum, map_sum, map_pow, aeval_X, map_sub, map_mul, map_neg,
      map_one, map_natCast] at hn
    rw [hn]
    apply Submodule.sub_mem
    · have hh := (pow_mono (a := a) (n := n) hdpos)
        (show aeval (fun i : Fin a => rowForm i u) (esymm (Fin a) ℂ d) ∈ E a n ^ 1 by
          simpa using elementary_mem_E u d)
      convert (E a n ^ d).smul_mem (((-1 : ℂ) ^ (d+1)) * (d : ℂ)) hh using 1
      simp [Algebra.smul_def, mul_assoc]
    · apply Submodule.sum_mem
      intro ij hij
      obtain ⟨hij, hi⟩ := Finset.mem_filter.mp hij
      have hsum : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hi' : 0 < ij.1 ∧ ij.1 < d := hi
      have hj : ij.2 < d := by omega
      have he := (pow_mono (a := a) (n := n) hi'.1)
        (show aeval (fun i : Fin a => rowForm i u) (esymm (Fin a) ℂ ij.1) ∈ E a n ^ 1 by
          simpa using elementary_mem_E u ij.1)
      have hp := Submodule.mul_mem_mul he (ih ij.2 hj)
      rw [← pow_add, hsum] at hp
      convert (E a n ^ d).smul_mem ((-1 : ℂ) ^ ij.1) hp using 1
      simp [Algebra.smul_def, mul_assoc]

def inRow {a n : ℕ} (i : Fin a) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] P a n :=
  rename (fun k => (i, k))

def pSum {a n : ℕ} : MvPolynomial (Fin n) ℂ →ₗ[ℂ] P a n :=
  ∑ i : Fin a, (inRow i).toLinearMap

lemma pSum_apply {a n : ℕ} (f : MvPolynomial (Fin n) ℂ) :
    pSum (a := a) f = ∑ i : Fin a, inRow i f := by
  simp [pSum, LinearMap.sum_apply]

lemma pSum_homogeneous_mem {a n d : ℕ} {f : MvPolynomial (Fin n) ℂ}
    (hf : f.IsHomogeneous d) : pSum (a := a) f ∈ E a n ^ d := by
  have hle : homogeneousSubmodule (Fin n) ℂ d ≤ (E a n ^ d).comap pSum := by
    rw [homogeneous_eq_span_powers]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change pSum (a := a) ((∑ k : Fin n, u k • X k) ^ d) ∈ E a n ^ d
    simpa [pSum_apply, inRow, rowForm] using powersum_mem (a := a) u d
  exact hle hf

end Foulkes.Chart

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization Foulkes.Collision

lemma distinctSum_homogeneous_mem {a n h : ℕ} (q : Fin h → MvPolynomial (Fin n) ℂ)
    (d : Fin h → ℕ) (hq : ∀ r, (q r).IsHomogeneous (d r)) :
    distinctSum (fun i : Fin a => inRow i) q ∈ E a n ^ (∑ r, d r) := by
  classical
  induction h with
  | zero =>
    simp only [distinctSum, Fin.prod_univ_zero, Fintype.sum_unique, Fin.sum_univ_zero, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | succ h ih =>
    rw [← Fin.cons_self_tail q, recurrence, Fin.sum_univ_succ]
    apply Submodule.sub_mem
    · have hh := Submodule.mul_mem_mul (pSum_homogeneous_mem (a := a) (hq 0))
        (ih (Fin.tail q) (Fin.tail d) (fun r => hq r.succ))
      rw [← pow_add] at hh
      simpa only [pSum_apply, Fin.tail] using hh
    · apply Submodule.sum_mem
      intro r _
      have hh := ih (Function.update (Fin.tail q) r (q 0 * q r.succ))
        (Function.update (Fin.tail d) r (d 0 + d r.succ)) (by
          intro j
          by_cases hj : j = r
          · subst j; simpa using (hq 0).mul (hq r.succ)
          · simpa [hj, Fin.tail] using hq j.succ)
      have hsum : (∑ j : Fin h, Function.update (Fin.tail d) r (d 0 + d r.succ) j) =
          d 0 + ∑ j : Fin h, d j.succ := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ r)]
        change d 0 + Fin.tail d r + ∑ j ∈ Finset.univ \ {r}, Fin.tail d j =
          d 0 + ∑ j, Fin.tail d j
        rw [Finset.sdiff_singleton_eq_erase, add_assoc,
          Finset.add_sum_erase Finset.univ (Fin.tail d) (Finset.mem_univ r)]
      rw [hsum] at hh
      exact hh

def rowExp {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) (i : Fin a) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => d (i,k))

@[simp] lemma rowExp_apply {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) (i : Fin a) (k : Fin n) :
    rowExp d i k = d (i,k) := by simp [rowExp]

lemma monomial_eq_prod_rows {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) :
    (monomial d 1 : P a n) = ∏ i : Fin a, inRow i (monomial (rowExp d i) 1) := by
  classical
  simp [inRow, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, rowExp]

lemma renameRow_inRow {a n : ℕ} (σ : Equiv.Perm (Fin a)) (i : Fin a)
    (f : MvPolynomial (Fin n) ℂ) : renameRow σ (inRow i f) = inRow (σ i) f := by
  simp [renameRow, inRow, rename_rename, Function.comp_def]

lemma permSum_monomial {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) :
    (∑ σ : Equiv.Perm (Fin a), renameRow σ (monomial d 1 : P a n)) =
      distinctSum (fun i : Fin a => inRow i) (fun i => monomial (rowExp d i) 1) := by
  classical
  simp only [monomial_eq_prod_rows, map_prod, renameRow_inRow, distinctSum]
  exact (Equiv.sum_comp (Equiv.embeddingEquivOfFinite (Fin a))
    (fun σ => ∏ i : Fin a, inRow (σ i) (monomial (rowExp d i) 1))).symm

lemma average_monomial_mem {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) (c : ℂ) :
    average a n (monomial d c) ∈ E a n ^ (∑ ij, d ij) := by
  classical
  have hhom (i : Fin a) : (monomial (rowExp d i) (1 : ℂ)).IsHomogeneous (∑ k, d (i,k)) := by
    apply isWeightedHomogeneous_monomial
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, rowExp]
  have hh := distinctSum_homogeneous_mem (a := a)
    (fun i => (monomial (rowExp d i) (1 : ℂ))) (fun i => ∑ k, d (i,k)) hhom
  rw [← Fintype.sum_prod_type, ← permSum_monomial] at hh
  have hs : (monomial d c : P a n) = c • monomial d 1 := by simp [smul_monomial]
  rw [hs, map_smul, average_apply]
  apply Submodule.smul_mem
  exact Submodule.smul_mem _ _ hh

end Foulkes.Chart

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization

def tailExp {a n : ℕ} (d : (Fin a × Fin (n+1)) →₀ ℕ) : (Fin a × Fin n) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun ij => d (ij.1, ij.2.succ))

@[simp] lemma tailExp_apply {a n : ℕ} (d : (Fin a × Fin (n+1)) →₀ ℕ) (ij : Fin a × Fin n) :
    tailExp d ij = d (ij.1, ij.2.succ) := by simp [tailExp]

def rehomExp {a n : ℕ} (k : ℕ) (d : (Fin a × Fin n) →₀ ℕ) :
    (Fin a × Fin (n+1)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun ij =>
    Fin.cases (k - ∑ r : Fin n, d (ij.1, r)) (fun r => d (ij.1, r)) ij.2)

lemma rehomExp_tailExp {a n k : ℕ} {d : (Fin a × Fin (n+1)) →₀ ℕ}
    (hd : Finsupp.weight (weight a (n+1)) d = fun _ => k) : rehomExp k (tailExp d) = d := by
  ext ij
  rcases ij with ⟨i,r⟩
  have hi := congrFun hd i
  rw [weight_apply_row, Fin.sum_univ_succ] at hi
  refine Fin.cases ?_ (fun r => ?_) r
  · simp only [rehomExp, Finsupp.equivFunOnFinite_symm_apply_apply, Fin.cases_zero, tailExp_apply]
    omega
  · simp [rehomExp]

lemma dehom_monomial {a n : ℕ} (d : (Fin a × Fin (n+1)) →₀ ℕ) (c : ℂ) :
    dehom a n (monomial d c) = monomial (tailExp d) c := by
  classical
  simp only [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, map_mul, map_prod, map_pow]
  rw [show (dehom a n) (C c) = C c from (dehom a n).commutes c]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.prod_univ_succ, dehom_X_zero, dehom_X_succ, one_pow, one_mul, tailExp_apply]

def rehom (a n k : ℕ) : P a n →ₗ[ℂ] P a (n+1) :=
  AddMonoidAlgebra.mapDomainLinearMap ℂ ℂ (rehomExp k)

@[simp] lemma rehom_monomial {a n k : ℕ} (d : (Fin a × Fin n) →₀ ℕ) (c : ℂ) :
    rehom a n k (monomial d c) = monomial (rehomExp k d) c := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

lemma rehom_dehom {a n k : ℕ} {f : P a (n+1)} (hf : f ∈ W a (n+1) k) :
    rehom a n k (dehom a n f) = f := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add f g hf hg ihf ihg => simp [ihf, ihg]
  | monomial d c hd => rw [dehom_monomial, rehom_monomial, rehomExp_tailExp hd]

lemma dehom_injective_W {a n k : ℕ} {f g : P a (n+1)} (hf : f ∈ W a (n+1) k)
    (hg : g ∈ W a (n+1) k) (hfg : dehom a n f = dehom a n g) : f = g := by
  rw [← rehom_dehom hf, ← rehom_dehom hg, hfg]

end Foulkes.Chart

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization Foulkes.Collision

lemma mul_mem_W {a n j k : ℕ} {f g : P a n} (hf : f ∈ W a n j) (hg : g ∈ W a n k) :
    f * g ∈ W a n (j+k) := by
  exact MvPolynomial.IsWeightedHomogeneous.mul hf hg

lemma one_mem_W (a n : ℕ) : (1 : P a n) ∈ W a n 0 :=
  MvPolynomial.isWeightedHomogeneous_one ℂ (weight a n)

theorem invariant_mem_E_pow {a n t : ℕ} {f : P a n} (hf : f ∈ rowInvariants a n)
    (ht : f.totalDegree ≤ t) : f ∈ E a n ^ t := by
  classical
  rw [← average_eq hf, f.as_sum]
  simp only [map_sum]
  apply Submodule.sum_mem
  intro d hd
  apply pow_mono _ (average_monomial_mem d _)
  have hh := (MvPolynomial.le_totalDegree hd).trans ht
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hh
  exact hh

lemma dehom_average {a n : ℕ} (f : P a (n+1)) :
    dehom a n (average a (n+1) f) = average a n (dehom a n f) := by
  simp only [average_apply, map_smul, map_sum, dehom_renameRow]

lemma dehom_R_mem_E_pow {a n k : ℕ} {f : P a (n+1)} (hf : f ∈ R a (n+1) k) :
    dehom a n f ∈ E a n ^ (a*k) := by
  classical
  have haux {g : P a (n+1)} (hg : g ∈ W a (n+1) k) :
      dehom a n (average a (n+1) g) ∈ E a n ^ (a*k) := by
    induction hg using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add f g hf hg ihf ihg => simpa using (E a n ^ (a*k)).add_mem ihf ihg
    | monomial d c hd =>
      rw [dehom_average, dehom_monomial]
      apply pow_mono _ (average_monomial_mem (tailExp d) c)
      rw [Fintype.sum_prod_type]
      calc
        ∑ i : Fin a, ∑ r : Fin n, tailExp d (i,r) ≤ ∑ _i : Fin a, k := by
          apply Finset.sum_le_sum
          intro i _
          have hi := congrFun hd i
          rw [weight_apply_row, Fin.sum_univ_succ] at hi
          simp only [tailExp_apply]
          omega
        _ = a*k := by simp
  simpa only [average_eq hf.2] using haux hf.1

def component (a n k : ℕ) : Submodule ℂ (P a n) := W a n k ⊓ (A a n).toSubmodule

lemma E_pow_le_component_image (a n m : ℕ) :
    E a n ^ m ≤ (component a (n+1) m).map (dehom a n).toLinearMap := by
  induction m with
  | zero =>
    rw [pow_zero, Submodule.one_le]
    exact Submodule.mem_map.mpr ⟨1, ⟨one_mem_W _ _, (A _ _).one_mem⟩, map_one (dehom a n)⟩
  | succ m ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro x hx y hy
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp (ih hx)
      obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hy
      exact Submodule.mem_map.mpr ⟨g*h,
        ⟨mul_mem_W hg.1 hh.1, (A _ _).mul_mem hg.2 (Algebra.subset_adjoin hh)⟩,
        map_mul (dehom a n) g h⟩
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy

theorem chart_standard {a n k L : ℕ} {f : P a (n+1)} (hf : f ∈ R a (n+1) k)
    (hL : a*k ≤ k+L) : z (Fin.cons (1 : ℂ) (fun _ : Fin n => 0)) ^ L * f ∈ A a (n+1) := by
  have hd := pow_mono hL (dehom_R_mem_E_pow hf)
  obtain ⟨g, hg, hgeq⟩ := Submodule.mem_map.mp (E_pow_le_component_image a n (k+L) hd)
  have hzW : z (Fin.cons (1 : ℂ) (fun _ : Fin n => 0)) ^ L * f ∈ W a (n+1) (k+L) := by
    simpa only [add_comm] using mul_mem_W (z_pow_mem _) hf.1
  have heq : g = z (Fin.cons (1 : ℂ) (fun _ : Fin n => 0)) ^ L * f := by
    apply dehom_injective_W hg.1 hzW
    simpa [dehom_z_cons, rowForm] using hgeq
  rw [← heq]
  exact hg.2

end Foulkes.Chart

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization

def columns {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) : P a n →ₐ[ℂ] P a m :=
  aeval (fun ij : Fin a × Fin n => rowForm ij.1 (g (Pi.single ij.2 1)))

def rowLinear {a n : ℕ} (i : Fin a) : (Fin n → ℂ) →ₗ[ℂ] P a n where
  toFun := rowForm i
  map_add' u v := by simp [rowForm, add_smul, Finset.sum_add_distrib]
  map_smul' c u := by simp [rowForm, mul_smul, Finset.smul_sum]

@[simp] lemma rowLinear_apply {a n : ℕ} (i : Fin a) (v : Fin n → ℂ) :
    rowLinear i v = rowForm i v := rfl

@[simp] lemma columns_X {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (ij : Fin a × Fin n) : columns g (X ij) = rowForm ij.1 (g (Pi.single ij.2 1)) := by
  simp [columns]

lemma rowForm_single {a n : ℕ} (i : Fin a) (k : Fin n) :
    rowForm i (Pi.single k 1) = (X (i,k) : P a n) := by
  classical
  simp [rowForm, Pi.single_apply]

lemma columns_rowForm {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (i : Fin a) (v : Fin n → ℂ) : columns g (rowForm i v) = rowForm i (g v) := by
  classical
  have hv : ∑ k : Fin n, v k • (Pi.single k (1 : ℂ) : Fin n → ℂ) = v := by
    ext k
    simp [Pi.single_apply]
  calc
    columns g (rowForm i v) = ∑ k : Fin n, v k • rowLinear i (g (Pi.single k 1)) := by
      simp only [rowForm, map_sum, map_smul, columns_X, rowLinear_apply]
    _ = rowLinear i (g (∑ k : Fin n, v k • Pi.single k 1)) := by simp
    _ = rowForm i (g v) := by rw [hv]; rfl

lemma columns_pureRows {a n m j : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (v : Fin a → Fin n → ℂ) : columns g (pureRows j v) = pureRows j (fun i => g (v i)) := by
  simp only [pureRows, map_prod, map_pow, columns_rowForm]

lemma columns_mem_W {a n m j : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    {f : P a n} (hf : f ∈ W a n j) : columns g f ∈ W a m j := by
  have hh : W a n j ≤ (W a m j).comap (columns g).toLinearMap := by
    rw [W_eq_span_pureRows]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change columns g (pureRows j v) ∈ W a m j
    rw [columns_pureRows]
    exact pureRows_mem _
  exact hh hf

lemma columns_renameRow {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (σ : Equiv.Perm (Fin a)) (f : P a n) :
    columns g (renameRow σ f) = renameRow σ (columns g f) := by
  have hh : (columns g).comp (renameRow σ) = (renameRow σ).comp (columns g) := by
    ext ij
    simp [columns, renameRow, rowForm]
  exact DFunLike.congr_fun hh f

lemma columns_mem_R {a n m j : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    {f : P a n} (hf : f ∈ R a n j) : columns g f ∈ R a m j := by
  refine ⟨columns_mem_W g hf.1, fun σ => ?_⟩
  rw [← columns_renameRow, hf.2 σ]

lemma columns_mem_A {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    {f : P a n} (hf : f ∈ A a n) : columns g f ∈ A a m := by
  have hh : A a n ≤ (A a m).comap (columns g) := by
    apply Algebra.adjoin_le
    intro h hh
    exact Algebra.subset_adjoin (columns_mem_R g hh)
  exact hh hf

lemma columns_z {a n m : ℕ} (g : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (v : Fin n → ℂ) :
    columns (a := a) g (z v) = z (g v) := by simp [z, columns_rowForm]

lemma columns_inverse {a n : ℕ} (g : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) (f : P a n) :
    columns g.toLinearMap (columns g.symm.toLinearMap f) = f := by
  have hh : (columns (a := a) g.toLinearMap).comp (columns g.symm.toLinearMap) =
      AlgHom.id ℂ (P a n) := by
    apply MvPolynomial.algHom_ext
    intro ij
    simp only [AlgHom.comp_apply, columns_X, columns_rowForm, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, AlgHom.id_apply, rowForm_single]
  exact DFunLike.congr_fun hh f

lemma exists_linearEquiv_send {n : ℕ} {v w : Fin n → ℂ} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ), g v = w := by
  let ev := LinearEquiv.toSpanNonzeroSingleton ℂ (Fin n → ℂ) v hv
  let ew := LinearEquiv.toSpanNonzeroSingleton ℂ (Fin n → ℂ) w hw
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ev.symm.trans ew)
  refine ⟨g, ?_⟩
  have hh := hg (ev 1)
  change (ew (ev.symm (ev 1)) : Fin n → ℂ) = g (ev 1) at hh
  rw [ev.symm_apply_apply] at hh
  have hev : (ev 1 : Fin n → ℂ) = v := by simp [ev]
  have hew : (ew 1 : Fin n → ℂ) = w := by simp [ew]
  rw [hev, hew] at hh
  exact hh.symm

theorem chart {a n k L : ℕ} {f : P a n} (hf : f ∈ R a n k)
    (v : Fin n → ℂ) (hv : v ≠ 0) (hL : a*k ≤ k+L) : z v ^ L * f ∈ A a n := by
  cases n with
  | zero =>
    exfalso
    apply hv
    ext i
    exact Fin.elim0 i
  | succ n =>
    let e : Fin (n+1) → ℂ := Fin.cons 1 (fun _ => 0)
    have he : e ≠ 0 := by
      intro hh
      have := congrFun hh 0
      simp [e] at this
    obtain ⟨g, hg⟩ := exists_linearEquiv_send he hv
    have hsource := chart_standard (columns_mem_R g.symm.toLinearMap hf) hL
    have htarget := columns_mem_A g.toLinearMap hsource
    change g (Fin.cons 1 (fun _ : Fin n => 0)) = v at hg
    simpa only [map_mul, map_pow, columns_z, columns_inverse, LinearEquiv.coe_coe, hg] using htarget

end Foulkes.Chart

namespace Foulkes.Chart
open MvPolynomial Foulkes.Polarization

lemma z_zero {a n : ℕ} (ha : 0 < a) : z (a := a) (0 : Fin n → ℂ) = 0 := by
  simp [z, rowForm, zero_pow ha.ne']

theorem independent_chart_bound (a n b : ℕ) (ha : 2 ≤ a) (hb : a*(a-1)^2 ≤ b) :
    R a n b = component a n b := by
  classical
  let L := (a-1)^2
  have ha1 : 1 ≤ a := by omega
  have hapos : 0 < a := by omega
  have hLpos : 0 < L := by
    have hs : 0 < a-1 := by omega
    exact pow_pos hs 2
  have hlow (v : Fin n → ℂ) (k : ℕ) (hk : k < a) {f : P a n} (hf : f ∈ R a n k) :
      z v ^ L * f ∈ A a n := by
    by_cases hv : v = 0
    · simp only [hv, z_zero hapos, zero_pow hLpos.ne', zero_mul]
      exact (A a n).zero_mem
    · apply chart hf v hv
      have hka : k ≤ a-1 := by omega
      have hm := Nat.mul_le_mul_left (a-1) hka
      have hs : a-1+1 = a := Nat.sub_add_cancel ha1
      dsimp [L]
      nlinarith
  have hmodule (v : Fin n → ℂ) {f : P a n} (hf : f ∈ lowDegreeModule a n) :
      z v ^ L * f ∈ A a n := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨k,hk,hf⟩ := hf
      exact hlow v k hk hf
    | zero => simp
    | add f g hf hg ihf ihg => simpa [mul_add] using (A a n).add_mem ihf ihg
    | smul c f hf ih =>
      change z v ^ L * ((c : P a n) * f) ∈ A a n
      simpa [mul_left_comm, mul_assoc] using (A a n).mul_mem c.property ih
  have hspan : invariantPolarizedSpan a n b L ≤ (A a n).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, f, hf, rfl⟩
    exact hmodule v (module_generation ha1 _ hf)
  apply le_antisymm
  · intro f hf
    refine ⟨hf.1, ?_⟩
    exact hspan ((R_polarization ha1 hb).le hf)
  · exact AComponent_le_R a n b

end Foulkes.Chart

end

end OAI
