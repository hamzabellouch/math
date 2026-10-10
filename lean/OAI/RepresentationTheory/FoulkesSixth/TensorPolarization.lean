import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.Differential
import OAI.RepresentationTheory.FoulkesSixth.GenericShift

namespace OAI

noncomputable section

namespace Foulkes.Polarization
open MvPolynomial
open Foulkes.PolynomialSpan

abbrev P (a n : ℕ) := MvPolynomial (Fin a × Fin n) ℂ

def weight (a n : ℕ) (ij : Fin a × Fin n) : Fin a → ℕ := Pi.single ij.1 1

def W (a n j : ℕ) : Submodule ℂ (P a n) :=
  weightedHomogeneousSubmodule ℂ (weight a n) (fun _ => j)

def rowForm {a n : ℕ} (i : Fin a) (x : Fin n → ℂ) : P a n :=
  ∑ k, x k • X (i, k)

def pureRows {a n : ℕ} (j : ℕ) (x : Fin a → Fin n → ℂ) : P a n :=
  ∏ i, (rowForm i (x i)) ^ j

lemma weight_apply_row {a n : ℕ} (d : (Fin a × Fin n) →₀ ℕ) (i : Fin a) :
    Finsupp.weight (weight a n) d i = ∑ k, d (i, k) := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [weight, Finset.sum_apply, Fintype.sum_prod_type, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp

lemma pureRows_mem {a n j : ℕ} (x : Fin a → Fin n → ℂ) :
    pureRows j x ∈ W a n j := by
  classical
  have hrow (i : Fin a) : (rowForm i (x i)).IsWeightedHomogeneous
      (weight a n) (Pi.single i 1) := by
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro k _
    exact (weightedHomogeneousSubmodule ℂ (weight a n) (Pi.single i 1)).smul_mem _
      (isWeightedHomogeneous_X (R := ℂ) (weight a n) (i, k))
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => (rowForm i (x i)) ^ j) (fun i => j • Pi.single i 1)
    (fun i _ => (hrow i).pow j)
  have hdeg : (∑ i : Fin a, j • (Pi.single i 1 : Fin a → ℕ)) = fun _ => j := by
    ext r
    simp [Pi.single_apply]
  rw [hdeg] at hprod
  exact hprod

theorem W_eq_span_pureRows (a n j : ℕ) :
    W a n j = Submodule.span ℂ (Set.range (pureRows (a := a) (n := n) j)) := by
  classical
  apply le_antisymm
  · intro p hp
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => exact Submodule.zero_mem _
    | add p q hp hq ihp ihq => exact Submodule.add_mem _ ihp ihq
    | monomial d c hd =>
      have hdrow (i : Fin a) : ∑ k, d (i, k) = j := by
        simpa [weight_apply_row] using congrFun hd i
      have hx (i : Fin a) : (∏ k : Fin n, (X (i, k) : P a n) ^ d (i, k)) ∈
          Submodule.span ℂ (Set.range fun x : Fin n → ℂ => (rowForm i x) ^ j) := by
        let e : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun k => d (i, k))
        have he : e.sum (fun _ v => v) = j := by
          rw [Finsupp.sum_fintype _ _ (by simp)]
          exact hdrow i
        have hh := prod_pow_mem_span_powers (fun k => (X (i, k) : P a n)) e j he
        rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)] at hh
        simpa [e, rowForm] using hh
      have hprod := prod_mem_span_range (fun i (x : Fin n → ℂ) => (rowForm i x) ^ j) hx
      have hm : (monomial d c : P a n) = c • ∏ i : Fin a, ∏ k : Fin n,
          (X (i, k) : P a n) ^ d (i, k) := by
        rw [monomial_eq, ← MvPolynomial.smul_eq_C_mul,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
      rw [hm]
      exact Submodule.smul_mem _ _ hprod
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact pureRows_mem x

lemma family_zero_of_all_shifted {A : Type*} [CommRing A] [Algebra ℂ A]
    {a n j L : ℕ} (c : Fin a → Fin n → A) (l : A →ₗ[ℂ] ℂ)
    (hj : a * L ≤ j)
    (hz : mapCoeffs l (GenericShift.family c j L Finset.univ) = 0) :
    mapCoeffs l (GenericShift.family c j L ∅) = 0 := by
  classical
  have hc (t : Finset (Fin a)) :
      mapCoeffs l (GenericShift.family c j L (Finset.univ \ t)) = 0 := by
    induction t using Finset.induction_on with
    | empty => simpa using hz
    | insert u t hu ih =>
      let s : Finset (Fin a) := Finset.univ \ insert u t
      have hus : u ∉ s := by simp [s]
      have hse : insert u s = Finset.univ \ t := by
        ext i
        by_cases hi : i = u <;> simp [s, hi, hu]
      have hcard : s.card + 1 ≤ a := by
        calc
          s.card + 1 = (insert u s).card := (Finset.card_insert_of_notMem hus).symm
          _ ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = a := by simp
      have hbound : s.card * L + L ≤ j := by
        have := Nat.mul_le_mul_right L hcard
        nlinarith
      have hL : L ≤ j := by omega
      change mapCoeffs l (GenericShift.family c j L s) = 0
      apply Differential.shift_power_kernel_zero (u := u.castSucc) (v := Fin.last a)
        (by simp)
        (homogeneous_mapCoeffs l _ (GenericShift.family_degree_source c j L s u hus))
        (homogeneous_mapCoeffs l _ (GenericShift.family_degree_dest c j L s)) hbound
      change ((GenericShift.shift u.castSucc (Fin.last a)).toLinearMap ^ L)
        (mapCoeffs l (GenericShift.family c j L s)) = 0
      rw [← GenericShift.mapCoeffs_shift_pow, GenericShift.shift_family c j L s u hus hL, hse]
      change (mapCoeffsLM l) (j.descFactorial L • GenericShift.family c j L (Finset.univ \ t)) = 0
      rw [map_nsmul]
      change j.descFactorial L • mapCoeffs l (GenericShift.family c j L (Finset.univ \ t)) = 0
      rw [ih, smul_zero]
  simpa using hc Finset.univ

def z {a n : ℕ} (v : Fin n → ℂ) : P a n := ∏ i, rowForm i v

def polarizedSpan (a n j L : ℕ) : Submodule ℂ (P a n) :=
  Submodule.span ℂ {p | ∃ (v : Fin n → ℂ) (f : P a n),
    f ∈ W a n (j - L) ∧ z v ^ L * f = p}

lemma eval_original_rowLinear {a n : ℕ} (u : Fin (a + 1)) (i : Fin a)
    (x : Fin (a + 1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P a n) (x ij))
      (GenericShift.rowLinear u (fun k => (X (i, k) : P a n))) =
        rowForm i (fun k => x (u, k)) :=
  GenericShift.eval_rowLinear u (fun k => (X (i, k) : P a n)) x

lemma eval_family_empty {a n j L : ℕ} (x : Fin (a + 1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P a n) (x ij))
      (GenericShift.family (fun i k => (X (i, k) : P a n)) j L ∅) =
        pureRows j (fun i k => x (i.castSucc, k)) := by
  simp only [GenericShift.family, GenericShift.mixedProduct, Finset.notMem_empty,
    ite_false, map_prod, map_pow, eval_original_rowLinear, pureRows]

lemma eval_family_univ {a n j L : ℕ} (x : Fin (a + 1) × Fin n → ℂ) :
    eval (fun ij => algebraMap ℂ (P a n) (x ij))
      (GenericShift.family (fun i k => (X (i, k) : P a n)) j L Finset.univ) =
        z (fun k => x (Fin.last a, k)) ^ L *
          pureRows (j - L) (fun i k => x (i.castSucc, k)) := by
  simp only [GenericShift.family, GenericShift.mixedProduct, Finset.mem_univ,
    ite_true, map_prod, map_mul, map_pow, eval_original_rowLinear, pureRows, z]
  rw [Finset.prod_mul_distrib, Finset.prod_pow]

lemma z_pow_mem {a n L : ℕ} (v : Fin n → ℂ) : z (a := a) v ^ L ∈ W a n L := by
  have h : (z (a := a) v).IsWeightedHomogeneous (weight a n) (fun _ => 1) := by
    simpa [W, z, pureRows] using pureRows_mem (j := 1) (fun _ => v)
  have hp := h.pow L
  simpa [W, Pi.smul_def] using hp

theorem W_polarization {a n j L : ℕ} (ha : 1 ≤ a) (hj : a * L ≤ j) :
    W a n j = polarizedSpan a n j L := by
  classical
  apply le_antisymm
  · intro f hf
    by_contra hnot
    obtain ⟨l, hlf, hlS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hl (p : P a n) (hp : p ∈ polarizedSpan a n j L) : l p = 0 := by
      have hmem : l p ∈ (polarizedSpan a n j L).map l := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
      rwa [hlS, Submodule.mem_bot] at hmem
    have hfull : mapCoeffs l (GenericShift.family
        (fun i k => (X (i, k) : P a n)) j L Finset.univ) = 0 := by
      apply MvPolynomial.funext
      intro x
      rw [eval_mapCoeffs, eval_family_univ, map_zero]
      apply hl
      exact Submodule.subset_span ⟨_, _, pureRows_mem _, rfl⟩
    have hzero := family_zero_of_all_shifted (fun i k => (X (i, k) : P a n)) l hj hfull
    have hpure (v : Fin a → Fin n → ℂ) : l (pureRows j v) = 0 := by
      let x : Fin (a + 1) × Fin n → ℂ :=
        fun ij => Fin.lastCases 0 (fun i => v i ij.2) ij.1
      have he := congrArg (eval x) hzero
      rw [eval_mapCoeffs, eval_family_empty, map_zero] at he
      simpa [x] using he
    have hW : W a n j ≤ LinearMap.ker l := by
      rw [W_eq_span_pureRows]
      apply Submodule.span_le.mpr
      rintro _ ⟨v, rfl⟩
      exact hpure v
    exact hlf (hW hf)
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, f, hf, rfl⟩
    have hL : L ≤ j := le_trans (Nat.le_mul_of_pos_left L ha) hj
    have hzm := z_pow_mem (a := a) (L := L) v
    change (z v ^ L).IsWeightedHomogeneous (weight a n) (fun _ => L) at hzm
    change f.IsWeightedHomogeneous (weight a n) (fun _ => j - L) at hf
    have hprod := hzm.mul hf
    simpa [W, Pi.add_def, Nat.add_sub_of_le hL] using hprod

end Foulkes.Polarization

end

end OAI
