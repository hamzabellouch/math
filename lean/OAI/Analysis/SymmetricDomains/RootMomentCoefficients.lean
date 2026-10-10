import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial MvPolynomial Finset
open scoped Classical BigOperators

noncomputable def powerSumPolynomial (n k : ℕ) : MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℝ (by simp : Fintype.card (Fin n) ≤ n)
    ⟨psum (Fin n) ℝ k, psum_isSymmetric _ _ _⟩).choose

lemma powerSumPolynomial_spec (n k : ℕ) :
    ((esymmAlgHom (Fin n) ℝ n) (powerSumPolynomial n k)).val = psum (Fin n) ℝ k := by
  exact congrArg Subtype.val (Classical.choose_spec
    (MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℝ
      (by simp : Fintype.card (Fin n) ≤ n) ⟨psum (Fin n) ℝ k, psum_isSymmetric _ _ _⟩))

lemma powerSumPolynomial_eval {n : ℕ} (k : ℕ) (v : Fin n → ℂ) :
    MvPolynomial.aeval (fun i : Fin n => (univ.val.map v).esymm (i.val+1))
      (powerSumPolynomial n k) = ∑ i, v i ^ k := by
  have he := congrArg (MvPolynomial.aeval v) (powerSumPolynomial_spec n k)
  rw [esymmAlgHom_apply] at he
  simpa only [MvPolynomial.comp_aeval_apply,aeval_esymm_eq_multiset_esymm,psum,
    map_sum,map_pow,MvPolynomial.aeval_X] using he

lemma multiset_enumerate {α : Type*} (s : Multiset α) {n : ℕ} (hn : s.card = n) :
    ∃ v : Fin n → α, Finset.univ.val.map v = s := by
  subst n
  refine ⟨fun i => s.toList.get ⟨i.val,by simp⟩, ?_⟩
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun i : Fin s.card => s.toList.get ⟨i.val,by simp⟩) = s.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [he,Multiset.coe_toList]

noncomputable def rootCoefficient (P : ℝ[X]) (i : Fin P.natDegree) : ℝ :=
  (-1)^(i.val+1) * P.coeff (P.natDegree - (i.val+1)) / P.leadingCoeff

lemma roots_esymm_eq_rootCoefficient {P : ℝ[X]} (hP : P ≠ 0) (i : Fin P.natDegree) :
    (P.map Complex.ofRealHom).roots.esymm (i.val+1) = (rootCoefficient P i : ℂ) := by
  have hcard := splits_iff_card_roots.mp (IsAlgClosed.splits (P.map Complex.ofRealHom))
  have he := coeff_eq_esymm_roots_of_card hcard
    (k := P.natDegree-(i.val+1)) (by rw [natDegree_map]; exact Nat.sub_le _ _)
  have hsub : P.natDegree - (P.natDegree - (i.val+1)) = i.val+1 := by omega
  rw [natDegree_map,hsub,Polynomial.coeff_map,leadingCoeff_map] at he
  simp only [Complex.ofRealHom_eq_coe] at he
  have hl : (P.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hP
  have hpow : ((-1 : ℂ)^(i.val+1))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (i.val+1),pow_mul]
    norm_num
  simp only [rootCoefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]
  apply (eq_div_iff hl).mpr
  rw [he]
  linear_combination -((P.map Complex.ofRealHom).roots.esymm (i.val+1) * (P.leadingCoeff : ℂ)) * hpow

theorem root_moment_coefficients {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) :
    (((P.map Complex.ofRealHom).roots.map (fun z => z^k)).sum : ℂ) =
      (MvPolynomial.eval (rootCoefficient P) (powerSumPolynomial P.natDegree k) : ℂ) := by
  obtain ⟨v,hv⟩ := multiset_enumerate (P.map Complex.ofRealHom).roots
    (by simpa using splits_iff_card_roots.mp (IsAlgClosed.splits (P.map Complex.ofRealHom)))
  have he := powerSumPolynomial_eval k v
  rw [hv] at he
  simp_rw [roots_esymm_eq_rootCoefficient hP] at he
  rw [← hv,Multiset.map_map]
  change (∑ i, v i ^ k) = _
  rw [← he,MvPolynomial.aeval_def]
  exact (MvPolynomial.eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ)
    (rootCoefficient P) (powerSumPolynomial P.natDegree k)).symm

end Release061.SignElimination

end

end OAI
