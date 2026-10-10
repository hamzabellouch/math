import Mathlib
import OAI.Analysis.SymmetricDomains.RootEvaluationSurjective
import OAI.Analysis.SymmetricDomains.SignatureRootValues
import OAI.Analysis.SymmetricDomains.RootSignPattern

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
open Polynomial Finset QuadraticMap
open scoped BigOperators Classical

noncomputable def complexEvaluation (n : ℕ) (z : ℂ) : degreeLT ℝ n →ₗ[ℝ] ℂ :=
  (aeval z).toLinearMap.comp (degreeLT ℝ n).subtype

@[simp] lemma complexEvaluation_apply (n : ℕ) (z : ℂ) (A : degreeLT ℝ n) :
    complexEvaluation n z A = (complexify A.val).eval z := by
  simp [complexEvaluation,aeval_def,complexify,eval_map]
  rfl

noncomputable def rootSquare (n : ℕ) (Q : ℝ[X]) (z : ℂ) :
    QuadraticForm ℝ (degreeLT ℝ n) :=
  Complex.reLm.compQuadraticMap
    ((complexify Q).eval z • (sq (R := ℝ) (A := ℂ)).comp (complexEvaluation n z))

@[simp] lemma rootSquare_apply (n : ℕ) (Q : ℝ[X]) (z : ℂ) (A : degreeLT ℝ n) :
    rootSquare n Q z A = ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re := by
  simp [rootSquare,pow_two]

noncomputable def hermiteForm (P Q : ℝ[X]) : QuadraticForm ℝ (degreeLT ℝ P.natDegree) :=
  ((complexify P).roots.map (rootSquare P.natDegree Q)).sum

lemma hermiteForm_apply (P Q : ℝ[X]) (A : degreeLT ℝ P.natDegree) :
    hermiteForm P Q A = ((complexify P).roots.map
      (fun z => ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re)).sum := by
  simp [hermiteForm,Finset.sum_multiset_map_count]

@[simp] lemma rootEvaluation_real (P : ℝ[X]) (A : degreeLT ℝ P.natDegree)
    (a : RealRoot P) : (rootEvaluation P A).1 a = A.val.eval a.val := by
  simp [rootEvaluation,aeval_def]

@[simp] lemma rootEvaluation_upper (P : ℝ[X]) (A : degreeLT ℝ P.natDegree)
    (b : UpperRoot P) : (rootEvaluation P A).2 b = (complexify A.val).eval b.val := by
  change A.val.eval₂ (algebraMap ℝ ℂ) b.val = _
  rw [eval₂_eq_eval_map]
  rfl

lemma hermiteForm_root_values {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X])
    (A : degreeLT ℝ P.natDegree) :
    hermiteForm P Q A =
      ∑ a : RealRoot P, (P.roots.count a.val : ℝ) * Q.eval a.val * (rootEvaluation P A).1 a ^ 2 +
      ∑ b : UpperRoot P, 2 * ((complexify P).roots.count b.val : ℝ) *
        ((complexify Q).eval b.val * (rootEvaluation P A).2 b ^ 2).re := by
  rw [hermiteForm_apply,Finset.sum_multiset_map_count]
  have he := (rootNodesEquiv hP).sum_comp
    (fun z => ((complexify P).roots.count z.val : ℝ) *
      ((complexify Q).eval z.val * (complexify A.val).eval z.val ^ 2).re)
  have he' := he.trans (Finset.sum_coe_sort (complexify P).roots.toFinset
    (fun z => ((complexify P).roots.count z : ℝ) *
      ((complexify Q).eval z * (complexify A.val).eval z ^ 2).re))
  simp only [nsmul_eq_mul]
  rw [← he']
  simp only [Fintype.sum_sum_type,rootNodesEquiv,Equiv.ofBijective_apply,
    rootNodes,realComplexNodes,Sum.elim_inl,Sum.elim_inr]
  rw [← sum_add_distrib]
  congr 1
  · apply sum_congr rfl
    intro a _
    rw [count_complex_root_real,complexify_real_eval,complexify_real_eval]
    rw [rootEvaluation_real]
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
    ring
  · apply sum_congr rfl
    intro b _
    rw [count_complex_root_conj,complexify_eval_conj,complexify_eval_conj]
    rw [← map_pow (starRingEnd ℂ),← map_mul (starRingEnd ℂ)]
    simp only [Complex.conj_re,rootEvaluation_upper]
    ring

theorem hermite_signature {P : ℝ[X]} (hP : P ≠ 0) (Q : ℝ[X]) :
    signedSignature (hermiteForm P Q) = tarskiQuery P Q := by
  rw [signature_of_root_values (hermiteForm P Q) (rootEvaluation P)
    (rootEvaluation_surjective hP)
    (fun a => (P.roots.count a.val : ℝ) * Q.eval a.val)
    (fun b => ((complexify P).roots.count b.val : ℝ))
    (fun b => (complexify Q).eval b.val) (hermiteForm_root_values hP Q)]
  rw [tarskiQuery]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply sum_congr rfl
  intro a _
  have ha : 0 < (P.roots.count a.val : ℝ) := by
    exact_mod_cast Multiset.count_pos.mpr (Multiset.mem_toFinset.mp a.property)
  rw [sign_mul,sign_pos ha,one_mul]

end Release061.SignElimination

end

end OAI
