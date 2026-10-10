import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
namespace Release061
namespace SignElimination
open Polynomial Finset
open scoped BigOperators Classical

noncomputable def tarskiQuery (P Q : ℝ[X]) : ℝ :=
  ∑ x ∈ P.roots.toFinset, (SignType.sign (Q.eval x) : ℝ)

noncomputable def signCoefficient (s : SignType) (e : Fin 3) : ℝ :=
  match s with
  | .zero => ![1,0,-1] e
  | .pos => ![0,1/2,1/2] e
  | .neg => ![0,-1/2,1/2] e

lemma sign_indicator (s t : SignType) :
    ∑ e : Fin 3, signCoefficient s e * (t : ℝ)^(e.val) =
      if t = s then 1 else 0 := by
  cases s <;> cases t <;> norm_num [signCoefficient,Fin.sum_univ_three,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem sign_pattern_count {ι : Type*} [Fintype ι] (P : ℝ[X])
    (Q : ι → ℝ[X]) (σ : ι → SignType) :
    ((P.roots.toFinset.filter (fun x => ∀ i, SignType.sign ((Q i).eval x) = σ i)).card : ℝ) =
      ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
        tarskiQuery P (∏ i, (Q i)^(e i).val) := by
  classical
  have pointwise (x : ℝ) :
      (if ∀ i, SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) =
      ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
        (SignType.sign ((∏ i, (Q i)^(e i).val).eval x) : ℝ) := by
    have hprod : (if ∀ i, SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) =
        ∏ i, (if SignType.sign ((Q i).eval x) = σ i then (1 : ℝ) else 0) := by
      split_ifs with h
      · simp only [h,ite_true,prod_const_one]
      · push Not at h
        obtain ⟨i,hi⟩ := h
        symm
        apply prod_eq_zero (mem_univ i)
        simp [hi]
    rw [hprod]
    simp_rw [← sign_indicator, Fintype.prod_sum]
    apply sum_congr rfl
    intro e _
    rw [prod_mul_distrib]
    congr 1
    simp only [eval_prod,eval_pow]
    have he : SignType.sign (∏ i, ((Q i).eval x)^(e i).val) =
        ∏ i, (SignType.sign ((Q i).eval x))^(e i).val := by
      exact map_prod (signHom : ℝ →*₀ SignType) _ _ |>.trans
        (prod_congr rfl fun i _ => map_pow (signHom : ℝ →*₀ SignType) _ _)
    rw [he]
    simpa only [SignType.castHom_apply,SignType.coe_pow] using
      (map_prod (SignType.castHom : SignType →*₀ ℝ)
        (fun i => (SignType.sign ((Q i).eval x))^(e i).val) Finset.univ).symm
  rw [← sum_boole]
  simp_rw [pointwise]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [tarskiQuery,mul_sum]

theorem exists_root_sign_pattern_iff {ι : Type*} [Fintype ι]
    {P : ℝ[X]} (hP : P ≠ 0) (Q : ι → ℝ[X]) (σ : ι → SignType) :
    (∃ x : ℝ, P.eval x = 0 ∧ ∀ i, SignType.sign ((Q i).eval x) = σ i) ↔
    0 < ∑ e : ι → Fin 3, (∏ i, signCoefficient (σ i) (e i)) *
      tarskiQuery P (∏ i, (Q i)^(e i).val) := by
  classical
  rw [← sign_pattern_count]
  simp only [Nat.cast_pos,card_pos,Finset.nonempty_iff_ne_empty]
  rw [← Finset.nonempty_iff_ne_empty]
  simp only [Finset.Nonempty,mem_filter,Multiset.mem_toFinset,mem_roots hP,IsRoot]

end SignElimination
end Release061

end

end OAI
