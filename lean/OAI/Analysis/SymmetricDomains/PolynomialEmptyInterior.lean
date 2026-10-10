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
namespace Release061
open Set Filter Topology

inductive PolynomialSignSet {X ι : Type*} (c : X → ι → ℝ) : Set X → Prop
  | zero (p : MvPolynomial ι ℝ) : PolynomialSignSet c {x | MvPolynomial.eval (c x) p = 0}
  | positive (p : MvPolynomial ι ℝ) : PolynomialSignSet c {x | 0 < MvPolynomial.eval (c x) p}
  | compl {S : Set X} : PolynomialSignSet c S → PolynomialSignSet c Sᶜ
  | union {S T : Set X} : PolynomialSignSet c S → PolynomialSignSet c T → PolynomialSignSet c (S ∪ T)

theorem PolynomialSignSet.exists_regular_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x,
      MvPolynomial.eval (c x) P ≠ 0 → S ∈ 𝓝 x ∨ Sᶜ ∈ 𝓝 x := by
  classical
  induction hS with
  | zero p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inl ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => Or.inr ?_⟩
      exact ((MvPolynomial.continuous_eval p).comp hc).continuousAt.eventually_ne hx
  | positive p =>
    by_cases hp : p = 0
    · subst p
      refine ⟨1,one_ne_zero,fun x _ => Or.inr ?_⟩
      simp
    · refine ⟨p,hp,fun x hx => ?_⟩
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · right
        filter_upwards [((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_lt_const hneg]
          with y hy
        exact not_lt_of_ge hy.le
      · exact Or.inl (((MvPolynomial.continuous_eval p).comp hc).continuousAt.tendsto.eventually_const_lt hpos)
  | @compl _ _ ih =>
    obtain ⟨P,hP,hreg⟩ := ih
    refine ⟨P,hP,fun x hx => ?_⟩
    simpa only [compl_compl] using (hreg x hx).symm
  | @union _ _ _ _ ihS ihT =>
    obtain ⟨P,hP,hregP⟩ := ihS
    obtain ⟨Q,hQ,hregQ⟩ := ihT
    refine ⟨P*Q,mul_ne_zero hP hQ,fun x hx => ?_⟩
    have hPQ : MvPolynomial.eval (c x) P ≠ 0 ∧ MvPolynomial.eval (c x) Q ≠ 0 := by
      simpa only [map_mul,mul_ne_zero_iff] using hx
    rcases hregP x hPQ.1 with hs | hs
    · exact Or.inl (Filter.mem_of_superset hs subset_union_left)
    rcases hregQ x hPQ.2 with ht | ht
    · exact Or.inl (Filter.mem_of_superset ht subset_union_right)
    · exact Or.inr (by simpa only [compl_union] using inter_mem hs ht)

theorem PolynomialSignSet.frontier_polynomial {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧
      ∀ x ∈ frontier S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hreg⟩ := hS.exists_regular_polynomial hc
  refine ⟨P,hP,fun x hx => ?_⟩
  by_contra hne
  rcases hreg x hne with hs | hs
  · exact hx.2 (mem_interior_iff_mem_nhds.mpr hs)
  · have hx' : x ∈ frontier Sᶜ := by simpa only [frontier_compl] using hx
    exact hx'.2 (mem_interior_iff_mem_nhds.mpr hs)

theorem PolynomialSignSet.polynomial_of_empty_interior {X ι : Type*}
    [TopologicalSpace X] {c : X → ι → ℝ} (hc : Continuous c)
    {S : Set X} (hS : PolynomialSignSet c S) (hempty : interior S = ∅) :
    ∃ P : MvPolynomial ι ℝ, P ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval (c x) P = 0 := by
  obtain ⟨P,hP,hzero⟩ := hS.frontier_polynomial hc
  refine ⟨P,hP,fun x hx => hzero x ?_⟩
  exact ⟨subset_closure hx,by simp only [hempty,mem_empty_iff_false,not_false_eq_true]⟩

end Release061

end

end OAI
