import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialStripPoints

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosGlobalFiberBranches ErdosConvexGraph

theorem regular_strip_lattice_bound (Q : Bivariate) (a b S : ℝ) (hS : 0 ≤ S)
    (hboundary : ∀ t ∈ Ioo a b, peval Q t 0 ≠ 0 ∧ peval Q t S ≠ 0)
    (hregular : ∀ t ∈ Ioo a b, ∀ y ∈ Icc 0 S, peval Q t y = 0 →
      peval (partialX Q) t y ≠ 0 ∧ peval (partialY Q) t y ≠ 0 ∧
        peval (inflectionPolynomial Q) t y ≠ 0) :
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
      12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
  classical
  have hR : Ioo a b ⊆ regularParameters Q 0 S := by
    intro t ht
    exact ⟨(hboundary t ht).1,(hboundary t ht).2,
      fun y hy => (hregular t ht y hy.1 hy.2).2.1⟩
  obtain ⟨n,hn,f,hf,_,hvals,hcover⟩ :=
    global_branches_on_regular_domain Q 0 S (Ioo a b) isOpen_Ioo isPreconnected_Ioo hR
  have hcurve : ∀ i, ∀ t ∈ Ioo a b, peval Q t (f i t) = 0 :=
    fun i t ht => (hvals i t ht).2.1
  have hparts (i : Fin n) : ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) := by
    apply regular_implicit_arc_lattice_bound Q (f i) a b S hS (hf i) (hcurve i)
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).1
    · exact fun t ht => (hvals i t ht).2.2
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).2.2
  have hcount : (polynomialStripPoints Q a b S).card ≤
      ∑ i : Fin n, (graphLatticePoints (Ioo a b) (f i) S).card := by
    rw [strip_eq_graph_union Q a b S f hcurve hcover]
    exact Finset.card_biUnion_le
  calc
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
        ∑ i : Fin n, ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _i : Fin n, 12*(1+S^((2 : ℝ)/3)) := Finset.sum_le_sum (fun i _ => hparts i)
    _ = (n : ℝ)*(12*(1+S^((2 : ℝ)/3))) := by simp
    _ ≤ (Q.totalDegree : ℝ)*(12*(1+S^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    _ = 12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by ring

end ErdosRegularStrip

end

end Erdos970

end OAI
