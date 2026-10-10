import Mathlib
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalGraph
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalInvariant

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

omit [Fintype F] in

theorem graph_data (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      (∀ G, 0 < (graphLaw d g P A).real.weight G → D.Good G) ∧
      (∀ h i, (graphLaw d g P A).real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → (graphLaw d g P A).real.expect
        (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=D.marginal h i*D.marginal l j) := by
  let dA : A → A → ℚ := fun i j => d i.val.1 j.val.1
  have hd0 : ∀ i j, 0 ≤ dA i j := by
    intro i j
    have hh : 0 ≤ (dA i j:ℝ) := by rw [← hd]; exact dist_nonneg
    exact_mod_cast hh
  have hown : ∀ i j, j∈own A i → dA i j=0 := by
    intro i j hj
    have he : j.val.1=i.val.1 := (mem_filter.mp hj).2
    have hh : (dA i j:ℝ)=0 := by rw [← hd,he,dist_self]
    exact_mod_cast hh
  have htotal : 1 ≤ ∑ _i : A, (g:ℝ) := by
    simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mass,mul_comm] using hA
  let D := Taper.physicalGraphData Δ g P dA (fun i : A => location i.val.1) (own A)
    hg hunit hP hP1 hd0 (fun i j => hd _ _) htotal hown (own_card A)
  have hh := Taper.physical_sparse_graph (enumeration A) Δ g P dA
    (fun i : A => location i.val.1) (own A) hg hunit hP hP1 hd0
      (fun i j => hd _ _) htotal hown (own_card A)
  exact ⟨D,hh.2⟩

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
