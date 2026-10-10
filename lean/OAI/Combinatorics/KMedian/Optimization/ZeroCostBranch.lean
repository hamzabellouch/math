import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost
import OAI.Combinatorics.KMedian.Optimization.IndexedInstanceLP

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

def zeroTest (I : Instance) : Prop := I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k

instance (I : Instance) : Decidable I.zeroTest := by unfold zeroTest; infer_instance

def zeroOutput (I : Instance) : Finset (Fin I.n) :=
  if I.clients.Nonempty then I.clients else {I.facilities.min' I.facilities_nonempty}

theorem zeroOutput_spec (I : Instance) (h : I.zeroTest) :
    I.zeroOutput ⊆ I.facilities ∧ I.zeroOutput.Nonempty ∧ I.zeroOutput.card ≤ I.k ∧
      cost I I.zeroOutput=0 := by
  by_cases hJ : I.clients.Nonempty
  · simp only [zeroOutput,ite_eq_left hJ]
    exact ⟨h.1,hJ,h.2,(I.cost_eq_zero_iff I.clients hJ).mpr Subset.rfl⟩
  · simp only [zeroOutput,ite_eq_right hJ]
    refine ⟨singleton_subset_iff.mpr (min'_mem _ _),singleton_nonempty _,?_,?_⟩
    · simpa only [card_singleton] using I.k_pos
    · have hj : I.clients=∅ := not_nonempty_iff_eq_empty.mp hJ
      simp only [cost,hj,sum_empty]

theorem zeroTest_iff (I : Instance) : I.zeroTest ↔ optimum I=0 :=
  I.optimum_eq_zero_iff.symm

theorem nonzero_clients (I : Instance) (h : ¬I.zeroTest) : I.clients.Nonempty := by
  by_contra hn
  apply h
  have hj : I.clients=∅ := not_nonempty_iff_eq_empty.mp hn
  simp only [zeroTest,hj,empty_subset,card_empty,Nat.zero_le,and_self]

theorem nonzero_optimum (I : Instance) (h : ¬I.zeroTest) : 0 < optimum I :=
  lt_of_le_of_ne I.optimum_nonneg (fun he => h (I.zeroTest_iff.mpr he.symm))

theorem initialPhase_spec (I : Instance) (r : ℕ) (hr : 0 < r) :
    if h : I.zeroTest then
      I.zeroOutput ⊆ I.facilities ∧ I.zeroOutput.Nonempty ∧ I.zeroOutput.card ≤ I.k ∧
        cost I I.zeroOutput=0
    else
      let out := I.computedFractional r hr (I.nonzero_clients h)
      out.Valid I.k ∧ (out.value I.indexedDistance:ℝ) ≤
        (1+3/(r:ℝ))*optimum I := by
  split_ifs with h
  · exact I.zeroOutput_spec h
  · obtain ⟨S,hSF,hS,hSk,he⟩ := I.optimum_attained
    have hc : 0 < rationalCost I S := by
      have hh := I.nonzero_optimum h
      rw [← he,← I.cast_rationalCost S] at hh
      exact_mod_cast hh
    obtain ⟨hv,hc⟩ := I.computedFractional_spec r hr (I.nonzero_clients h) S hSF hS hSk hc
    refine ⟨hv,?_⟩
    have hh : ((I.computedFractional r hr (I.nonzero_clients h)).value I.indexedDistance:ℝ) ≤
        (1+3/(r:ℝ))*(rationalCost I S:ℝ) := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hc
      push_cast at hh
      exact hh
    rwa [I.cast_rationalCost,he] at hh

end Instance
end MetricKMedian
end
end

end OAI
