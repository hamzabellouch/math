import Mathlib
import OAI.Probability.Ballisticity.Estimates.SurvivingLane

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma quenched_hit_future_bound {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) (C : ℝ≥0∞)
    (hC : ∀ y ∈ T, quenchedKernel (ω,y) (B y) ≤ C) :
    quenchedKernel (ω,x) (⋃ n, HitAt S T n ∩ FutureEvent B n) ≤
      C * quenchedKernel (ω,x) (Hit S T) := by
  rw [← hitKernel_future ω x hST B hB,← hitKernel_total hST]
  calc
    _ ≤ ∫⁻ y, C ∂hitKernel S T (ω,x) := by
      apply lintegral_mono_ae
      filter_upwards [hitKernel_ae_target S T (ω,x)] with y hy
      exact hC y hy
    _ = _ := by simp

lemma hit_split_subset {d : ℕ} (S T U : Set (Lattice d)) (hST : Disjoint S T) (X : Path d)
    (h : X ∈ Hit S T) (hu : ∃ k, X k ∈ U ∧ ∀ j < k, X j ∈ S) :
    X ∈ ⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n := by
  obtain ⟨k,hkU,hkS⟩ := hu
  have hex : ∃ j, X j ∈ U := ⟨k,hkU⟩
  let n := Nat.find hex
  have hnU : X n ∈ U := Nat.find_spec hex
  have hnk : n ≤ k := Nat.find_min' hex hkU
  have hnS : ∀ j < n, X j ∈ S \ U := fun j hj => ⟨hkS j (hj.trans_le hnk),Nat.find_min hex hj⟩
  obtain ⟨m,hmT,hmS⟩ := Set.mem_iUnion.mp h
  by_cases hnm : n ≤ m
  · refine Set.mem_iUnion.mpr ⟨n,⟨hnU,hnS⟩,?_⟩
    change (fun j => X (n+j)) ∈ Hit S T
    refine Set.mem_iUnion.mpr ⟨m-n,?_,?_⟩
    · simpa [Nat.add_sub_of_le hnm] using hmT
    · intro j hj
      exact hmS (n+j) (by omega)
  · exact False.elim (Set.disjoint_left.mp hST (hkS m (by omega)) hmT)

end DirectionalTransience

end

end OAI
