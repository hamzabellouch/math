import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalBest
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalTransport

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open RationalLeaves
lemma connection_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (S : Finset (Fin m)) (j : Fin d) :
    connection (fun i j=>(δ (loc j) i:ℚ)) (S.image original) j=(LocalSearch.natConnection δ S (loc j):ℚ) := by
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,hei⟩:=Finset.exists_mem_eq_inf' hS (δ (loc j))
    rw [LocalSearch.natConnection,dite_eq_left hS,hei]
    apply le_antisymm
    · apply RationalMin.minimum_le_mem
      exact List.mem_map.mpr ⟨original i,(Finset.mem_sort _).mpr (Finset.mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
    · apply RationalMin.minimum_lower
      · intro hempty
        have hm : (δ (loc j) i:ℚ) ∈ (BinaryLabel.orderedSort (S.image original)).map
            (fun a=>rows (fun i j=>(δ (loc j) i:ℚ)) a j) :=
          List.mem_map.mpr ⟨original i,(Finset.mem_sort _).mpr (Finset.mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
        rw [hempty] at hm
        exact List.not_mem_nil hm
      · intro q hq
        obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
        obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ((Finset.mem_sort _).mp ha)
        change (δ (loc j) i:ℚ) ≤ δ (loc j) b
        exact_mod_cast (show δ (loc j) i ≤ δ (loc j) b by rw [←hei]; exact Finset.inf'_le _ hb)
  · have he : S=∅:=Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [LocalSearch.natConnection,dite_eq_right hS]
    simp only [connection,Finset.image_empty,BinaryLabel.orderedSort,Finset.sort_empty,List.map_nil,
      RationalMin.minimum,List.head?_nil,Option.getD_none,List.foldl_nil,Nat.cast_zero]
lemma cost_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (S : Finset (Fin m)) :
    cost (fun i j=>(δ (loc j) i:ℚ)) (S.image original)=
      (LocalSearch.natCost δ (Finset.univ.image loc) S:ℚ) := by
  simp only [cost,connection_nat,LocalSearch.natCost,Nat.cast_sum]
  rw [Finset.sum_image (fun a _ b _ hab=>hloc hab)]
lemma rank_nat {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (S : Finset (Fin m)) :
    ⌈cost (fun i j=>(δ (loc j) i:ℚ)) (S.image original)⌉₊=
      LocalSearch.natCost δ (Finset.univ.image loc) S := by
  rw [cost_nat δ loc hloc,Nat.ceil_natCast]
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations RationalLeaves
open BinaryFiniteContext (labels setBits)
lemma run_integral {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m))
    (w n : ℕ) (hS : S⊆fs.toFinset) :
    run w (pairBits (List.replicate n true,pack (fun i j=>(δ (loc j) i:ℚ)) (fs.map original) (S.image original)))=
      setBits ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) w n S).image original) := by
  rw [run_pack]
  · rw [LocalSearch.executableDescent_map original original.injective fs _ _ (BinaryLocalCost.rank_nat δ loc hloc)]
  · intro a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,List.mem_toFinset.mp (hS hb),rfl⟩)
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
