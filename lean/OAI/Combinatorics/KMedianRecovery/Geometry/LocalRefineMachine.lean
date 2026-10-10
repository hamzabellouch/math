import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.LocalFuel

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]
lemma executableRefineFuel_spec (δ : V→V→ℕ) (fs : List V) (D S : Finset V) (n M : ℕ)
    (hSF : S⊆fs.toFinset) (hS : S.Nonempty)
    (hδ : ∀ p∈D,∀ i∈fs.toFinset,(δ p i:ℝ)=dist p i)
    (hM : ∀ p∈D,∀ i∈fs.toFinset,δ p i≤M) (hn : D.card*M≤n) :
    let T := executableDescent fs (natCost δ D) 5 n S
    T⊆fs.toFinset ∧ T.Nonempty ∧ T.card=S.card ∧ cost D T≤cost D S ∧ WidthLocalMin fs.toFinset D T 5 := by
  dsimp only
  have hp:=executableDescent_properties fs (natCost δ D) 5 n S hSF
  have hm:=executableDescent_min fs (natCost δ D) 5 n S hSF
    ((natCost_le δ fs.toFinset D S hSF M hM).trans hn)
  refine ⟨hp.1,Finset.card_pos.mp (by rw [hp.2.1]; exact Finset.card_pos.mpr hS),hp.2.1,?_,?_⟩
  · rw [←natCost_cast δ fs.toFinset D _ hp.1 hδ,←natCost_cast δ fs.toFinset D S hSF hδ]
    exact_mod_cast hp.2.2
  · intro U hUF hcard hrem hadd
    rw [←natCost_cast δ fs.toFinset D _ hp.1 hδ,←natCost_cast δ fs.toFinset D U hUF hδ]
    exact_mod_cast hm U (candidate_of_exchange _ _ _ _ hUF hcard hrem hadd)
end MetricKMedianRecovery.LocalSearch
namespace MetricKMedianRecovery.BitMachine.BinaryLocalRefine
open RationalLeaves WordOperations WordList Polynomial
noncomputable def run (x : List Bool) : List Bool :=
  BinaryLocalSearch.run 5 (pairBits (BinaryLocalAnchor.fuel.word x,x))
noncomputable def run_computes : PolyComputes run :=
  (BinaryLocalAnchor.fuel.computes.pair id_computes).comp (BinaryLocalSearch.run_computes 5)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (S : Finset (Fin m)) : List Bool :=
  BinaryLocalSearch.pack distance (fs.map original) (S.image original)
lemma run_pack {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m)) (hS : S⊆fs.toFinset) :
    run (pack (fun i j=>(δ (loc j) i:ℚ)) fs S)=BinaryFiniteContext.setBits
      ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) 5
        (BinaryLocalAnchor.fuelPoly.eval (pack (fun i j=>(δ (loc j) i:ℚ)) fs S).length) S).image original) := by
  rw [run,pack,BinaryLocalSearch.run_word]
  · rw [BinaryLocalAnchor.fuel.word_length,LocalSearch.executableDescent_map original original.injective fs _ _
      (BinaryLocalCost.rank_nat δ loc hloc)]
  · intro a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,List.mem_toFinset.mp (hS hb),rfl⟩)
lemma fuel_bound {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (S : Finset (Fin m)) :
    d*Rounding.cap d (IntegralAssembly.gamma/16)≤BinaryLocalAnchor.fuelPoly.eval (pack distance fs S).length := by
  let L := (pack distance fs S).length
  have hd : d≤L := by
    simp only [L,pack,BinaryLocalSearch.pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,List.length_replicate]
    omega
  have hc:=GlobalAssembly.cap_polynomial d L hd
  have hdl : d≤L+2 := by omega
  change d*Rounding.cap d (IntegralAssembly.gamma/16)≤BinaryLocalAnchor.fuelPoly.eval L
  calc
    _ ≤ (L+2)*((⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(L+2)^2) := Nat.mul_le_mul hdl hc
    _ = _ := by simp only [BinaryLocalAnchor.fuelPoly,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]; ring
lemma integral_spec {m d : ℕ} [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (S : Finset (Fin m))
    (hSF : S⊆fs.toFinset) (hS : S.Nonempty)
    (hδ : ∀ j,∀ i∈fs.toFinset,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈fs.toFinset,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ T : Finset (Fin m),run (pack (fun i j=>(δ (loc j) i:ℚ)) fs S)=BinaryFiniteContext.setBits (T.image original) ∧
      T⊆fs.toFinset ∧ T.Nonempty ∧ T.card=S.card ∧
      LocalSearch.cost (Finset.univ.image loc) T≤LocalSearch.cost (Finset.univ.image loc) S ∧
      LocalSearch.WidthLocalMin fs.toFinset (Finset.univ.image loc) T 5 := by
  refine ⟨_,run_pack δ loc hloc fs S hSF,?_⟩
  apply LocalSearch.executableRefineFuel_spec δ fs (Finset.univ.image loc) S _
    (Rounding.cap d (IntegralAssembly.gamma/16)) hSF hS
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hδ j i hi
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hM j i hi
  · rw [Finset.card_image_of_injective _ hloc,Finset.card_univ,Fintype.card_fin]
    exact fuel_bound _ fs S
end MetricKMedianRecovery.BitMachine.BinaryLocalRefine

end OAI
