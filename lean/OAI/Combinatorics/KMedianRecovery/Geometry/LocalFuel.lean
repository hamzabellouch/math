import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.PolynomialProduct
import OAI.Combinatorics.KMedianRecovery.Encoding.WordTake
import OAI.Combinatorics.KMedianRecovery.Algorithms.LocalIntegral

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels setBits)
lemma run_input_length (w : ℕ) (u v x : List Bool) (h : u.length=v.length) :
    run w (pairBits (u,x))=run w (pairBits (v,x)) := by
  simp only [run,Function.comp_apply,iterationInput,extractPrefix_pairBits,discardPrefix_pairBits,
    BoundedIteration.run_pair,capacity.word_length,pairBits_length,h]
lemma run_word {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m)))
    (S : Finset (Label (Fin m))) (w : ℕ) (u : List Bool) (hS : S⊆fs.toFinset) :
    run w (pairBits (u,pack distance fs S))=setBits
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w u.length S) := by
  rw [run_input_length w u (List.replicate u.length true) _ (List.length_replicate ..).symm]
  exact run_pack distance fs S w u.length hS
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def seed (x : List Bool) : List Bool :=
  BinaryLabel.sort (Take.run (pairBits (field 3 x,field 2 x)))
attribute [local irreducible] Take.run BinaryLabel.sort
noncomputable def seed_computes : PolyComputes seed :=
  (((field_computes 3).pair (field_computes 2)).comp Take.run_computes).comp BinaryLabel.sort_computes
noncomputable def state (x : List Bool) : List Bool :=
  encode [field 0 x,field 1 x,field 2 x,seed x]
noncomputable def state_computes : PolyComputes state :=
  list_computes [field 0,field 1,field 2,seed] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact ⟨field_computes 0⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨field_computes 2⟩
    · exact ⟨seed_computes⟩)
noncomputable def fuelPoly : Polynomial ℕ :=
  C (⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(X+2)^3
noncomputable def fuel : PolynomialCounter fuelPoly := PolynomialCounter.choose fuelPoly
noncomputable def run (x : List Bool) : List Bool :=
  BinaryLocalSearch.run 5 (pairBits (fuel.word x,state x))
noncomputable def run_computes : PolyComputes run :=
  (fuel.computes.pair state_computes).comp (BinaryLocalSearch.run_computes 5)
def pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) : List Bool :=
  encode [Rectangular.encode distance,List.replicate d true,labels (fs.map original),r.bits]
lemma seed_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
    seed (pack distance fs r)=setBits ((fs.take r).toFinset.image original) := by
  simp only [seed,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    labels,Take.run_encode,←List.map_take,BinaryLabel.sort_encode]
  change setBits ((fs.take r).map original).toFinset=setBits ((fs.take r).toFinset.image original)
  apply congrArg setBits
  ext a
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
lemma state_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
    state (pack distance fs r)=BinaryLocalSearch.pack distance (fs.map original) ((fs.take r).toFinset.image original) := by
  rw [state,seed_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryLocalSearch.pack]
lemma run_pack {m d : ℕ} (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (r : ℕ) :
    run (pack (fun i j=>(δ (loc j) i:ℚ)) fs r)=
      setBits ((LocalSearch.executableDescent fs (LocalSearch.natCost δ (Finset.univ.image loc)) 5
        (fuelPoly.eval (pack (fun i j=>(δ (loc j) i:ℚ)) fs r).length) (fs.take r).toFinset).image original) := by
  rw [run,state_pack,BinaryLocalSearch.run_word]
  · rw [fuel.word_length,LocalSearch.executableDescent_map original original.injective fs _ _
      (BinaryLocalCost.rank_nat δ loc hloc)]
  · intro a ha
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,List.mem_toFinset.mp (LocalSearch.seed_subset fs r hb),rfl⟩)
lemma fuel_bound {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
    d*Rounding.cap d (IntegralAssembly.gamma/16) ≤ (fuelPoly.eval (pack distance fs r).length) := by
  let L := (pack distance fs r).length
  have hd : d≤L := by
    simp only [L,pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,List.length_replicate]
    omega
  have hc := GlobalAssembly.cap_polynomial d L hd
  have hdl : d≤L+2 := by omega
  change d*Rounding.cap d (IntegralAssembly.gamma/16)≤fuelPoly.eval L
  calc
    _ ≤ (L+2)*((⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(L+2)^2) := Nat.mul_le_mul hdl hc
    _ = _ := by simp only [fuelPoly,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]; ring
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]
lemma executableAnchorFuel_spec (δ : V→V→ℕ) (fs : List V) (D : Finset V) (r n M : ℕ)
    (hfs : fs.Nodup) (hr : 0<r) (hrF : r≤fs.length)
    (hδ : ∀ p∈D,∀ i∈fs.toFinset,(δ p i:ℝ)=dist p i)
    (hM : ∀ p∈D,∀ i∈fs.toFinset,δ p i≤M) (hn : D.card*M≤n) :
    let S := executableDescent fs (natCost δ D) 5 n (fs.take r).toFinset
    S⊆fs.toFinset ∧ S.Nonempty ∧ S.card=r ∧ WidthLocalMin fs.toFinset D S 5 ∧
      ∀ O : Finset V,O.Nonempty→O⊆fs.toFinset→O.card≤r→cost D S≤5*cost D O := by
  dsimp only
  let S := executableDescent fs (natCost δ D) 5 n (fs.take r).toFinset
  have hp := executableDescent_properties fs (natCost δ D) 5 n (fs.take r).toFinset (seed_subset fs r)
  have hc : S.card=r:=hp.2.1.trans (seed_card fs r hfs hrF)
  have hs : S.Nonempty:=Finset.card_pos.mp (by rw [hc]; exact hr)
  have hm := executableDescent_min fs (natCost δ D) 5 n (fs.take r).toFinset (seed_subset fs r)
    ((natCost_le δ fs.toFinset D _ (seed_subset fs r) M hM).trans hn)
  have hlocal : WidthLocalMin fs.toFinset D S 5 := by
    intro U hUF hcard hrem hadd
    rw [←natCost_cast δ fs.toFinset D S hp.1 hδ,←natCost_cast δ fs.toFinset D U hUF hδ]
    exact_mod_cast hm U (candidate_of_exchange _ _ _ _ hUF hcard hrem hadd)
  refine ⟨hp.1,hs,hc,hlocal,?_⟩
  intro O hO hOF hOr
  exact local_five_approx _ _ _ O hs hO hp.1 hlocal hOF (by rw [hc]; exact hOr)
end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open RationalLeaves LocalSearch
lemma integral_spec {m d : ℕ} [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (r : ℕ)
    (hfs : fs.Nodup) (hr : 0<r) (hrF : r≤fs.length)
    (hδ : ∀ j,∀ i∈fs.toFinset,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈fs.toFinset,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ S : Finset (Fin m),
      run (pack (fun i j=>(δ (loc j) i:ℚ)) fs r)=BinaryFiniteContext.setBits (S.image original) ∧
      S⊆fs.toFinset ∧ S.Nonempty ∧ S.card=r ∧ WidthLocalMin fs.toFinset (Finset.univ.image loc) S 5 ∧
      ∀ O : Finset (Fin m),O.Nonempty→O⊆fs.toFinset→O.card≤r→
        cost (Finset.univ.image loc) S≤5*cost (Finset.univ.image loc) O := by
  refine ⟨_,run_pack δ loc hloc fs r,?_⟩
  apply executableAnchorFuel_spec δ fs (Finset.univ.image loc) r _
    (Rounding.cap d (IntegralAssembly.gamma/16)) hfs hr hrF
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hδ j i hi
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hM j i hi
  · rw [Finset.card_image_of_injective _ hloc,Finset.card_univ,Fintype.card_fin]
    exact fuel_bound _ fs r
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
