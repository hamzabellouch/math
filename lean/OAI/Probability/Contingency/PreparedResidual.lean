import Mathlib
import OAI.Probability.Contingency.WeightedSampler

namespace OAI

/-! Prepared Residual. -/

noncomputable section


open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

def groupMass (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j s : ℕ) : ℝ :=
  ((Finset.univ.filter fun f : Fin s→Bool => (run draw (encodeNat N++(ws.flatten++rest)) f).state=none ∧
    Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0)
      (BinarySubtract.value ((run draw (encodeNat N++(ws.flatten++rest)) f).memory.stack 5))=some j).card:ℝ)/2^s

theorem group_sum (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j s : ℕ) :
    groupMass N ws rest j s=∑ u : Fin (N+1),
      if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then
        WeightedSampler.storedMass N (ws.flatten++rest) u s else 0 := by
  classical
  let input := encodeNat N++(ws.flatten++rest)
  have point (f : Fin s→Bool) :
      (if (run draw input f).state=none ∧ Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0)
            (BinarySubtract.value ((run draw input f).memory.stack 5))=some j then (1:ℝ) else 0)=
        ∑ u : Fin (N+1),if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then
          (if (run draw input f).state=none ∧ (run draw input f).memory.stack 5=(IntegerDraw.integerWord N u).reverse then (1:ℝ) else 0) else 0 := by
    by_cases hh : (run draw input f).state=none
    · obtain ⟨u,hu,h6,h7,hi,ho⟩ := WeightedSampler.first_safe N (ws.flatten++rest) (List.ofFn f) hh
      change (run draw input f).memory.stack 5=(IntegerDraw.integerWord N u).reverse at hu
      have hv : BinarySubtract.value ((run draw input f).memory.stack 5)=u.val := by
        rw [hu,WeightedSampler.reverse_value,IntegerDraw.integerWord_value]
      rw [Finset.sum_eq_single u]
      · simp only [hh,true_and,hu,ite_true,WeightedSampler.reverse_value,IntegerDraw.integerWord_value]
      · intro v _ hne
        have hn : (run draw input f).memory.stack 5≠(IntegerDraw.integerWord N v).reverse := by
          intro he
          have hvu : u.val=v.val := by
            have hh' := congrArg (fun bs => BinaryTrial.beValue bs.reverse) (hu.symm.trans he)
            simpa using hh'
          exact hne (Fin.ext hvu.symm)
        simp [hn]
      · simp
    · simp [hh]
  unfold groupMass
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  change (∑ f : Fin s→Bool,if (run draw input f).state=none ∧ _ then (1:ℝ) else 0)/2^s=_
  rw [show (∑ f : Fin s→Bool,if (run draw input f).state=none ∧ Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) (BinarySubtract.value ((run draw input f).memory.stack 5))=some j then (1:ℝ) else 0)=_ from Finset.sum_congr rfl (fun f _ => point f)]
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hs : Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j
  · simp only [hs,ite_true,WeightedSampler.storedMass,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rfl
  · simp [hs]

 
theorem group_limit (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j : ℕ)
    (htotal : WeightedScan.weightTotal ws=N+1) :
    Tendsto (groupMass N ws rest j) atTop
      (nhds ((Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ))) := by
  classical
  have hc : (∑ u : Fin (N+1),if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then (1:ℕ) else 0)=
      Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j := by
    change (∑ u : Fin (N+1),(fun x : ℕ => if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) x=some j then (1:ℕ) else 0) u.val)=_
    rw [Fin.sum_univ_eq_sum_range (fun x => if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) x=some j then (1:ℕ) else 0) (N+1)]
    have ht : Contingency.IntegerDraw.total (WeightedScan.indexedWeights ws 0)=N+1 :=
      (WeightedScan.indexed_total ws 0).trans htotal
    rw [← ht]
    exact Contingency.IntegerDraw.scan_count _ _
  have hcr : (∑ u : Fin (N+1),if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then (1:ℝ) else 0)=
      (Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ) := by exact_mod_cast hc
  have he : (∑ u : Fin (N+1),if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then
      (1/(N+1:ℝ)) else 0)=(Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ) := by
    rw [← hcr,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  rw [← he]
  have hh := tendsto_finsetSum (Finset.univ : Finset (Fin (N+1))) (fun u _ =>
    show Tendsto (fun s => if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then
      WeightedSampler.storedMass N (ws.flatten++rest) u s else 0) atTop
      (nhds (if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then 1/(N+1:ℝ) else 0)) from by
      split_ifs
      · exact WeightedSampler.stored_uniform N (ws.flatten++rest) u
      · exact tendsto_const_nhds)
  have heq : groupMass N ws rest j=(fun s => ∑ u : Fin (N+1),if Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j then WeightedSampler.storedMass N (ws.flatten++rest) u s else 0) := by
    funext s
    exact group_sum N ws rest j s
  rw [heq]
  exact hh

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

theorem mass_upper (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j s : ℕ)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    mass program (encodeNat N++(ws.flatten++rest)) (List.replicate j false) s ≤ groupMass N ws rest j s := by
  classical
  unfold mass groupMass
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun f : Fin s→Bool => (run program (encodeNat N++(ws.flatten++rest)) f).state=none ∧
      (run program (encodeNat N++(ws.flatten++rest)) f).memory.outputRev.reverse=List.replicate j false) ⊆
    (Finset.univ.filter fun f : Fin s→Bool => (run draw (encodeNat N++(ws.flatten++rest)) f).state=none ∧
      Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0)
        (BinarySubtract.value ((run draw (encodeNat N++(ws.flatten++rest)) f).memory.stack 5))=some j) from by
    intro f hf
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hf ⊢
    obtain ⟨k,u,hk,hscan,hu,ho⟩ := halted_output N ws rest (List.ofFn f) hlen htotal hf.1
    change (run program (encodeNat N++(ws.flatten++rest)) f).memory.outputRev=List.replicate k false at ho
    have hkj : k=j := by
      have he := congrArg List.length hf.2
      simpa only [List.length_reverse,ho,List.length_replicate] using he
    subst k
    refine ⟨first_returned (List.ofFn f) _ hf.1,?_⟩
    change (run draw (encodeNat N++(ws.flatten++rest)) f).memory.stack 5=(IntegerDraw.integerWord N u).reverse at hu
    rw [hu,WeightedSampler.reverse_value,IntegerDraw.integerWord_value]
    exact hscan)

theorem mass_lower (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j s : ℕ)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    groupMass N ws rest j s ≤ mass program (encodeNat N++(ws.flatten++rest)) (List.replicate j false) (s+delay N ws) := by
  classical
  let e : Fin s→Fin (s+delay N ws) := Fin.castAdd (delay N ws)
  have hi : Function.Injective e := by
    intro i j h; exact Fin.ext (congrArg (fun k : Fin (s+delay N ws) => k.val) h)
  let p : (Fin s→Bool)→Prop := fun f => (run draw (encodeNat N++(ws.flatten++rest)) f).state=none ∧
    Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0)
      (BinarySubtract.value ((run draw (encodeNat N++(ws.flatten++rest)) f).memory.stack 5))=some j
  have he := CoordinateLaw.probability_restrict e hi p
  simp only [Fintype.card_fin] at he
  unfold groupMass mass
  change ((Finset.univ.filter p).card:ℝ)/2^s≤_
  rw [← he]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show
    (Finset.univ.filter fun f : Fin (s+delay N ws)→Bool => p (f∘e)) ⊆
    (Finset.univ.filter fun f : Fin (s+delay N ws)→Bool => (run program (encodeNat N++(ws.flatten++rest)) f).state=none ∧
      (run program (encodeNat N++(ws.flatten++rest)) f).memory.outputRev.reverse=List.replicate j false) from by
    intro f hf
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hf ⊢
    change (run draw (encodeNat N++(ws.flatten++rest)) (f∘e)).state=none ∧ _ at hf
    obtain ⟨u,hu,h6,h7,hin,hout⟩ := WeightedSampler.first_safe N (ws.flatten++rest) (List.ofFn (f∘e)) hf.1
    change (run draw (encodeNat N++(ws.flatten++rest)) (f∘e)).memory.stack 5=(IntegerDraw.integerWord N u).reverse at hu
    have hs : Contingency.IntegerDraw.scan (WeightedScan.indexedWeights ws 0) u.val=some j := by
      have hg := hf.2
      rw [hu,WeightedSampler.reverse_value,IntegerDraw.integerWord_value] at hg
      exact hg
    have ht : (List.ofFn f).take s=List.ofFn (f∘e) := by
      rw [List.ofFn_add]
      simp only [List.take_append,List.length_ofFn,Nat.sub_self,List.take_zero,List.append_nil]
      rw [List.take_of_length_le (by simp)]
      congr 2
    have hc := completes N ws rest (List.ofFn f) s j u hlen htotal
      ((List.length_ofFn (f:=f)).symm.le)
      (by rw [ht]; exact hf.1) (by rw [ht]; exact hu) hs
    refine ⟨hc.1,?_⟩
    have ho : (run program (encodeNat N++(ws.flatten++rest)) f).memory.outputRev=List.replicate j false := hc.2
    rw [ho,List.reverse_replicate])

theorem stack_law (N : ℕ) (ws : List (List Bool)) (rest : List Bool) (j : ℕ)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    Tendsto (mass program (encodeNat N++(ws.flatten++rest)) (List.replicate j false)) atTop
      (nhds ((Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ))) := by
  obtain ⟨r,hr⟩ := mass_limit_exists program (encodeNat N++(ws.flatten++rest)) (List.replicate j false)
  have hg := group_limit N ws rest j htotal
  have hu : r≤(Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ) :=
    le_of_tendsto_of_tendsto' hr hg (fun s => mass_upper N ws rest j s hlen htotal)
  have hl : (Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ)≤r :=
    le_of_tendsto_of_tendsto' hg (hr.comp (tendsto_add_atTop_nat (delay N ws))) (fun s => mass_lower N ws rest j s hlen htotal)
  simpa only [le_antisymm hu hl] using hr

 

theorem cached_selector (N : ℕ) (ws : List (List Bool)) (rest : List Bool)
    (hlen : ∀ w∈ws,w.length=N.size+1) (htotal : WeightedScan.weightTotal ws=N+1) :
    (∀ (t : ℕ) (f : Fin t→Bool),(machine.run (encodeNat N++(ws.flatten++rest)) f).state=none →
      ∃ j<ws.length,(machine.run (encodeNat N++(ws.flatten++rest)) f).outputRev.reverse=List.replicate j false) ∧
    (∀ j,Tendsto (machine.mass (encodeNat N++(ws.flatten++rest)) (List.replicate j false)) atTop
      (nhds ((Contingency.IntegerDraw.weight (WeightedScan.indexedWeights ws 0) j:ℝ)/(N+1:ℝ)))) ∧
    Summable (machine.tail (encodeNat N++(ws.flatten++rest))) ∧
    Tendsto (machine.tail (encodeNat N++(ws.flatten++rest))) atTop (nhds 0) ∧
    (∑' s,machine.tail (encodeNat N++(ws.flatten++rest)) s)≤70*(N.size:ℝ)+42+2*delay N ws := by
  refine ⟨?_,?_,charged_time N ws rest hlen htotal⟩
  · apply safe_compile program _ (fun out => ∃ j<ws.length,out=List.replicate j false)
    intro t f hh
    obtain ⟨j,u,hj,hs,hu,ho⟩ := halted_output N ws rest (List.ofFn f) hlen htotal hh
    refine ⟨j,hj,?_⟩
    change (run program (encodeNat N++(ws.flatten++rest)) f).memory.outputRev=List.replicate j false at ho
    rw [ho,List.reverse_replicate]
  · intro j
    exact mass_limit_compile program _ _ _ (stack_law N ws rest j hlen htotal)

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

def cacheMaximum (weights : List ℕ) : ℕ := weights.sum-1

def cacheWords (weights : List ℕ) : List (List Bool) :=
  weights.map (BinarySubtract.bits ((cacheMaximum weights).size+1))

def cacheInput (weights : List ℕ) (rest : List Bool) : List Bool :=
  encodeNat (cacheMaximum weights)++((cacheWords weights).flatten++rest)

def integerEntries : List ℕ→ℕ→List (ℕ×ℕ)
  | [],_ => []
  | w::ws,i => (i,w)::integerEntries ws (i+1)

theorem member_le_sum (weights : List ℕ) (x : ℕ) (hx : x∈weights) : x≤weights.sum := by
  induction weights with
  | nil => simp at hx
  | cons a as ih =>
    simp only [List.mem_cons] at hx
    simp only [List.sum_cons]
    rcases hx with rfl|hx
    · omega
    · have hh := ih hx; omega

theorem cache_width (weights : List ℕ) (hp : 0<weights.sum) :
    ∀ w∈cacheWords weights,w.length=(cacheMaximum weights).size+1 := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  apply BinarySubtract.bits_length
  have hmax : cacheMaximum weights+1=weights.sum := by dsimp [cacheMaximum]; omega
  have hb : cacheMaximum weights<2^(cacheMaximum weights).size := Nat.size_le.mp (le_refl _)
  have hxsum := member_le_sum weights x hx
  rw [pow_succ]
  omega

theorem cache_total (weights : List ℕ) (hp : 0<weights.sum) :
    WeightedScan.weightTotal (cacheWords weights)=cacheMaximum weights+1 := by
  have hmax : cacheMaximum weights+1=weights.sum := by dsimp [cacheMaximum]; omega
  rw [hmax]
  unfold WeightedScan.weightTotal cacheWords
  simp only [List.map_map,Function.comp_def,BinarySubtract.bits_value]
  have he : (weights.map fun x => x)=weights := by induction weights <;> simp_all
  rw [he]

theorem cache_entries (weights : List ℕ) (i : ℕ) :
    WeightedScan.indexedWeights (cacheWords weights) i=integerEntries weights i := by
  have hh (n : ℕ) (as : List ℕ) (j : ℕ) :
      WeightedScan.indexedWeights (as.map (BinarySubtract.bits n)) j=integerEntries as j := by
    induction as generalizing j with
    | nil => rfl
    | cons a as ih => simp [WeightedScan.indexedWeights,integerEntries,ih]
  exact hh _ _ _

 

theorem integer_cache_sampler (weights : List ℕ) (rest : List Bool) (hp : 0<weights.sum) :
    (∀ (t : ℕ) (f : Fin t→Bool),(machine.run (cacheInput weights rest) f).state=none →
      ∃ j<weights.length,(machine.run (cacheInput weights rest) f).outputRev.reverse=List.replicate j false) ∧
    (∀ j,Tendsto (machine.mass (cacheInput weights rest) (List.replicate j false)) atTop
      (nhds ((Contingency.IntegerDraw.weight (integerEntries weights 0) j:ℝ)/(weights.sum:ℝ)))) ∧
    Summable (machine.tail (cacheInput weights rest)) ∧
    Tendsto (machine.tail (cacheInput weights rest)) atTop (nhds 0) ∧
    (∑' s,machine.tail (cacheInput weights rest) s)≤
      78*((cacheMaximum weights).size:ℝ)+58+10*((cacheMaximum weights).size+2)*weights.length := by
  have hc := cached_selector (cacheMaximum weights) (cacheWords weights) rest
    (cache_width weights hp) (cache_total weights hp)
  have hmax : cacheMaximum weights+1=weights.sum := by dsimp [cacheMaximum]; omega
  have hlen : (cacheWords weights).length=weights.length := by simp [cacheWords]
  have hreal : (cacheMaximum weights:ℝ)+1=(weights.sum:ℝ) := by exact_mod_cast hmax
  refine ⟨?_,?_,hc.2.2.1,hc.2.2.2.1,?_⟩
  · simpa only [cacheInput,hlen] using hc.1
  · simpa only [cacheInput,cache_entries,hreal] using hc.2.1
  · have ht := hc.2.2.2.2
    dsimp only [delay] at ht
    rw [hlen] at ht
    push_cast at ht
    dsimp only [cacheInput]
    nlinarith

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

 

 

 

open scoped BigOperators
open Filter
namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

theorem entries_below (ws : List ℕ) (i j : ℕ) (hj : j < i) :
    Contingency.IntegerDraw.weight (integerEntries ws i) j=0 := by
  induction ws generalizing i with
  | nil => rfl
  | cons a as ih =>
    have hn : i≠j := by omega
    simp [integerEntries,Contingency.IntegerDraw.weight,hn]
    exact ih (i+1) (by omega)

theorem entries_lookup (ws : List ℕ) (i j : ℕ) :
    Contingency.IntegerDraw.weight (integerEntries ws i) (i+j)=ws.getD j 0 := by
  induction ws generalizing i j with
  | nil => simp [integerEntries,Contingency.IntegerDraw.weight]
  | cons a as ih =>
    cases j with
    | zero =>
      have hz := entries_below as (i+1) i (by omega)
      simp only [Nat.add_zero,integerEntries,Contingency.IntegerDraw.weight,List.map_cons,List.sum_cons,ite_true]
      change a+Contingency.IntegerDraw.weight (integerEntries as (i+1)) i=_
      rw [hz]
      simp
    | succ j =>
      have hn : i≠i+(j+1) := by omega
      simp only [integerEntries,Contingency.IntegerDraw.weight,List.map_cons,List.sum_cons,hn,ite_false,Nat.zero_add]
      change Contingency.IntegerDraw.weight (integerEntries as (i+1)) (i+(j+1))=_
      rw [show i+(j+1)=(i+1)+j by omega,ih]
      simp

theorem finite_weights_law {M : ℕ} (w : Fin M→ℕ) (hw : 0<∑ j,w j) (rest : List Bool) (j : Fin M) :
    Tendsto (machine.mass (cacheInput (List.ofFn w) rest) (List.replicate j.val false)) atTop
      (nhds ((w j:ℝ)/(∑ a,w a:ℕ))) := by
  have hp : 0<(List.ofFn w).sum := by simpa only [List.sum_ofFn] using hw
  have h := (integer_cache_sampler (List.ofFn w) rest hp).2.1 j.val
  have hl := entries_lookup (List.ofFn w) 0 j.val
  simp only [Nat.zero_add] at hl
  rw [hl,List.getD_eq_getElem _ _ (by simp)] at h
  simpa only [List.getElem_ofFn,List.sum_ofFn] using h

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

namespace Contingency
open BitModel.StackCode.PaddedWeightedSampler
noncomputable section
variable {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
local instance preparedResidualVectorTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _
variable (hrc : (∑ i,r i)=∑ j,c j)

 

def residualVector : Fin (Fintype.card (Tables r c))→ℕ :=
  fun j => arbitraryResidual r c hrc ((Fintype.equivFin (Tables r c)).symm j)

theorem residualVector_sum : (∑ j,residualVector r c hrc j)=∑ X,arbitraryResidual r c hrc X := by
  unfold residualVector
  exact Equiv.sum_comp (Fintype.equivFin (Tables r c)).symm _

 

theorem residual_cache_law (rest : List Bool) (X : Tables r c) :
    Tendsto (machine.mass (cacheInput (List.ofFn (residualVector r c hrc)) rest)
      (List.replicate ((Fintype.equivFin (Tables r c)) X).val false)) atTop
      (nhds ((arbitraryResidual r c hrc X:ℝ)/(Fintype.card (Tables r c)*2^(arbitraryDraw r c hrc (2*Parameters.D m n (∑ i,r i))).bits:ℝ))) := by
  have hp : 0<∑ j,residualVector r c hrc j := by
    rw [residualVector_sum]
    exact arbitraryResidual_total_pos r c hrc
  have hh := BitModel.StackCode.PaddedWeightedSampler.finite_weights_law (residualVector r c hrc) hp rest
    ((Fintype.equivFin (Tables r c)) X)
  have hw : residualVector r c hrc ((Fintype.equivFin (Tables r c)) X)=arbitraryResidual r c hrc X := by
    simp [residualVector]
  rw [hw,residualVector_sum,(arbitraryResidual_data r c hrc).2] at hh
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh

end
end Contingency

 

 

open scoped BigOperators
open Filter

namespace Contingency.BitModel.StackCode.PaddedWeightedSampler
noncomputable section

 

theorem cache_maximum_size_le (weights : List ℕ) (D R : ℕ)
    (hp : 0 < (weights).sum) (hM : (weights).length ≤ 2 ^ D)
    (hs : (weights).sum = (weights).length * 2 ^ R) :
    (cacheMaximum weights).size ≤ D + R := by
  apply Nat.size_le.mpr
  have hsum : (weights).sum ≤ 2 ^ (D + R) := by
    rw [hs, pow_add]
    exact Nat.mul_le_mul_right _ hM
  dsimp only [cacheMaximum]
  exact (Nat.sub_lt hp (by omega)).trans_le hsum

 

theorem integer_cache_rare_time (weights : List ℕ) (rest : List Bool) (D R : ℕ)
    (hp : 0 < (weights).sum) (hM : (weights).length ≤ 2 ^ D)
    (hs : (weights).sum = (weights).length * 2 ^ R) :
    (1 / (2 : ℝ) ^ D) * (∑' t, machine.tail (cacheInput weights rest) t) ≤
      (100 * (D + R + 1) : ℕ) := by
  have ht := (integer_cache_sampler weights rest hp).2.2.2.2
  have hsize := cache_maximum_size_le weights D R hp hM hs
  have hδ0 : (0 : ℝ) ≤ 1 / 2 ^ D := by positivity
  have hδ1 : (1 : ℝ) / 2 ^ D ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hδM : (1 / (2 : ℝ) ^ D) * (weights).length ≤ 1 := by
    calc
      _ = ((weights).length : ℝ) / 2 ^ D := by ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hM)
  have hfirst := mul_le_mul_of_nonneg_right hδ1
    (show (0 : ℝ) ≤ 78 * (cacheMaximum weights).size + 58 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hδM
    (show (0 : ℝ) ≤ 10 * ((cacheMaximum weights).size + 2) by positivity)
  have hsizeR : ((cacheMaximum weights).size : ℝ) ≤ (D + R : ℕ) := by
    exact_mod_cast hsize
  have hsum0 : (0 : ℝ) ≤ (D + R : ℕ) := Nat.cast_nonneg _
  calc
    _ ≤ (1 / (2 : ℝ) ^ D) *
        (78 * (cacheMaximum weights).size + 58 +
          10 * ((cacheMaximum weights).size + 2) * (weights).length) :=
      mul_le_mul_of_nonneg_left ht hδ0
    _ = (1 / (2 : ℝ) ^ D) * (78 * (cacheMaximum weights).size + 58) +
        10 * ((cacheMaximum weights).size + 2) *
          ((1 / (2 : ℝ) ^ D) * (weights).length) := by ring
    _ ≤ (78 * (cacheMaximum weights).size + 58) +
        10 * ((cacheMaximum weights).size + 2) := by
      simpa only [one_mul, mul_one] using add_le_add hfirst hsecond
    _ ≤ (100 * (D + R + 1) : ℕ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at *
      nlinarith only [hsizeR, hsum0]

end
end Contingency.BitModel.StackCode.PaddedWeightedSampler

namespace Contingency
open BitModel.StackCode.PaddedWeightedSampler
noncomputable section

 

def residualSelectionBudget (s : ℕ) : ℕ :=
  100 * (26 ^ 2 * (s + 3) ^ 16 +
    (32 * (s + 2 * (26 ^ 2 * (s + 3) ^ 16) + 3) ^ 2) ^ 300 + 1)

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local instance preparedResidualBudgetTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _
variable (hrc : (∑ i, r i) = ∑ j, c j)
local notation "D" => Parameters.D m n (∑ i, r i)
local notation "p" => arbitraryDraw r c hrc (2 * D)
local notation "weights" => List.ofFn (residualVector r c hrc)

 

theorem residual_cache_rare_time (rest : List Bool) :
    (1 / (2 : ℝ) ^ D) * (∑' t, machine.tail (cacheInput weights rest) t) ≤
      (residualSelectionBudget (inputSize m n (∑ i, r i)) : ℕ) := by
  have hp : 0 < (weights).sum := by
    rw [List.sum_ofFn, residualVector_sum]
    exact arbitraryResidual_total_pos r c hrc
  have hM : (weights).length ≤ 2 ^ D := by
    simpa only [List.length_ofFn, Nat.card_eq_fintype_card] using
      Parameters.table_card_D_all r c hrc
  have hs : (weights).sum = (weights).length * 2 ^ (p).bits := by
    rw [List.sum_ofFn, residualVector_sum, (arbitraryResidual_data r c hrc).2,
      List.length_ofFn]
  have ht := integer_cache_rare_time weights rest D (p).bits hp hM hs
  have hD := Parameters.D_le_input m n (∑ i, r i)
  have hk : 1 ≤ 2 * D := by
    have := Parameters.D_positive m n (∑ i, r i)
    omega
  have hR := arbitraryDraw_bits_input r c hrc (2 * D) hk
  have hbase : inputSize m n (∑ i, r i) + 2 * D + 3 ≤
      inputSize m n (∑ i, r i) +
        2 * (26 ^ 2 * (inputSize m n (∑ i, r i) + 3) ^ 16) + 3 := by omega
  have hR' : (p).bits ≤
      (32 * (inputSize m n (∑ i, r i) +
        2 * (26 ^ 2 * (inputSize m n (∑ i, r i) + 3) ^ 16) + 3) ^ 2) ^ 300 := by
    calc
      _ ≤ (32 * (inputSize m n (∑ i, r i) + 2 * D + 3) ^ 2) ^ 300 := hR
      _ ≤ _ := by gcongr
  refine ht.trans ?_
  apply Nat.cast_le.mpr
  unfold residualSelectionBudget
  apply Nat.mul_le_mul_left
  omega

 

theorem residual_cache_corrected_limit (rest : List Bool) (X : Tables r c) :
    Tendsto
      (fun t => (1 - 1 / (2 : ℝ) ^ D) * (p).toLaw.mass X +
        (1 / (2 : ℝ) ^ D) *
          machine.mass (cacheInput weights rest)
            (List.replicate ((Fintype.equivFin (Tables r c)) X).val false) t)
      atTop (nhds (1 / (Nat.card (Tables r c) : ℝ))) := by
  classical
  let := tables_nonempty r c hrc
  have hM : Fintype.card (Tables r c) ≤ 2 ^ D := by
    simpa only [Nat.card_eq_fintype_card] using Parameters.table_card_D_all r c hrc
  have hk : 1 ≤ 2 * D := by
    have := Parameters.D_positive m n (∑ i, r i)
    omega
  have he := corrected_exact p D hM (arbitraryDraw_tv r c hrc (2 * D) hk) X
  change (1 - 1 / (2 : ℝ) ^ D) * (p).toLaw.mass X +
      (1 / (2 : ℝ) ^ D) * ((arbitraryResidual r c hrc X : ℝ) /
        (Fintype.card (Tables r c) * 2 ^ (p).bits : ℝ)) =
      1 / (Fintype.card (Tables r c) : ℝ) at he
  have hl := ((residual_cache_law r c hrc rest X).const_mul ((1 : ℝ) / 2 ^ D)).const_add
    ((1 - 1 / (2 : ℝ) ^ D) * (p).toLaw.mass X)
  simpa only [he, Nat.card_eq_fintype_card] using hl

 

theorem prepared_residual_stage (rest : List Bool) :
    (∀ (t : ℕ) (coins : Fin t → Bool),
      (machine.run (cacheInput weights rest) coins).state = none →
      ∃ j < Fintype.card (Tables r c),
        (machine.run (cacheInput weights rest) coins).outputRev.reverse =
          List.replicate j false) ∧
    Summable (machine.tail (cacheInput weights rest)) ∧
    Tendsto (machine.tail (cacheInput weights rest)) atTop (nhds 0) ∧
    (1 / (2 : ℝ) ^ D) * (∑' t, machine.tail (cacheInput weights rest) t) ≤
      (residualSelectionBudget (inputSize m n (∑ i, r i)) : ℕ) ∧
    (∀ X : Tables r c,
      Tendsto
        (fun t => (1 - 1 / (2 : ℝ) ^ D) * (p).toLaw.mass X +
          (1 / (2 : ℝ) ^ D) *
            machine.mass (cacheInput weights rest)
              (List.replicate ((Fintype.equivFin (Tables r c)) X).val false) t)
        atTop (nhds (1 / (Nat.card (Tables r c) : ℝ)))) := by
  have hp : 0 < (weights).sum := by
    rw [List.sum_ofFn, residualVector_sum]
    exact arbitraryResidual_total_pos r c hrc
  have hc := integer_cache_sampler weights rest hp
  exact ⟨by simpa only [List.length_ofFn] using hc.1, hc.2.2.1, hc.2.2.2.1,
    residual_cache_rare_time r c hrc rest, residual_cache_corrected_limit r c hrc rest⟩

end
end Contingency

end

end OAI
