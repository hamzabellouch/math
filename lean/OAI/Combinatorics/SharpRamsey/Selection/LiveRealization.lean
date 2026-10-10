import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankContext
import OAI.Combinatorics.SharpRamsey.Selection.LiveFamilies

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ChronologicalTree
open BinaryTree Finset
open scoped Classical
variable {I : Type*} [LinearOrder I]
lemma liveTree_empty (fallback : I) : liveTree ∅ fallback=nil := by
  simp [liveTree,balanced,BinaryTree.map]
end SharpLogRamsey.ChronologicalTree

namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype I] [LinearOrder I] [Fintype Y₀] {d : ℕ} {b τ P H : ℝ}
local instance realDecEq : DecidableEq I := Classical.decEq _
local instance realizationBanksFintype : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

structure Realization (q : Law Y₀) where
  Ω : Type
  inst : Fintype Ω
  μ : Law Ω
  source : Ω→Y₀
  supports : Ω→I→Original (K:=K) (V:=V) d b
  marginal : μ.map source=q

attribute [instance] Realization.inst

variable (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)

include hb

theorem Book.live_realization
    (q : Law Y₀) (S : Finset I) (fallback : I)
    (p : I→Law (Projectivization K (Module.Dual K V)))
    (r : I→Law (Projectivization K V))
    (goodA : I→Finset (Projectivization K (Module.Dual K V)))
    (goodB : I→Finset (Projectivization K V)) (MA MB κA κB : I→ℝ)
    (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
    (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
    (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (counts : I→ℕ)
    (target : Y₀→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (hR : ∀ y,q.mass y≠0→∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target y i j).2 (target y i j).1)
    (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
      goodIncidence (q.map (fun y=>(target y i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
      goodIncidence (p k) (q.map (fun y=>(target y i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    ∃ e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q,
      (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
        ∑ ω,e.μ.mass ω*((∑ i∈S,(counts i:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b) (fun i=>List.ofFn (target (e.source ω) i)) z
          (liveTree S fallback) (univ,univ)).length))≤
        (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB := by
  by_cases hS : S.Nonempty
  · let e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q :=
      { Ω := {y // q.mass y≠0} × OriginalChoice (liveX S hS X) (liveY S hS Y)
        inst := inferInstance
        μ := q.nullFree.prod (familyLaw (liveX S hS X) (liveY S hS Y)).nullFree
        source := fun ω=>ω.1.val
        supports := fun ω=>liveOriginal S hS X Y hMA hMB hprod ω.2
        marginal := by
          rw [Law.prod_map_left]
          exact (q.nullFree_map id).trans (Law.map_id q) }
    refine ⟨e,?_⟩
    apply book.live_population_loss S hS X Y hdim hτ hτsmall hMA hMB hprod q.nullFree counts
      (fun y=>target y.val) fallback (fun y=>hR y.val y.property) GA GB ε εA εB δA δB hε hεA hεB
      hfirst hself
    · intro i hi j k hk hik
      rw [q.nullFree_map (fun y=>(target y i j).1)]
      exact hmeanA i hi j k hk hik
    · intro i hi j k hk hki
      rw [q.nullFree_map (fun y=>(target y i j).2)]
      exact hmeanB i hi j k hk hki
    · intro i hi j
      rw [q.nullFree_integral (fun y=>if (target y i j).1∈GA i j then (0:ℝ) else 1)]
      exact hbadA i hi j
    · intro i hi j
      rw [q.nullFree_integral (fun y=>if (target y i j).2∈GB i j then (0:ℝ) else 1)]
      exact hbadB i hi j
  · have hS' : S=∅ := not_nonempty_iff_eq_empty.mp hS
    let e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q :=
      { Ω := Y₀
        inst := inferInstance
        μ := q
        source := id
        supports := fun _ _=>emptyOriginal hdim hb
        marginal := Law.map_id q }
    refine ⟨e,?_⟩
    simp [hS',liveTree_empty,fullOutput_nil]
end
end SharpLogRamsey.ActualPivot

end

end OAI
