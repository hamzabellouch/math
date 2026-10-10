import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalTree
import OAI.Combinatorics.SharpRamsey.Parameters.ReciprocalScales
import OAI.Combinatorics.SharpRamsey.Execution.VariableOutput

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence SupportMixtures Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω : Type*} [Fintype I] [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}
local instance flat_ActualReciprocalPopulation_1 : DecidableEq I := Classical.decEq _
local instance populationBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
  {d : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
  (hprod : ∀ i,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

theorem Book.original_population_loss
    (μ : Law Ω) (n : I→ℕ)
    (target : Ω→∀ i,Fin (n i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (t : BinaryTree I) (ht : Separated t)
    (hR : ∀ ω,∀ i∈labels t,∀ j,SharpLogRamsey.Incidence.Incident (target ω i j).2 (target ω i j).1)
    (GA : ∀ i,Fin (n i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (n i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈labels t,∀ j∈leftPath i t,
      goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hsecond : ∀ i∈labels t,∀ j∈rightPath i t,
      goodIncidence (p j) (r i) (goodA j) (goodB i)≤ε)
    (hself : ∀ i∈labels t,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈labels t,∀ j,∀ k∈insert i (leftPath i t),
      goodIncidence (μ.map (fun ω=>(target ω i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈labels t,∀ j,∀ k∈insert i (rightPath i t),
      goodIncidence (p k) (μ.map (fun ω=>(target ω i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈labels t,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
      ∑ ω,(μ.prod (familyLaw X Y).nullFree).mass ω*((∑ i∈labels t,(n i:ℝ))-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
        (fun _=>chronoRead b) (fun i=>List.ofFn (target ω.1 i)) z t (univ,univ)).length))≤
        (∑ i∈labels t,(n i:ℝ))*treeError (Nat.card K) τ t.height ε εA εB δA δB := by
  apply original_variable_loss (μ.prod (familyLaw X Y).nullFree).asPublic
    (fun _ : I=>banksLaw (K:=K) (V:=V) b) (fun y x=>SharpLogRamsey.Incidence.Incident x y)
    (fun ω i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
    (fun _=>chronoRead b) n (fun ω=>target ω.1) t (univ,univ) ht (fun ω=>hR ω.1)
  intro i hi j
  apply book.original_tree_target_loss X Y hdim hτ hτsmall hMA hMB hprod
    μ i t ht hi (fun ω=>(target ω i j).1) (fun ω=>(target ω i j).2)
    (GA i j) (GB i j) ε εA εB δA δB hε hεA hεB
  · intro k hk l hl
    exact hfirst k (plannedPath_subset i t hk) l hl
  · intro k hk l hl
    exact hsecond k (plannedPath_subset i t hk) l hl
  · intro k hk
    exact hself k (plannedPath_subset i t hk)
  · exact hmeanA i hi j
  · exact hmeanB i hi j
  · exact hbadA i hi j
  · exact hbadB i hi j

end
end SharpLogRamsey.ActualPivot

end

end OAI
