import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalPopulation
import OAI.Combinatorics.SharpRamsey.Windows.BalancedWindows
import OAI.Combinatorics.SharpRamsey.Selection.EmptySupports

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] [LinearOrder I]
local instance liveDecEq : DecidableEq I := Classical.decEq _

def liveRetraction (S : Finset I) (h : S.Nonempty) (i : I) : S :=
  if hi : i∈S then ⟨i,hi⟩ else ⟨h.choose,h.choose_spec⟩

omit [Fintype I] [LinearOrder I] in
lemma liveRetraction_mem (S : Finset I) (h : S.Nonempty) (i : I) (hi : i∈S) :
    (liveRetraction S h i).val=i := by simp [liveRetraction,hi]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {Ω : Type*} [Fintype Ω]
  {p : I→Law (Projectivization K (Module.Dual K V))}
  {r : I→Law (Projectivization K V)}
  {goodA : I→Finset (Projectivization K (Module.Dual K V))}
  {goodB : I→Finset (Projectivization K V)} {MA MB κA κB : I→ℝ}
local instance liveBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

variable (S : Finset I) (hS : S.Nonempty)
  (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))

abbrev liveX (i : I) := X (liveRetraction S hS i)
abbrev liveY (i : I) := Y (liveRetraction S hS i)

variable {d : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
  (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

abbrev liveOriginal (z : OriginalChoice (liveX S hS X) (liveY S hS Y)) (i : I) :
    Original (K:=K) (V:=V) d b :=
  originalFamily (liveX S hS X) (liveY S hS Y)
    (fun i=>hMA _ (liveRetraction S hS i).property)
    (fun i=>hMB _ (liveRetraction S hS i).property)
    (fun i=>hprod _ (liveRetraction S hS i).property) z i

theorem Book.live_population_loss
    (μ : Law Ω) (counts : I→ℕ)
    (target : Ω→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (fallback : I)
    (hR : ∀ ω,∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target ω i j).2 (target ω i j).1)
    (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
      goodIncidence (μ.map (fun ω=>(target ω i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
      goodIncidence (p k) (μ.map (fun ω=>(target ω i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈S,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈S,∀ j,(∑ ω,μ.mass ω*(if (target ω i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
      ∑ ω,(μ.prod (familyLaw (liveX S hS X) (liveY S hS Y)).nullFree).mass ω*
      ((∑ i∈S,(counts i:ℝ))-
       (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ.le hτsmall (liveOriginal S hS X Y hMA hMB hprod ω.2 i))
        (fun _=>chronoRead b) (fun i=>List.ofFn (target ω.1 i)) z (liveTree S fallback) (univ,univ)).length))≤
      (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB := by
  have hsubL (i j : I) (hj : j∈leftPath i (liveTree S fallback)) : j∈S := by
    rw [←liveTree_labels S fallback]
    exact leftPath_subset i _ hj
  have hsubR (i j : I) (hj : j∈rightPath i (liveTree S fallback)) : j∈S := by
    rw [←liveTree_labels S fallback]
    exact rightPath_subset i _ hj
  have hh := book.original_population_loss (liveX S hS X) (liveY S hS Y) hdim hτ hτsmall
    (fun i=>hMA _ (liveRetraction S hS i).property)
    (fun i=>hMB _ (liveRetraction S hS i).property)
    (fun i=>hprod _ (liveRetraction S hS i).property) μ counts target (liveTree S fallback)
    (liveTree_separated S fallback)
  simp only [liveTree_labels] at hh
  apply hh (fun ω=>hR ω) GA GB ε εA εB δA δB hε hεA hεB
  · intro i hi j hj
    simpa only [liveRetraction_mem S hS i hi,liveRetraction_mem S hS j (hsubL i j hj)] using
      hfirst i hi j (hsubL i j hj) (liveTree_left S fallback i j hj)
  · intro i hi j hj
    simpa only [liveRetraction_mem S hS i hi,liveRetraction_mem S hS j (hsubR i j hj)] using
      hfirst j (hsubR i j hj) i hi (liveTree_right S fallback i j hj)
  · intro i hi
    simpa only [liveRetraction_mem S hS i hi] using hself i hi
  · intro i hi j k hk
    rcases mem_insert.mp hk with hki|hk
    · subst k
      simpa only [liveRetraction_mem S hS i hi] using hmeanA i hi j i hi le_rfl
    · simpa only [liveRetraction_mem S hS k (hsubL i k hk)] using
        hmeanA i hi j k (hsubL i k hk) (liveTree_left S fallback i k hk).le
  · intro i hi j k hk
    rcases mem_insert.mp hk with hki|hk
    · subst k
      simpa only [liveRetraction_mem S hS i hi] using hmeanB i hi j i hi le_rfl
    · simpa only [liveRetraction_mem S hS k (hsubR i k hk)] using
        hmeanB i hi j k (hsubR i k hk) (liveTree_right S fallback i k hk).le
  · exact hbadA
  · exact hbadB

end
end SharpLogRamsey.ActualPivot

end

end OAI
