import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.OriginalFamilies

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

local instance reciprocalBanksFintype (b : ℝ) : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def goodIncidence (p : Law (Projectivization K (Module.Dual K V)))
    (r : Law (Projectivization K V))
    (A : Finset (Projectivization K (Module.Dual K V))) (B : Finset (Projectivization K V)) : ℝ :=
  (p.prod r).event (univ.filter (fun ay=>ay.1∈A ∧ ay.2∈B ∧ ay.1.rep ay.2.rep=0))

variable (X : ∀ i,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
  (Y : ∀ i,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
  {n : ℕ} {b τ P H : ℝ} (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hτ : 0<τ) (hτsmall : τ≤1/40000)
  (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
  (hprod : ∀ i,(Nat.card K:ℝ)^(n+3)*exp (-b)≤
    (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))

theorem Book.original_tree_target_loss
    (μ : Law Ω) (target : I) (t : BinaryTree I) (ht : Separated t) (hmem : target∈labels t)
    (a : Ω→Projectivization K (Module.Dual K V)) (c : Ω→Projectivization K V)
    (GA : Finset (Projectivization K (Module.Dual K V))) (GB : Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈plannedPath target t,∀ j∈leftPath i t,
      goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hsecond : ∀ i∈plannedPath target t,∀ j∈rightPath i t,
      goodIncidence (p j) (r i) (goodA j) (goodB i)≤ε)
    (hself : ∀ i∈plannedPath target t,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈insert target (leftPath target t),
      goodIncidence (μ.map a) (r i) GA (goodB i)≤εA)
    (hmeanB : ∀ i∈insert target (rightPath target t),
      goodIncidence (p i) (μ.map c) (goodA i) GB≤εB)
    (hbadA : (∑ ω,μ.mass ω*(if a ω∈GA then (0:ℝ) else 1))≤δA)
    (hbadB : (∑ ω,μ.mass ω*(if c ω∈GB then (0:ℝ) else 1))≤δB) :
    (∑ ω,(μ.prod (familyLaw X Y).nullFree).mass ω *
      (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z *
        targetFailure
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (originalFamily X Y hMA hMB hprod ω.2 i))
          (fun _=>chronoRead b) (a ω.1) (c ω.1) target t (univ,univ) z))≤
      20*(12*(Nat.card K:ℝ)*((4*exp 1)*(4*exp 1)*ε))*t.height^2+
        ((Nat.card K:ℝ)*((4*exp 1)*(4*exp 1)*ε)/τ+2*exp (-(Nat.card K:ℝ)))*t.height+
        δA+δB+((t.height:ℝ)+1)*
          (12*(Nat.card K:ℝ)*((4*exp 1)*εA)+12*(Nat.card K:ℝ)*((4*exp 1)*εB)) := by
  let ν := μ.prod (familyLaw X Y).nullFree
  have hdc (i j : I) :
      (∑ ω,ν.mass ω * density (originalFamily X Y hMA hMB hprod ω.2 i).B
        (originalFamily X Y hMA hMB hprod ω.2 j).A)≤
      (4*exp 1)*(4*exp 1)*goodIncidence (p i) (r j) (goodA i) (goodB j) := by
    rw [show (∑ ω,ν.mass ω * density (originalFamily X Y hMA hMB hprod ω.2 i).B
        (originalFamily X Y hMA hMB hprod ω.2 j).A)=
      ∑ z,(familyLaw X Y).nullFree.mass z * density (originalFamily X Y hMA hMB hprod z i).B
        (originalFamily X Y hMA hMB hprod z j).A from
      μ.prod_right_sum (familyLaw X Y).nullFree
        (fun z=>density (originalFamily X Y hMA hMB hprod z i).B
          (originalFamily X Y hMA hMB hprod z j).A)]
    exact originalFamily_density X Y hMA hMB hprod i j
  exact book.target_loss hdim hτ.le hτsmall ν.asPublic
    (fun ω i=>originalFamily X Y hMA hMB hprod ω.2 i) target t (univ,univ) ht hmem
    (by intros; exact ⟨subset_univ _,subset_univ _⟩)
    (fun ω=>a ω.1∈GA) (fun ω=>c ω.1∈GB) (fun ω=>a ω.1) (fun ω=>c ω.1)
    (by simp) (by simp) hτ ((4*exp 1)*(4*exp 1)*ε) ((4*exp 1)*εA) ((4*exp 1)*εB)
    δA δB (by positivity) (by positivity) (by positivity)
    (fun i hi j hj=>(hdc i j).trans (mul_le_mul_of_nonneg_left (hfirst i hi j hj) (by positivity)))
    (fun i hi j hj=>(hdc j i).trans (mul_le_mul_of_nonneg_left (hsecond i hi j hj) (by positivity)))
    (fun i hi=>(hdc i i).trans (mul_le_mul_of_nonneg_left (hself i hi) (by positivity)))
    (fun i hi=>(originalFamily_first_target X Y hMA hMB hprod μ a GA i).trans
      (mul_le_mul_of_nonneg_left (hmeanA i hi) (by positivity)))
    (fun i hi=>(originalFamily_second_target X Y hMA hMB hprod μ c GB i).trans
      (mul_le_mul_of_nonneg_left (hmeanB i hi) (by positivity)))
    (by
      have hh := (μ.prod_left_sum (familyLaw X Y).nullFree
        (fun ω=>if a ω∈GA then (0:ℝ) else 1)).le.trans hbadA
      convert hh using 1
      congr 1
      funext outcome
      congr 1
      by_cases hgood : a outcome.1∈GA <;> simp only [hgood,ite_true,ite_false])
    (by
      have hh := (μ.prod_left_sum (familyLaw X Y).nullFree
        (fun ω=>if c ω∈GB then (0:ℝ) else 1)).le.trans hbadB
      convert hh using 1
      congr 1
      funext outcome
      congr 1
      by_cases hgood : c outcome.1∈GB <;> simp only [hgood,ite_true,ite_false])

end
end SharpLogRamsey.ActualPivot

end

end OAI
