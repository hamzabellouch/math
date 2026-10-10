import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.LiveRealization
import OAI.Combinatorics.SharpRamsey.Windows.GoodPopulation

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {A B J : Type*} [Fintype A] [Fintype B] [Fintype J] [DecidableEq J]
lemma Law.marginal_fst_map (q : Law (J→A×B)) (i : J) :
    (q.marginal i).fst=q.map (fun y=>(y i).1) := by
  rw [←Law.map_fst,Law.marginal,Law.map_comp]
  rfl
lemma Law.marginal_snd_map (q : Law (J→A×B)) (i : J) :
    (q.marginal i).snd=q.map (fun y=>(y i).2) := by
  rw [←Law.map_snd,Law.marginal,Law.map_comp]
  rfl
lemma Law.map_bad_sum (q : Law A) (f : A→B) (S : Finset B) :
    (∑ y,q.mass y*(if f y∈S then (0:ℝ) else 1))=(q.map f).event (univ\S) := by
  rw [←q.sum_map f (fun b=>if b∈S then (0:ℝ) else 1)]
  have hs : univ\S=univ.filter (fun b=>b∉S) := by ext b; simp
  rw [Law.event,hs]
  simp only [sum_filter,ite_not,mul_ite,mul_zero,mul_one]
end
end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection.Windows
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
local instance goodBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance
local instance goodDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
  (z : (model w n k p θ G t).FreshHistory)
local instance goodBlockDec : DecidableEq (Block w) := Classical.decEq _

theorem good_population_realization
    (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
    (bad : Finset ((model w n k p θ G t).Index z.1))
    (live : Finset (Fin w)) (fallback : Fin w)
    (hgood : ∀ i∈live,∀ c,((model w n k p θ G t).representative z (i,c))∉bad)
    (GA : (model w n k p θ G t).Index z.1→Finset (Projectivization K (Module.Dual K V)))
    (GB : (model w n k p θ G t).Index z.1→Finset (Projectivization K V))
    (MA MB κA κB : (model w n k p θ G t).Index z.1→ℝ)
    (X : ∀ i,i∉bad→AuxiliarySupport (((model w n k p θ G t).tupleLaw z.1).marginal i).fst
      (GA i) (MA i) (κA i))
    (Y : ∀ i,i∉bad→AuxiliarySupport (((model w n k p θ G t).tupleLaw z.1).marginal i).snd
      (GB i) (MB i) (κB i))
    (hMA : ∀ i,0<MA i) (hMB : ∀ i,0<MB i)
    (hprod : ∀ i∈live,
      let a:=(model w n k p θ G t).representative z (i,false)
      let c:=(model w n k p θ G t).representative z (i,true)
      (Nat.card K:ℝ)^(d+3)*exp (-b)≤(MA a*exp (-κA a)/2)*(MB c*exp (-κB c)/2))
    (hR : ∀ y,((model w n k p θ G t).tupleLaw z.1).mass y≠0→∀ i,
      SharpLogRamsey.Incidence.Incident (y i).2 (y i).1)
    (ε δA δB : ℝ) (hε : 0≤ε)
    (hinc : ∀ i j,
      position ((model w n k p θ G t).origin z.1 i)<position ((model w n k p θ G t).origin z.1 j)→
      ((i∉bad ∧ j∈otherRepresentatives ((model w n k p θ G t).embedding z.1)
        ((model w n k p θ G t).owner z.1) z.2 i) ∨
       (j∉bad ∧ i∈otherRepresentatives ((model w n k p θ G t).embedding z.1)
        ((model w n k p θ G t).owner z.1) z.2 j))→
      goodIncidence (((model w n k p θ G t).tupleLaw z.1).marginal i).fst
        (((model w n k p θ G t).tupleLaw z.1).marginal j).snd (GA i) (GB j)≤ε)
    (hbadA : ∀ i,i∉bad→(((model w n k p θ G t).tupleLaw z.1).marginal i).fst.event (univ\GA i)≤δA)
    (hbadB : ∀ i,i∉bad→(((model w n k p θ G t).tupleLaw z.1).marginal i).snd.event (univ\GB i)≤δB) :
    ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) ((model w n k p θ G t).tupleLaw z.1),
      (∑ a,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass a*
        ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b)
          (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) a
          (liveTree live fallback) (univ,univ)).length))≤
        (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
          treeError (Nat.card K) τ (liveTree live fallback).height ε ε ε δA δB := by
  let M:=model w n k p θ G t
  let early:=fun i=>M.representative z (i,false)
  let late:=fun i=>M.representative z (i,true)
  apply book.live_realization hdim hb hτ hτsmall (M.tupleLaw z.1) live fallback
    (fun i=>(M.tupleLaw z.1|>.marginal (early i)).fst)
    (fun i=>(M.tupleLaw z.1|>.marginal (late i)).snd)
    (fun i=>GA (early i)) (fun i=>GB (late i))
    (fun i=>MA (early i)) (fun i=>MB (late i)) (fun i=>κA (early i)) (fun i=>κB (late i))
    (fun i=>X (early i) (hgood i i.property false))
    (fun i=>Y (late i) (hgood i i.property true))
    (fun i _=>hMA (early i)) (fun i _=>hMB (late i)) hprod
    (fun i=>(goodMiddle w n k p θ G t z bad i).card)
    (fun y i j=>y (goodTarget w n k p θ G t z bad i j))
    (fun y hy i _ j=>hR y hy _) (fun i j=>GA (goodTarget w n k p θ G t z bad i j))
    (fun i j=>GB (goodTarget w n k p θ G t z bad i j)) ε ε ε δA δB hε hε hε
  · intro i hi j hj hij
    apply hinc _ _ (representative_before w n k p θ G t z i j hij false true)
    exact Or.inl ⟨hgood i hi false,representative_other w n k p θ G t z (j,true) (i,false) (by simp)⟩
  · intro i hi
    apply hinc _ _ (representatives_straddle w n k p θ G t z i)
    exact Or.inl ⟨hgood i hi false,representative_other w n k p θ G t z (i,true) (i,false) (by simp)⟩
  · intro i _ j m _ him
    rw [←Law.marginal_fst_map (M.tupleLaw z.1) (goodTarget w n k p θ G t z bad i j)]
    apply hinc
    · exact target_before_later w n k p θ G t z i m him _
    · exact Or.inl ⟨goodTarget_not_bad w n k p θ G t z bad i j,target_other w n k p θ G t z (m,true) i _⟩
  · intro i _ j m _ hmi
    rw [←Law.marginal_snd_map (M.tupleLaw z.1) (goodTarget w n k p θ G t z bad i j)]
    apply hinc
    · exact earlier_before_target w n k p θ G t z m i hmi _
    · exact Or.inr ⟨goodTarget_not_bad w n k p θ G t z bad i j,target_other w n k p θ G t z (m,false) i _⟩
  · intro i _ j
    rw [Law.map_bad_sum,←Law.marginal_fst_map]
    exact hbadA _ (goodTarget_not_bad w n k p θ G t z bad i j)
  · intro i _ j
    rw [Law.map_bad_sum,←Law.marginal_snd_map]
    exact hbadB _ (goodTarget_not_bad w n k p θ G t z bad i j)
end
end SharpLogRamsey.Selection.Windows

end

end OAI
