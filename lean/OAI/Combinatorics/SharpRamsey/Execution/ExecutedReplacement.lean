import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.NullFreeLaw
import OAI.Combinatorics.SharpRamsey.Execution.VariableExtraction
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalDomains

namespace OAI

section
namespace SharpLogRamsey.Selection
variable {Ω : Type*} [Fintype Ω]
def Law.ofPublic (p : PublicTables.Law Ω) : Law Ω := ⟨p.mass,p.nonneg,p.total⟩
end SharpLogRamsey.Selection

namespace SharpLogRamsey.ActualPivot
open Finset Real TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I Ω Ξ : Type*} [Fintype I] [Fintype Ω]
  {n : ℕ} {b τ P H : ℝ}
local instance flat_ActualExecutedReplacement_1 : DecidableEq I := Classical.decEq _
local instance replacementBanksFintype : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

abbrev Flag := Projectivization K (Module.Dual K V)×Projectivization K V

variable (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
  (hτ : 0≤τ) (hτsmall : τ≤1/40000)

include hb hH hP haP

theorem Book.actual_replacement (μ : Selection.Law Ω)
    (s : Ω→I→Original (K:=K) (V:=V) n b)
    (targets : Ω→I→List (Flag (K:=K) (V:=V))) (t : Ω→BinaryTree I)
    (U : ChronoDomains (K:=K) (V:=V)) (N W ht m : ℕ) (hN : 0<N)
    (hsize : ∀ ω,(population (targets ω) (t ω)).length≤N)
    (hnodes : ∀ ω,(t ω).numNodes≤W) (hheight : ∀ ω,(t ω).height≤ht)
    (hcounts : ∀ ω i,(targets ω i).length≤ m)
    (Q : Flag (K:=K) (V:=V)→Flag (K:=K) (V:=V)→Prop)
    (hcons : ∀ ω,μ.mass ω≠0→(population (targets ω) (t ω)).Pairwise Q)
    (stream : Ω→Ξ) (base : Ξ→ℝ) (L : ℝ) (hb0 : ∀ x,0≤base x) (hL : 0≤L)
    (hdom : ∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),μ.mass ω)≤L*base x)
    (hmean : (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      ∑ ω,μ.mass ω*((N:ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall (s ω i))
        (fun _=>chronoRead b) (targets ω) z (t ω) U).length))≤(N:ℝ)/4) :
    ∃ z : I→Banks (K:=K) (V:=V) b,
      let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
      let choose:=fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)
      let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
      let E:=fun ω=>(N:ℝ)/2≤(fullOutput R (choose ω) read (targets ω) z (t ω) U).length
      ∃ hE : 0<PublicTables.acceptProb μ.asPublic E,
        let ν:=Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic E hE)
        let M:=fun ω=>fullMessage R (choose ω) read (targets ω) z (t ω) U
        let S:=univ.image M
        let msg : Ω→S:=fun ω=>⟨M ω,mem_image.mpr ⟨ω,mem_univ _,rfl⟩⟩
        let domains:=fun c : S=>(decode R (fixedRead read z) c.val U).take (N/2)
        (1/2:ℝ)≤PublicTables.acceptProb μ.asPublic E ∧
        (∀ x,(∑ ω∈univ.filter (fun ω=>stream ω=x),ν.mass ω)≤(2*L)*base x) ∧
        (∀ ω,ν.mass ω≠0→
          let out:=(fullOutput R (choose ω) read (targets ω) z (t ω) U).take (N/2)
          out.length=N/2 ∧ out.Sublist (population (targets ω) (t ω)) ∧
          out.Pairwise Q ∧ List.Forall₂ (fun x D=>x∈D) out (domains (msg ω))) ∧
        (∀ c D,D∈domains c→(D.card:ℝ)≤8000000*(Nat.card K:ℝ)^(n+2)*exp b) ∧
        Selection.entropy (ν.map msg)≤((2*W+1:ℕ):ℝ)*log 2+
          (W:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
          (2*(H+22)*(Nat.card K:ℝ)*P)*
          ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(n+3)) U+(W:ℝ)*(b+log 4+2*log 2000))+(W:ℝ)*P) := by
  let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
  let choose:=fun ω i=>book.chronoChoose hdim hτ hτsmall (s ω i)
  let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
  obtain ⟨z,hE,hprob,hextract⟩:=fixed_extraction_le μ.asPublic
    (fun _ : I=>banksLaw (K:=K) (V:=V) b) R choose read targets t U N hN hsize Q hcons hmean
  refine ⟨z,hE,hprob,?_,hextract,?_,?_⟩
  · have hh:=PublicTables.conditionSuccess_fiber μ.asPublic _ hE stream base L (1/2)
      (by norm_num) hprob hb0 hL hdom
    simpa only [Selection.Law.ofPublic, R, choose, read, div_div,div_one,one_div,div_inv_eq_mul,mul_comm] using hh
  · intro c D hD
    obtain ⟨ω,_,he⟩:=mem_image.mp c.property
    have hm : D∈decode R (fixedRead read z) (fullMessage R (choose ω) read (targets ω) z (t ω) U) U := by
      change D∈(decode R (fixedRead read z) c.val U).take (N/2) at hD
      rw [←he] at hD
      exact List.mem_of_mem_take hD
    exact book.actual_decoded_size hdim hb hτ hτsmall (s ω) z (targets ω)
      (fun i=>(targets ω i).length) (t ω) U D hm
  · have hh:=book.actual_full_entropy hb hH hP haP hdim hτ hτsmall
      (Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic _ hE)) s z t U
      W ht m targets (fun ω i=>(targets ω i).length) hcounts hnodes hheight
    simp only [Selection.entropy_map] at hh ⊢
    simpa only [R, choose, read, Selection.Law.map,
      Subtype.mk.injEq, fullMessage, fullMessage_eq_codeTree] using hh

end
end SharpLogRamsey.ActualPivot

end

end OAI
