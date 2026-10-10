import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ContextOutput

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Selection TreeDecoder FreshExecution BinaryTree ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) ]
  {I X Ω : Type} [Fintype I] [Fintype X] [Fintype Ω]
  {d ℓ : ℕ} {b τ P H : ℝ}
local instance outEqI : DecidableEq I := Classical.decEq _
local instance outBanks : Fintype (Banks (K:=K) (V:=V) b) := inferInstance

def reciprocalOutputCost (W ht m : ℕ) : ℝ :=
  ((2*W+1:ℕ):ℝ)*log 2+
    (W:ℝ)*(log ((Fintype.card I:ℝ)+1)+headerCost (K:=K) (V:=V)+log (m+1:ℕ))+
    (2*(H+22)*(Nat.card K:ℝ)*P)*
      ((ht:ℝ)*(potential ((Nat.card K:ℝ)^(d+3)) ((univ,univ) : ChronoDomains (K:=K) (V:=V))+(W:ℝ)*(b+log 4+2*log 2000))+(W:ℝ)*P)

theorem Book.context_output (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
    (hτ : 0≤τ) (hτsmall : τ≤1/40000)
    (p : Law Ω) (G : Ω→Fin ℓ→Flag (K:=K) (V:=V)) (μ : Law X) (source : X→Ω)
    (hmarginal : μ.map source=p)
    (s : X→I→Original (K:=K) (V:=V) d b)
    (targets : X→I→List (Flag (K:=K) (V:=V))) (t : X→BinaryTree I)
    (N W ht m : ℕ) (hN : 0<N)
    (hsize : ∀ x,(population (targets x) (t x)).length≤N)
    (hnodes : ∀ x,(t x).numNodes≤W) (hheight : ∀ x,(t x).height≤ht)
    (hcounts : ∀ x i,(targets x i).length≤ m)
    (hsub : ∀ x,μ.mass x≠0→(population (targets x) (t x)).Sublist (List.ofFn (G (source x))))
    (hmean : (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
      ∑ x,μ.mass x*((N:ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall (s x i))
        (fun _=>chronoRead b) (targets x) z (t x) (univ,univ)).length))≤(N:ℝ)/4) :
    Nonempty (ContextOutput p G (N/2) (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
      (reciprocalOutputCost (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) (P:=P) (H:=H) W ht m) 2) := by
  obtain ⟨z,hE,hprob,hdom,hextract,hdomains,hcost⟩:=book.actual_replacement hdim hb hH hP haP hτ hτsmall
    μ s targets t (univ,univ) N W ht m hN hsize hnodes hheight hcounts
    (fun _ _=>True) (by intro x hx;exact List.pairwise_of_forall (fun _ _=>trivial))
    source p.mass 1 p.nonneg (by norm_num)
    (by intro a;change (μ.map source).mass a≤1*p.mass a;rw [hmarginal,one_mul]) hmean
  let R:=fun (y : Projectivization K (Module.Dual K V)) (x : Projectivization K V)=>SharpLogRamsey.Incidence.Incident x y
  let choose:=fun x i=>book.chronoChoose hdim hτ hτsmall (s x i)
  let read:=fun _ : I=>chronoRead (K:=K) (V:=V) b
  let E:=fun x=>(N:ℝ)/2≤(fullOutput R (choose x) read (targets x) z (t x) (univ,univ)).length
  let ν:=Selection.Law.ofPublic (PublicTables.conditionSuccess μ.asPublic E hE)
  let M:=fun x=>fullMessage R (choose x) read (targets x) z (t x) (univ,univ)
  let S:=univ.image M
  let msg : X→S:=fun x=>⟨M x,mem_image.mpr ⟨x,mem_univ _,rfl⟩⟩
  let DD:=fun c : S=>(decode R (fixedRead read z) c.val (univ,univ)).take (N/2)
  let out:=fun x=>(fullOutput R (choose x) read (targets x) z (t x) (univ,univ)).take (N/2)
  apply contextOutput_of_lists p G ν source msg out DD (by positivity)
  · intro x hx
    exact (hextract x hx).1
  · intro x hx
    have hμ : μ.mass x≠0:=(PublicTables.conditionSuccess_support μ.asPublic E hE x hx).1
    exact (hextract x hx).2.1.trans (hsub x hμ)
  · intro x hx
    exact (hextract x hx).2.2.2
  · exact hdomains
  · intro a
    have hh:=hdom a
    simpa only [mul_one,Law.map] using hh
  · exact hcost
end
end SharpLogRamsey.ActualPivot

end

end OAI
