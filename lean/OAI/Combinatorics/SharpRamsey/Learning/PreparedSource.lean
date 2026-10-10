import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureSupport
import OAI.Combinatorics.SharpRamsey.Trees.GoodChronology

namespace OAI

section
namespace SharpLogRamsey.Selection.ExposureModel
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ ι β C : Type} [Fintype Ω] [Fintype Θ] [Fintype ι]
  [DecidableEq ι] [Fintype β] [Fintype C]
variable (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
  (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
  (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
  (z : (contextual n k p θ G e own t).FreshHistory)
  (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)

include hp hz

lemma prepared_marginal_source
    (i : (contextual n k p θ G e own t).Index z.1) (a : β)
    (ha : (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      G ω ((contextual n k p θ G e own t).origin z.1 i)=a := by
  obtain ⟨y,hy,he⟩:=((contextual n k p θ G e own t).tupleLaw z.1).map_support
    (fun y=>y i) a ha
  obtain ⟨ω,hω,hθ,hG⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  exact ⟨ω,hω,hθ,(hG i).trans he⟩

lemma prepared_marginal_domain (S : Θ→ι→Finset β)
    (hS : ∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i)
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,a∉S z.1.1 ((contextual n k p θ G e own t).origin z.1 i)→
      (((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a=0 := by
  intro a ha
  by_contra h
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a h
  have hh:=hS ω hω ((contextual n k p θ G e own t).origin z.1 i)
  rw [hθ,hG] at hh
  exact ha hh

lemma prepared_marginal_property (P : Θ→ι→β→Prop)
    (hP : ∀ ω,p.mass ω≠0→∀ i,P (θ ω) i (G ω i))
    (i : (contextual n k p θ G e own t).Index z.1) :
    ∀ a,(((contextual n k p θ G e own t).tupleLaw z.1).marginal i).mass a≠0→
      P z.1.1 ((contextual n k p θ G e own t).origin z.1 i) a := by
  intro a ha
  obtain ⟨ω,hω,hθ,hG⟩:=prepared_marginal_source n k p θ G e own t hp z hz i a ha
  simpa only [hθ,hG] using hP ω hω ((contextual n k p θ G e own t).origin z.1 i)

lemma prepared_pair_property (P : Θ→ι→ι→β→β→Prop)
    (hP : ∀ ω,p.mass ω≠0→∀ i j,P (θ ω) i j (G ω i) (G ω j))
    (i j : (contextual n k p θ G e own t).Index z.1) :
    ∀ y,((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0→
      P z.1.1 ((contextual n k p θ G e own t).origin z.1 i)
        ((contextual n k p θ G e own t).origin z.1 j) (y i) (y j) := by
  intro y hy
  obtain ⟨ω,hω,hθ,hG⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  simpa only [hθ,hG i,hG j] using hP ω hω ((contextual n k p θ G e own t).origin z.1 i)
    ((contextual n k p θ G e own t).origin z.1 j)

end
end SharpLogRamsey.Selection.ExposureModel

end

end OAI
