import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalMarginals
import OAI.Combinatorics.SharpRamsey.Learning.PreparedIncidence

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section
variable {Ω : Type*} [Fintype Ω]
lemma Law.exists_mass_ne_zero (p : Law Ω) : ∃ ω,p.mass ω≠0 := by
  by_contra h
  push Not at h
  have hh:=p.total
  simp only [h,sum_const_zero] at hh
  norm_num at hh

namespace ExposureModel
variable {Ω Θ ι C β : Type} [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι]
  [Fintype C] [Fintype β]
lemma prepared_context_property (n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (P : Θ→Prop) (hP : ∀ ω,p.mass ω≠0→P (θ ω)) : P z.1.1 := by
  obtain ⟨y,hy⟩:=((contextual n k p θ G e own t).tupleLaw z.1).exists_mass_ne_zero
  obtain ⟨ω,hω,hθ,_⟩:=contextual_fresh_source n k p θ G e own t hp z hz y hy
  simpa only [hθ] using hP ω hω
end ExposureModel

open ExposureModel

theorem eventually_prepared_reciprocal (d : ℕ) (β : ℝ) (hβ : 0<β) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (Projectivization K V)]
      [Fintype (Projectivization K (Module.Dual K V))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ (Ω Θ ι C : Type) [Fintype Ω] [Fintype Θ] [Fintype ι] [DecidableEq ι] [Fintype C]
        (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→ι→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→ι→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→ι→ℝ) (n k : ℕ) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C)
        (t : Fin k) (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
        (D J a : ℝ),
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        σ^β≤D → ((d+2:ℕ):ℝ)*σ≤J →
        ∀ (z : (contextual n k p θ G e own t).FreshHistory)
          (c : (contextual n k p θ G e own t).Index z.1→
            (contextual n k p θ G e own t).Index z.1→NNReal),
          ((contextual n k p θ G e own t).freshLaw hp).mass z≠0 →
          ∀ i,i∉badIndices ((contextual n k p θ G e own t).tupleLaw z.1)
            ((contextual n k p θ G e own t).embedding z.1)
            ((contextual n k p θ G e own t).owner z.1) c J (D*σ^β) a z.2 →
          let q:=((contextual n k p θ G e own t).tupleLaw z.1).marginal i
          let ui:=u z.1.1 ((contextual n k p θ G e own t).origin z.1 i)
          let MA:=1024*exp (((d+3:ℕ):ℝ)*σ-ui)
          let MB:=1024*exp ui
          let L:=((d+2:ℕ):ℝ)*σ
          let κ:=D*σ^(3*β)
          Nonempty (AuxiliarySupport q.fst (univ.filter (goodFirst q MA L κ (1/50))) MA κ) ∧
          Nonempty (AuxiliarySupport q.snd (univ.filter (goodSecond q MB L κ (1/50))) MB κ) ∧
          q.fst.event (univ.filter (fun x=>¬goodFirst q MA L κ (1/50) x))≤3251*σ^(-2*β) ∧
          q.snd.event (univ.filter (fun x=>¬goodSecond q MB L κ (1/50) x))≤3251*σ^(-2*β) := by
  filter_upwards [eventually_actual_reciprocal d β hβ] with σ he
  intro K V _ _ _ _ _ _ _ hdim hlog Ω Θ ι C _ _ _ _ _ p θ G S u n k e own t hp D J a
    hS hf hcap hD hJ z c hz i hi
  let M:=contextual n k p θ G e own t
  have hd:=((not_badIndices (M.tupleLaw z.1) (M.embedding z.1) (M.owner z.1)
    c J (D*σ^β) a z.2 i).mp hi).1
  have hcaps:=prepared_context_property n k p θ G e own t hp z hz
    (fun θ=>∀ i,(((S θ i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u θ i) ∧
      (((S θ i).image Prod.snd).card:ℝ)≤1024*exp (u θ i) ∧
      ((S θ i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) hcap
  apply he K V hdim hlog (M.tupleLaw z.1|>.marginal i) (S z.1.1 (M.origin z.1 i)) D
    (u z.1.1 (M.origin z.1 i))
  · exact prepared_marginal_domain n k p θ G e own t hp z hz S hS i
  · intro x hx
    exact prepared_marginal_property n k p θ G e own t hp z hz
      (fun _ _ x=>x.1.rep x.2.rep=0) hf i x (ne_of_gt hx)
  · exact (hcaps _).1
  · exact (hcaps _).2.1
  · exact (hcaps _).2.2
  · exact hD
  · exact (sub_le_sub_right hJ _).trans hd
end
end SharpLogRamsey.Selection

end

end OAI
