import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.SourceCoupling
import OAI.Combinatorics.SharpRamsey.Selection.FreshRepresentatives

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

lemma Law.common_source_support (q : Law X) (p : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=p.map g) (x : X) (hx : q.mass x≠0) :
    ∃ ω,p.mass ω≠0 ∧ g ω=f x := by
  have hf : (p.map g).mass (f x)≠0 := by
    rw [←h]
    exact ne_of_gt ((lt_of_le_of_ne (q.nonneg x) (Ne.symm hx)).trans_le (q.le_map f x))
  exact p.map_support g (f x) hf

namespace ExposureModel
variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]

omit [Fintype Θ] [Fintype ι] [DecidableEq ι] in
lemma afterDraw_tagged (M : ExposureModel ι β C) (hp : ∀ z,0<M.remaining z)
    (tag : M.History→Θ) (φ : Θ×(ι→β)→ℝ) :
    (∑ x,(M.afterDraw hp).joint.mass x*φ (tag x.1.1,(M.afterDraw hp).restore x.1 x.2))=
      ∑ x,M.joint.mass x*φ (tag x.1,M.restore x.1 x.2) := by
  rw [joint,Law.sigma_sum,joint,Law.sigma_sum]
  exact M.freshLaw_old hp (fun z=>∑ y,(M.tupleLaw z).mass y*φ (tag z,M.restore z y))

theorem contextual_afterDraw_tagged_map (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z) :
    ((contextual n k p θ G e own t).afterDraw hp).joint.map
      (fun x=>(x.1.1.1,((contextual n k p θ G e own t).afterDraw hp).restore x.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  ext y
  have he:=afterDraw_tagged (contextual n k p θ G e own t) hp (fun z=>z.1)
    (fun x=>if x=y then 1 else 0)
  have he' := he.trans (contextual_tagged n k p θ G e own t (fun x=>if x=y then 1 else 0))
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using he'

theorem contextual_fresh_source (n k : ℕ) {Ω : Type} [Fintype Ω]
    (p : Law Ω) (θ : Ω→Θ) (G : Ω→ι→β)
    (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (hp : ∀ z,0<(contextual n k p θ G e own t).remaining z)
    (z : (contextual n k p θ G e own t).FreshHistory)
    (hz : ((contextual n k p θ G e own t).freshLaw hp).mass z≠0)
    (y : (contextual n k p θ G e own t).Index z.1→β)
    (hy : ((contextual n k p θ G e own t).tupleLaw z.1).mass y≠0) :
    ∃ ω,p.mass ω≠0 ∧ θ ω=z.1.1 ∧
      ∀ i,G ω ((contextual n k p θ G e own t).origin z.1 i)=y i := by
  let M:=contextual n k p θ G e own t
  obtain ⟨ω,hω,he⟩:=Law.common_source_support (M.afterDraw hp).joint p
    (fun x=>(x.1.1.1,(M.afterDraw hp).restore x.1 x.2)) (fun ω=>(θ ω,G ω))
    (contextual_afterDraw_tagged_map n k p θ G e own t hp) ⟨z,y⟩ (mul_ne_zero hz hy)
  refine ⟨ω,hω,congrArg Prod.fst he,fun i=>?_⟩
  have hh:=congrFun (congrArg Prod.snd he) (M.origin z.1 i)
  exact hh.trans (M.restore_origin z.1 y i)

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
