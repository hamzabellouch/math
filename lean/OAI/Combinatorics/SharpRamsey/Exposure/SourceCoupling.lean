import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.ExposureMixture

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

def Law.attach (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B) : Law (Σ _x : X,Ω) :=
  q.sigma (fun x=>μ.cond g (f x))

theorem Law.attach_source (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=μ.map g) (φ : Ω→ℝ) :
    (∑ x,(q.attach μ f g).mass x*φ x.2)=∑ ω,μ.mass ω*φ ω := by
  rw [Law.attach,Law.sigma_sum]
  change (∑ x,q.mass x*(fun b=>∑ ω,(μ.cond g b).mass ω*φ ω) (f x))=_
  rw [←q.sum_map f (fun b=>∑ ω,(μ.cond g b).mass ω*φ ω),h]
  exact μ.history_sum g φ

lemma Law.attach_support (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (h : q.map f=μ.map g) (x : Σ _x : X,Ω)
    (hx : (q.attach μ f g).mass x≠0) :
    q.mass x.1≠0 ∧ μ.mass x.2≠0 ∧ g x.2=f x.1 := by
  have hx' : q.mass x.1≠0 ∧ (μ.cond g (f x.1)).mass x.2≠0 := mul_ne_zero_iff.mp hx
  have hf : (μ.map g).mass (f x.1)≠0 := by
    rw [←h]
    exact ne_of_gt ((lt_of_le_of_ne (q.nonneg x.1) (Ne.symm hx'.1)).trans_le (q.le_map f x.1))
  exact ⟨hx'.1,μ.cond_support g (f x.1) hf x.2 hx'.2⟩

variable {β C ι Θ : Type} [Fintype β] [Fintype C] [Fintype ι]
  [DecidableEq ι] [Fintype Θ]
namespace ExposureModel

theorem contextual_tagged (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k)
    (φ : Θ×(ι→β)→ℝ) :
    (∑ x,(contextual n k p θ G e own t).joint.mass x*
      φ (x.1.1,(contextual n k p θ G e own t).restore x.1 x.2))=
      ∑ ω,p.mass ω*φ (θ ω,G ω) := by
  rw [joint,Law.sigma_sum]
  change (∑ h,((p.map θ).sigma (fun z=>(atRound n k ((p.cond θ z).map G)
    (e z) (own z) t).historyLaw)).mass h*
      ∑ x,((atRound n k ((p.cond θ h.1).map G) (e h.1) (own h.1) t).tupleLaw h.2).mass x*
        φ (h.1,(atRound n k ((p.cond θ h.1).map G) (e h.1) (own h.1) t).restore h.2 x))=_
  rw [Law.sigma_sum]
  change (∑ z,(p.map θ).mass z*(atRound n k ((p.cond θ z).map G)
    (e z) (own z) t).expectation (fun x=>φ (z,x)))=_
  simp_rw [atRound_preserves]
  exact (p.history_observable_sum θ G (fun z x=>φ (z,x))).symm

theorem contextual_tagged_map (n k : ℕ) {Ω : Type} [Fintype Ω] (p : Law Ω) (θ : Ω→Θ)
    (G : Ω→ι→β) (e : Θ→C×Fin (n+k)↪ι) (own : Θ→ι→Option C) (t : Fin k) :
    (contextual n k p θ G e own t).joint.map
      (fun x=>(x.1.1,(contextual n k p θ G e own t).restore x.1 x.2))=
        p.map (fun ω=>(θ ω,G ω)) := by
  ext y
  have he:=contextual_tagged n k p θ G e own t (fun x=>if x=y then 1 else 0)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using he

end ExposureModel
end
end SharpLogRamsey.Selection

end

end OAI
