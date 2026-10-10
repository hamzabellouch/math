import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.SourceCoupling

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B : Type*} [Fintype X] [Fintype Ω] [Fintype B]

theorem Law.attach_source_le (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b≤c*(μ.map g).mass b)
    (φ : Ω→ℝ) (hφ : ∀ ω,0≤φ ω) :
    (∑ x,(q.attach μ f g).mass x*φ x.2)≤c*∑ ω,μ.mass ω*φ ω := by
  rw [Law.attach,Law.sigma_sum]
  change (∑ x,q.mass x*(fun b=>∑ ω,(μ.cond g b).mass ω*φ ω) (f x))≤_
  rw [←q.sum_map f (fun b=>∑ ω,(μ.cond g b).mass ω*φ ω)]
  calc
    _ ≤ ∑ b,c*(μ.map g).mass b*∑ ω,(μ.cond g b).mass ω*φ ω := by
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_right (h b)
        (sum_nonneg (fun ω _=>mul_nonneg ((μ.cond g b).nonneg ω) (hφ ω)))
    _ = c*∑ ω,μ.mass ω*φ ω := by
      simp_rw [mul_assoc]
      rw [←mul_sum,μ.history_sum]

lemma Law.attach_support_of_dominated (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b≤c*(μ.map g).mass b)
    (x : Σ _x : X,Ω) (hx : (q.attach μ f g).mass x≠0) :
    q.mass x.1≠0 ∧ μ.mass x.2≠0 ∧ g x.2=f x.1 := by
  have hx' : q.mass x.1≠0 ∧ (μ.cond g (f x.1)).mass x.2≠0 := mul_ne_zero_iff.mp hx
  have hf : (μ.map g).mass (f x.1)≠0 := by
    intro he
    have hh:=h (f x.1)
    rw [he,mul_zero] at hh
    have hp : 0<q.mass x.1 := lt_of_le_of_ne (q.nonneg x.1) (Ne.symm hx'.1)
    exact (not_lt_of_ge hh) (hp.trans_le (q.le_map f x.1))
  exact ⟨hx'.1,μ.cond_support g (f x.1) hf x.2 hx'.2⟩

lemma Law.attach_map_source_le (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B)
    (c : ℝ) (h : ∀ b,(q.map f).mass b≤c*(μ.map g).mass b) (ω : Ω) :
    ((q.attach μ f g).map (fun x=>x.2)).mass ω≤c*μ.mass ω := by
  have hh:=q.attach_source_le μ f g c h (fun x=>if x=ω then 1 else 0) (by intro x; positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,ite_true] using hh
end
end SharpLogRamsey.Selection

end

end OAI
