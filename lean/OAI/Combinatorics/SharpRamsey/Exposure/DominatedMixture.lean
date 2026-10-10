import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.GoodRows
import OAI.Combinatorics.SharpRamsey.Exposure.DominatedCoupling

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Z B : Type} [Fintype Z] [Fintype B]

lemma Law.event_nonzero_filter (μ : Law Z) (H : Finset Z) :
    μ.event (H.filter (fun z=>μ.mass z≠0))=μ.event H := by
  unfold Law.event
  rw [sum_filter]
  apply sum_congr rfl
  intro z hz
  split_ifs with h
  · rfl
  · exact (not_not.mp h).symm

lemma Law.dominated_observable {X Y : Type} [Fintype X] [Fintype Y]
    (p : Law X) (q : Law Y) (f : X→Y) (c : ℝ)
    (h : ∀ y,(p.map f).mass y≤c*q.mass y) (g : Y→ℝ) (hg : ∀ y,0≤g y) :
    (∑ x,p.mass x*g (f x))≤c*∑ y,q.mass y*g y := by
  rw [←p.sum_map f g,mul_sum]
  apply sum_le_sum
  intro y _
  exact (mul_le_mul_of_nonneg_right (h y) (hg y)).trans_eq (mul_assoc _ _ _)

omit [Fintype B] in

theorem Law.dominated_history_mixture (μ : Law Z) (H : Finset Z)
    (hH : (1:ℝ)/2≤μ.event H) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (X : H→Type) [∀ z,Fintype (X z)] (ν : ∀ z,Law (X z))
    (f : ∀ z,X z→Q z.val) (c : ℝ) (hc : 0≤c)
    (hd : ∀ z y,((ν z).map (f z)).mass y≤c*(q z.val).mass y)
    (restore : ∀ z,Q z→B) (φ : B→ℝ) (hφ : ∀ b,0≤φ b) :
    (∑ x,((μ.onEvent H (by linarith)).sigma ν).mass x*
      φ (restore x.1.val (f x.1 x.2)))≤(2*c)*
        ∑ y,(μ.sigma q).mass y*φ (restore y.1 y.2) := by
  rw [Law.sigma_sum,Law.sigma_sum]
  calc
    _ ≤ ∑ z : H,(μ.onEvent H (by linarith)).mass z*
        (c*∑ y,(q z.val).mass y*φ (restore z.val y)) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ ((μ.onEvent H (by linarith)).nonneg z)
      exact (ν z).dominated_observable (q z.val) (f z) c (hd z)
        (fun y=>φ (restore z.val y)) (fun y=>hφ _)
    _ = c*∑ z : H,(μ.onEvent H (by linarith)).mass z*
        (∑ y,(q z.val).mass y*φ (restore z.val y)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring
    _ ≤ c*(2*∑ z,μ.mass z*∑ y,(q z).mass y*φ (restore z y)) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact μ.onEvent_mean_le_two H hH (fun z=>∑ y,(q z).mass y*φ (restore z y))
        (fun z=>sum_nonneg (fun y _=>mul_nonneg ((q z).nonneg y) (hφ _)))
    _ = _ := by ring

lemma Law.dominated_history_map (μ : Law Z) (H : Finset Z)
    (hH : (1:ℝ)/2≤μ.event H) (Q : Z→Type) [∀ z,Fintype (Q z)] (q : ∀ z,Law (Q z))
    (X : H→Type) [∀ z,Fintype (X z)] (ν : ∀ z,Law (X z))
    (f : ∀ z,X z→Q z.val) (c : ℝ) (hc : 0≤c)
    (hd : ∀ z y,((ν z).map (f z)).mass y≤c*(q z.val).mass y)
    (restore : ∀ z,Q z→B) (b : B) :
    (((μ.onEvent H (by linarith)).sigma ν).map
      (fun x=>restore x.1.val (f x.1 x.2))).mass b≤
        (2*c)*((μ.sigma q).map (fun y=>restore y.1 y.2)).mass b := by
  have hh:=μ.dominated_history_mixture H hH Q q X ν f c hc hd restore
    (fun y=>if y=b then 1 else 0) (by intro y; positivity)
  simpa only [Law.map,sum_filter,mul_ite,mul_one,mul_zero] using hh
end
end SharpLogRamsey.Selection

end

end OAI
