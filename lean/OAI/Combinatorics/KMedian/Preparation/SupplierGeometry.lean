import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeBundles
import OAI.Combinatorics.KMedian.Preparation.PreparationCostGeometry
import OAI.Combinatorics.KMedian.Preparation.SupplierMap
import OAI.Combinatorics.KMedian.Preparation.SupplierCharges

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem request_connection_radius (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ γ β : ℝ} (G : BundleGeometry F y s i V M δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 ≤ δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (j : X) (t : T) (hD : 0 < G.c t → dist j (s t) ≤ β*G.L t)
    (q : Star I T → ℝ) (htarget : ∀ e, t ∉ targets G.A e → q e=0)
    (hzero : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0) :
    ∀ e, 0 < q e → match supplier G.next e with
      | .inl a => dist j (i a) ≤ connectionCharge G.P G.A y (fun a => dist j (i a)) G.L
          (1+2*δ/(1-β-δ)) β δ e
      | .inr u => ∀ a ∈ G.P u, dist j (i a) ≤
          connectionCharge G.P G.A y (fun a => dist j (i a)) G.L (1+2*δ/(1-β-δ)) β δ e := by
  have hAP : ∀ t, Disjoint (G.A t) (G.P t) := fun t => by
    rw [G.missing t]
    exact sdiff_disjoint
  rintro (a | (ut | u)) he
  · exact le_rfl
  · obtain ⟨hut,hw⟩ := ordinary_positive G.P G.A y G.c γ q t ut.1 ut.2 hy htarget hzero he
    rcases ut with ⟨u,v⟩
    dsimp only at hut
    subst u
    dsimp only [supplier,connectionCharge]
    intro a ha
    have hvt : v ≠ t := by
      intro hv
      subst v
      rw [disjoint_iff_inter_eq_empty.mp (hAP t),sum_empty] at hw
      exact lt_irrefl _ hw
    have hct : 0 < G.c t := by
      rw [← G.deficit_mass t]
      exact hw.trans_le (sum_le_sum_of_subset_of_nonneg inter_subset_left (fun a _ _ => hy a))
    have hnv : G.next v ≠ v := fun hv => hvt ((G.self_singleton v hv t).symm)
    have hr : ∀ b ∈ G.A t ∩ G.P v, dist j (i a) ≤
        (1+2*δ/(1-β-δ))*dist j (i b) := by
      intro b hb
      apply bundle_relocation j (s t) (s v) (i b) (i a) hβ hδ hsep (hD hct)
      · exact G.closest t v hvt.symm
      · exact (G.closest v t hvt).trans_eq (dist_comm _ _)
      · exact G.radius v hnv b (mem_inter.mp hb).2
      · exact G.radius v hnv a ha
    have hs : (∑ b ∈ G.A t ∩ G.P v, y b)*dist j (i a) ≤
        (1+2*δ/(1-β-δ))*(∑ b ∈ G.A t ∩ G.P v, y b*dist j (i b)) := by
      rw [sum_mul,mul_sum]
      exact sum_le_sum (fun b hb => (mul_le_mul_of_nonneg_left (hr b hb) (hy b)).trans_eq (by ring))
    calc
      dist j (i a) ≤ ((1+2*δ/(1-β-δ))*(∑ b ∈ G.A t ∩ G.P v, y b*dist j (i b)))/
          (∑ b ∈ G.A t ∩ G.P v, y b) := (le_div_iff₀ hw).mpr (by nlinarith only [hs])
      _ = _ := by ring
  · have hut : u=t := by
      by_contra hn
      have hz := htarget (.inr (.inr u)) (by simpa only [targets,mem_singleton] using Ne.symm hn)
      rw [hz] at he
      exact lt_irrefl _ he
    subst u
    have hct : 0 < G.c t := by
      apply lt_of_le_of_ne (G.nonneg t)
      intro hz
      have heq := hzero (.inr (.inr t)) (by simp only [weight,← hz,mul_zero])
      rw [heq] at he
      exact lt_irrefl _ he
    have hn : G.next t ≠ t := fun ht => (ne_of_gt hct) (G.self_zero t ht)
    have hnn : G.next (G.next t) ≠ G.next t := fun ht => hn (G.self_singleton (G.next t) ht t).symm
    dsimp only [supplier,connectionCharge]
    intro a ha
    have hLn : G.L (G.next t) ≤ G.L t :=
      (G.closest (G.next t) t hn).trans_eq ((dist_comm _ _).trans (G.next_distance t).symm)
    have hr := (G.radius (G.next t) hnn a ha).trans (mul_le_mul_of_nonneg_left hLn hδ)
    have ht := dist_triangle j (s t) (i a)
    have ht' := dist_triangle (s t) (s (G.next t)) (i a)
    rw [← G.next_distance t] at ht'
    nlinarith only [ht,ht',hr,hD hct]

end MetricKMedian.Preparation
end
end

end OAI
