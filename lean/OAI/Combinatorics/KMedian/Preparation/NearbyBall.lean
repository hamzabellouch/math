import Mathlib
import OAI.Combinatorics.KMedian.Preparation.RepresentativeBundles
import OAI.Combinatorics.KMedian.Preparation.CoupledGeometry

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem nearby_ball (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B T₁ v : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hδ : 0 ≤ δ) (hT₁ : 0 ≤ T₁) (hv : 0 ≤ v) (hg : 0 ≤ g)
    (j : X) (t : T) (hD : dist j (s t) ≤ M*v)
    (hL : 0 < G.c t → G.L t ≤ T₁*v)
    (hR : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v)
    (z : L.Ω × (T → Finset I)) (hz : 0 < (L.ν.joint L.κ).weight z) :
    1 ≤ ∑ a ∈ univ.filter (fun a : Physical I T =>
      Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a ≤
        (M+(1+δ)*T₁)*v), physicalOpen L z a := by
  obtain ⟨hω,hξ⟩ := L.ν.support_joint L.κ z hz
  have hTv := mul_nonneg hT₁ hv
  by_cases hc : G.c t=0
  · have hrad : ∀ a ∈ G.P t, dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hh := hR hc a (G.sub t ha)
      have htri := dist_triangle j (s t) (i a)
      have hδT := mul_nonneg hδ hTv
      nlinarith only [hh,htri,hD,hδT]
    have hb := bundle_ball_mass L hg z hξ (fun a => dist j (i a))
      ((M+(1+δ)*T₁)*v) {t} (by simpa only [mem_singleton,forall_eq] using hrad)
    simpa only [sum_singleton,zero_deficit_total L t hc (G.unit t) z.1 hω] using hb
  · have hc' : 0 < G.c t := lt_of_le_of_ne (G.nonneg t) (Ne.symm hc)
    have hn : G.next t ≠ t := fun ht => hc (G.self_zero t ht)
    have hLn : G.L (G.next t) ≤ G.L t := by
      calc
        G.L (G.next t) ≤ dist (s (G.next t)) (s t) := G.closest _ _ hn
        _ = G.L t := (dist_comm _ _).trans (G.next_distance t).symm
    have hown : ∀ a ∈ G.P t, dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hh := (G.radius t hn a ha).trans (mul_le_mul_of_nonneg_left (hL hc') hδ)
      have htri := dist_triangle j (s t) (i a)
      nlinarith only [hh,htri,hD,hTv]
    have hother : ∀ a ∈ G.P (G.next t), dist j (i a) ≤ (M+(1+δ)*T₁)*v := by
      intro a ha
      have hn' : G.next (G.next t) ≠ G.next t := by
        intro ht
        exact hn (G.self_singleton (G.next t) ht t).symm
      have hr := G.radius (G.next t) hn' a ha
      have hr' := hr.trans (mul_le_mul_of_nonneg_left hLn hδ)
      have htri := dist_triangle j (s t) (i a)
      have htri' := dist_triangle (s t) (s (G.next t)) (i a)
      rw [← G.next_distance t] at htri'
      have hδL := mul_le_mul_of_nonneg_left (hL hc') hδ
      nlinarith only [hr',htri,htri',hD,hL hc',hδL]
    have hb := bundle_ball_mass L hg z hξ (fun a => dist j (i a))
      ((M+(1+δ)*T₁)*v) {t,G.next t} (by
        intro u hu
        rcases mem_insert.mp hu with rfl | hu
        · exact hown
        · rw [mem_singleton] at hu
          simpa only [hu] using hother)
    have hh := add_le_add (L.half z.1 t) (L.half z.1 (G.next t))
    have he : (∑ u ∈ ({t,G.next t} : Finset T), g*(L.K z.1 u:ℝ))=
        g*(L.K z.1 t:ℝ)+g*(L.K z.1 (G.next t):ℝ) := by simp [hn.symm]
    rw [he] at hb
    exact (by linarith only [hh] : (1:ℝ) ≤ _).trans hb

end MetricKMedian.Preparation
end
end

end OAI
