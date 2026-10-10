import Mathlib
import OAI.Combinatorics.KMedian.Preparation.SupplierGeometry
import OAI.Combinatorics.KMedian.Preparation.PreparationAssignments
import OAI.Combinatorics.KMedian.Preparation.CoupledGeometry
import OAI.Combinatorics.KMedian.Preparation.NearestAssignmentGeometry
import OAI.Combinatorics.KMedian.Preparation.PreparationParameters

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem distant_assignments (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B v p₀ α β : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 < δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp : ∀ t, p₀ ≤ G.p t) (hα : 0 ≤ α) (hα1 : α < 1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hV : V t ≤ v) (R : ℝ) (hDα : dist j (s t) ≤ α*R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R)
    (hmin : ∀ a ∉ F t, R ≤ dist (s t) (i a))
    (hDβ : 0 < G.c t → dist j (s t) ≤ β*G.L t) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        farFactor δ p₀ α β γ*v := by
  classical
  let d := fun a => dist j (i a)
  let κ := 1+2*δ/(1-β-δ)
  let charge := connectionCharge G.P G.A y d G.L κ β δ
  have hκ : 1 ≤ κ := le_add_of_nonneg_right (div_nonneg (by positivity) (by linarith only [hsep]))
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hAP : ∀ u, Disjoint (G.A u) (G.P u) := fun u => by
    rw [G.missing u]
    exact sdiff_disjoint
  have hrad : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
      ∀ e, 0 < L.R ω t e → match supplier G.next e with
        | .inl a => d a ≤ charge e
        | .inr u => ∀ a, 0 < L.C ω ξ (u,a) → d a ≤ charge e := by
    intro ω hω ξ hξ e he
    let q : Star I T → ℝ := fun e => (L.R ω t e:ℝ)
    have ht : ∀ e, t ∉ targets G.A e → q e=0 := by
      intro e ht
      simp only [q,L.request_target ω t e ht,Nat.cast_zero]
    have hz : ∀ e, weight y G.P G.A G.c γ e=0 → q e=0 := by
      intro e hz
      have hh := L.request_cap ω hω t e
      rw [L.open_zero ω hω e hz] at hh
      simp only [q,Nat.eq_zero_of_le_zero hh,Nat.cast_zero]
    have hr := request_connection_radius F y s i V G hy hδ.le hβ hsep j t hDβ q ht hz e (show 0 < (L.R ω t e:ℝ) by exact_mod_cast he)
    cases hs : supplier G.next e with
    | inl a => simpa only [hs] using hr
    | inr u =>
      simp only [hs] at hr
      intro a ha
      apply hr a
      by_contra hn
      rw [(L.pieces ω ξ hξ u).2.2 a hn] at ha
      exact Nat.lt_irrefl _ ha
  obtain ⟨r,hr,hc⟩ := supplier_assignments G.P G.A y G.p G.c hg hunit L G.next G.self_zero
    hAP t d charge hy (fun _ => dist_nonneg) (hp₀.trans_le (hp t))
    (connectionCharge_nonneg G.P G.A y d G.L hy (fun _ => dist_nonneg)
      (fun t => by rw [G.next_distance t]; exact dist_nonneg) hκ0 hβ hδ.le) hrad
  refine ⟨r,?_,hc.trans ?_⟩
  · intro z hz
    refine ⟨?_, (hr z hz).2⟩
    intro a
    cases a <;> exact (hr z hz).1 _
  apply (old_charge_bound (F t) G.P G.A y d G.p G.c G.L hy (fun _ => dist_nonneg)
    G.disjoint t (G.sub t) (G.missing t) hp₀ (hp t) hκ).trans
  have hex := metric_exchange Fj (F t) y i j (s t) hy hmj hms hα hα1 hDα hmax hmin
  rw [hvj] at hex
  have hbase := mul_le_mul_of_nonneg_left hex
    (show 0 ≤ max (1/p₀) κ from le_trans hκ0 (le_max_right _ _))
  have hext := (extra_star_charge hβ hδ hγ (G.charge t)).trans
    (mul_le_mul_of_nonneg_left hV (show 0 ≤ (β+1+δ)*γ/δ by positivity))
  exact (add_le_add hbase hext).trans_eq (by dsimp only [farFactor,κ]; ring)

end MetricKMedian.Preparation
end
end

end OAI
