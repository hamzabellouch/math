import Mathlib
import OAI.Combinatorics.KMedian.Preparation.PreparationParameters
import OAI.Combinatorics.KMedian.Preparation.NearbyBall
import OAI.Combinatorics.KMedian.Process.PhysicalOldMass
import OAI.Combinatorics.KMedian.Preparation.SupportRepair

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem nearby_assignments (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B T₁ v p₀ : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT₁ : 0 ≤ T₁)
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ G.p t)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hD : dist j (s t) ≤ M*v) (hL : 0 < G.c t → G.L t ≤ T₁*v)
    (hR : G.c t=0 → ∀ a ∈ F t, dist (s t) (i a) ≤ T₁*v) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        nearFactor p₀ (M+(1+δ)*T₁) γ g*v := by
  classical
  have hv : 0 ≤ v := (sum_nonneg (fun a _ => mul_nonneg (hy a) dist_nonneg)).trans_eq hvj
  have hc1 : ∀ t, G.c t ≤ 1 := by
    intro t
    have hu := G.unit t
    have hpp := hp t
    linarith only [hu,hpp,hp₀]
  obtain ⟨hshort,hcost⟩ := physical_old_estimates hg hγ hunit L hy hp₀ hp₀1 hp
    G.nonneg hc1 G.disjoint Fj hmj (fun a => dist j (i a)) (fun _ => dist_nonneg)
  rw [hvj] at hcost
  let d : Physical I T → ℝ := Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2))
  let ball := univ.filter (fun a => d a ≤ (M+(1+δ)*T₁)*v)
  have hrad : 0 ≤ (M+(1+δ)*T₁)*v := by positivity
  obtain ⟨r,hr,hc⟩ := support_repaired_cost (L.ν.joint L.κ) ball
    (physicalOpen L) (oldAssignment L Fj) d hrad
    (fun z hz a => (old_feasible L hg Fj z hz a).1)
    (fun z hz a => (old_feasible L hg Fj z hz a).2)
    (fun a => by cases a <;> exact dist_nonneg)
    (fun a ha => (mem_filter.mp ha).2)
    (nearby_ball F y s i V G L hδ hT₁ hv hg j t hD hL hR)
    hcost hshort
  refine ⟨r,hr,hc.trans_eq ?_⟩
  dsimp only [nearFactor,shortfallFactor]
  ring

end MetricKMedian.Preparation
end
end

end OAI
