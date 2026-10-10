import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

def reaction (k t : ℝ) : ℝ := 4*Real.pi*k*(max t 0)^(3/2:ℝ)

lemma reaction_nonneg {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : 0 ≤ reaction k t := by
  unfold reaction
  positivity

lemma reaction_monotone {k : ℝ} (hk : 0 ≤ k) : Monotone (reaction k) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) (by norm_num))
    (by positivity)

lemma reaction_continuous (k : ℝ) : Continuous (reaction k) := by
  apply continuous_const.mul
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

lemma reaction_convex {k : ℝ} (hk : 0 ≤ k) : ConvexOn ℝ univ (reaction k) := by
  have hm : ConvexOn ℝ (univ : Set ℝ) (fun t : ℝ => max t 0) :=
    (convexOn_id convex_univ).sup (convexOn_const 0 convex_univ)
  have him : (fun t : ℝ => max t 0) '' univ = Ici 0 := by
    ext t
    constructor
    · rintro ⟨s,_,rfl⟩
      exact le_max_right (s : ℝ) 0
    · intro ht
      exact ⟨t,mem_univ _,max_eq_left ht⟩
  have hp : ConvexOn ℝ ((fun t : ℝ => max t 0) '' univ)
      (fun t : ℝ => t^(3/2:ℝ)) := by
    rw [him]
    exact convexOn_rpow (by norm_num)
  have hmono : MonotoneOn (fun t : ℝ => t^(3/2:ℝ))
      ((fun t : ℝ => max t 0) '' univ) := by
    rw [him]
    intro s hs t _ hst
    exact Real.rpow_le_rpow hs hst (by norm_num)
  exact (hp.comp hm hmono).smul (by positivity : 0 ≤ 4*Real.pi*k)

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [IsProbabilityMeasure P] (hm : m ≤ mΩ)
include hm

theorem reaction_condExp {k : ℝ} (hk : 0 ≤ k) {u : Ω → ℝ}
    (hu : Integrable u P) (hfu : Integrable (reaction k ∘ u) P) :
    ∀ᵐ sample ∂P, reaction k (P[u | m] sample) ≤ P[reaction k ∘ u | m] sample := by
  exact (reaction_convex hk).map_condExp_le_univ hm (reaction_continuous k).lowerSemicontinuous hu hfu

theorem offset_condExp {u : Ω → ℝ} (hu : Integrable u P) (V : ℝ) :
    (fun sample => V + P[fun sample => u sample - V | m] sample) =ᵐ[P] P[u | m] := by
  have he := condExp_sub hu (integrable_const V) m
  rw [condExp_const hm] at he
  filter_upwards [he] with sample hω
  change (P[fun sample => u sample - V | m]) sample = (P[u | m]) sample - V at hω
  rw [hω]
  ring

theorem reaction_offset_condExp {k : ℝ} (hk : 0 ≤ k) {u : Ω → ℝ}
    (hu : Integrable u P) (hfu : Integrable (reaction k ∘ u) P) (V : ℝ) :
    ∀ᵐ sample ∂P, reaction k (V + P[fun sample => u sample-V | m] sample) ≤
      P[reaction k ∘ u | m] sample := by
  filter_upwards [offset_condExp hm hu V,reaction_condExp hm hk hu hfu] with sample he hj
  rwa [he]

theorem offset_condExp_bounds {u : Ω → ℝ} (hu : Integrable u P)
    {a b : ℝ} (ha : ∀ᵐ sample ∂P, a ≤ u sample) (hb : ∀ᵐ sample ∂P, u sample ≤ b) (V : ℝ) :
    ∀ᵐ sample ∂P, a ≤ V + P[fun sample => u sample-V | m] sample ∧
      V + P[fun sample => u sample-V | m] sample ≤ b := by
  have h1 := condExp_mono (integrable_const a) hu ha (m := m)
  have h2 := condExp_mono hu (integrable_const b) hb (m := m)
  rw [condExp_const hm] at h1 h2
  filter_upwards [offset_condExp hm hu V,h1,h2] with sample he h1 h2
  rw [he]
  exact ⟨h1,h2⟩

end CoulombBarrier

end

end OAI
