import OAI.Analysis.CircleDomains.Topology.PotentialPhysicalPaths
import OAI.Analysis.CircleDomains.Sobolev.LineLIntegralAbsoluteContinuity

namespace OAI

/-! On each physical chart line with finite density integral, the actual
barrier pullback is absolutely continuous. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem potential_chart_absolutelyContinuousOnInterval
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Y → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    (φ : ℝ → Y) (hφ : Measurable φ) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) (hdom : MapsTo φ (Icc a b) d.physicalDomain)
    (hfinite : (∫⁻t in Icc a b, g (φ t)) < ∞) :
    AbsolutelyContinuousOnInterval (v ∘ φ) a b := by
  let ρ : ℝ → ℝ≥0∞ := fun t => 4 * ((L : ℝ≥0∞) * g (φ t))
  have hfρ : (∫⁻t in uIoc a b, ρ t) < ∞ := by
    apply lt_of_le_of_lt (lintegral_mono_set (show uIoc a b ⊆ Icc a b from by
      rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self))
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinite)
  have hseg (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x < y) :
      ENNReal.ofReal |v (φ y) - v (φ x)| ≤ ∫⁻t in uIoc x y, ρ t := by
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hi := potential_chart_interval_bound d hdisj ν N u g hg m hm hpath v hv
      φ hφ hxy (hL.mono hsub) (fun t ht => hdom (hsub ht))
    rw [uIoc_of_le hxy.le]
    dsimp [ρ]
    rw [lintegral_const_mul' 4 (fun t => (L : ℝ≥0∞) * g (φ t)) (by norm_num),
      lintegral_const_mul' (L : ℝ≥0∞) (fun t => g (φ t)) ENNReal.coe_ne_top]
    have he : (∫⁻t in Ioc x y, g (φ t)) = ∫⁻t in Icc x y, g (φ t) :=
      setLIntegral_congr Ioc_ae_eq_Icc
    rwa [he]
  apply absolutelyContinuousOnInterval_of_lintegral_bound hfρ
  intro x hx y hy
  rw [uIcc_of_le hab] at hx hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm] using hseg x y hx hy hxy
  · subst y
    simp only [dist_self, ENNReal.ofReal_zero]
    exact bot_le
  · simpa only [Function.comp_apply, Real.dist_eq, abs_sub_comm, uIoc_comm y x] using hseg y x hy hx hyx

end CircleDomainRigidity

end OAI
